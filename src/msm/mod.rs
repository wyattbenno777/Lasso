/// Copy of ark_ec::VariableBaseMSM with minor modifications to speed up
/// known small element sized MSMs.
use ark_ff::{prelude::*, PrimeField, BigInteger};
use ark_std::{borrow::Borrow, iterable::Iterable, vec::Vec};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_r1cs_std::{
  alloc::{AllocVar, AllocationMode},
  fields::fp::FpVar,
  fields::nonnative::NonNativeFieldVar,
  prelude::{EqGadget, FieldVar},
};

use ark_ec::{CurveGroup, ScalarMul};
use ark_r1cs_std::boolean::Boolean;

use ark_ec::Group;
use ark_bn254::Fr as Fr;
use ark_bn254::Fq as Fq;
use ark_bn254::G1Affine as G1Affine;
use ark_bn254::G1Projective as G1Projective;
use ark_bn254::G2Affine as G2Affine;
use ark_bn254::G2Projective as G2Projective;
use ark_ff::BigInt;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[cfg(not(feature = "ark-msm"))]
impl<G: CurveGroup> VariableBaseMSM for G {}

pub trait VariableBaseMSM: ScalarMul {
  /// Computes an inner product between the [`PrimeField`] elements in `scalars`
  /// and the corresponding group elements in `bases`.
  ///
  /// If the elements have different length, it will chop the slices to the
  /// shortest length between `scalars.len()` and `bases.len()`.
  ///
  /// Reference: [`VariableBaseMSM::msm`]
  fn msm_unchecked(bases: &[Self::MulBase], scalars: &[Self::ScalarField]) -> Self {
    let bigints = ark_std::cfg_into_iter!(scalars)
      .map(|s| s.into_bigint())
      .collect::<Vec<_>>();
    Self::msm_bigint(bases, &bigints)
  }

  /// Performs multi-scalar multiplication.
  ///
  /// # Warning
  ///
  /// This method checks that `bases` and `scalars` have the same length.
  /// If they are unequal, it returns an error containing
  /// the shortest length over which the MSM can be performed.
  fn msm(bases: &[Self::MulBase], scalars: &[Self::ScalarField]) -> Result<Self, usize> {
    (bases.len() == scalars.len())
      .then(|| Self::msm_unchecked(bases, scalars))
      .ok_or_else(|| bases.len().min(scalars.len()))
  }

  /// Optimized implementation of multi-scalar multiplication.
  fn msm_bigint(
    bases: &[Self::MulBase],
    bigints: &[<Self::ScalarField as PrimeField>::BigInt],
  ) -> Self {
    if Self::NEGATION_IS_CHEAP {
      msm_bigint_wnaf(bases, bigints)
    } else {
      msm_bigint(bases, bigints)
    }
  }

  fn msm_circuit(bases: &[G1Projective], scalars: &[Fr], cs: ConstraintSystemRef<Fr>) -> Result<G1Projective, usize> {
    (bases.len() == scalars.len())
      .then(|| Self::msm_unchecked_circuit(bases, scalars, cs))
      .ok_or_else(|| bases.len().min(scalars.len()))
  }

  fn msm_unchecked_circuit(
    bases: &[G1Projective],
    scalars: &[Fr],
    cs: ConstraintSystemRef<Fr>,
  ) -> G1Projective {
    let bigints = ark_std::cfg_into_iter!(scalars)
      .map(|s| s.into_bigint())
      .collect::<Vec<_>>();
    Self::msm_bigint_circuit(bases, &bigints, cs)
  }

  fn msm_bigint_circuit(
    bases: &[G1Projective],
    bigints: &[<Fr as PrimeField>::BigInt],
    cs: ConstraintSystemRef<Fr>,
  ) -> G1Projective {
    msm_bigint_circuit(bases, bigints, cs)
  }

  /// Streaming multi-scalar multiplication algorithm with hard-coded chunk
  /// size.
  fn msm_chunks<I: ?Sized, J>(bases_stream: &J, scalars_stream: &I) -> Self
  where
    I: Iterable,
    I::Item: Borrow<Self::ScalarField>,
    J: Iterable,
    J::Item: Borrow<Self::MulBase>,
  {
    assert!(scalars_stream.len() <= bases_stream.len());

    // remove offset
    let bases_init = bases_stream.iter();
    let mut scalars = scalars_stream.iter();

    // align the streams
    // TODO: change `skip` to `advance_by` once rust-lang/rust#7774 is fixed.
    // See <https://github.com/rust-lang/rust/issues/77404>
    let mut bases = bases_init.skip(bases_stream.len() - scalars_stream.len());
    let step: usize = 1 << 20;
    let mut result = Self::zero();
    for _ in 0..(scalars_stream.len() + step - 1) / step {
      let bases_step = (&mut bases)
        .take(step)
        .map(|b| *b.borrow())
        .collect::<Vec<_>>();
      let scalars_step = (&mut scalars)
        .take(step)
        .map(|s| s.borrow().into_bigint())
        .collect::<Vec<_>>();
      result += Self::msm_bigint(bases_step.as_slice(), scalars_step.as_slice());
    }
    result
  }
}

// Compute msm using windowed non-adjacent form
fn msm_bigint_wnaf<V: VariableBaseMSM>(
  bases: &[V::MulBase],
  bigints: &[<V::ScalarField as PrimeField>::BigInt],
) -> V {
  let mut max_num_bits = 1usize;
  for bigint in bigints {
    if bigint.num_bits() as usize > max_num_bits {
      max_num_bits = bigint.num_bits() as usize;
    }

    // Hack for early exit
    if max_num_bits > 60 {
      max_num_bits = V::ScalarField::MODULUS_BIT_SIZE as usize;
      break;
    }
  }

  let size = ark_std::cmp::min(bases.len(), bigints.len());
  let scalars = &bigints[..size];
  let bases = &bases[..size];

  let c = if size < 32 {
    3
  } else {
    ln_without_floats(size) + 2
  };

  let num_bits = max_num_bits;
  let digits_count = (num_bits + c - 1) / c;
  let scalar_digits = scalars
    .iter()
    .flat_map(|s| make_digits(s, c, num_bits))
    .collect::<Vec<_>>();
  let zero = V::zero();
  let window_sums: Vec<_> = ark_std::cfg_into_iter!(0..digits_count)
    .map(|i| {
      let mut buckets = vec![zero; 1 << c];
      for (digits, base) in scalar_digits.chunks(digits_count).zip(bases) {
        use ark_std::cmp::Ordering;
        // digits is the digits thing of the first scalar?
        let scalar = digits[i];
        match 0.cmp(&scalar) {
          Ordering::Less => buckets[(scalar - 1) as usize] += base,
          Ordering::Greater => buckets[(-scalar - 1) as usize] -= base,
          Ordering::Equal => (),
        }
      }

      let mut running_sum = V::zero();
      let mut res = V::zero();
      buckets.into_iter().rev().for_each(|b| {
        running_sum += &b;
        res += &running_sum;
      });
      res
    })
    .collect();

  // We store the sum for the lowest window.
  let lowest = *window_sums.first().unwrap();

  // We're traversing windows from high to low.
  lowest
    + window_sums[1..]
      .iter()
      .rev()
      .fold(zero, |mut total, sum_i| {
        total += sum_i;
        for _ in 0..c {
          total.double_in_place();
        }
        total
      })
}

/// Optimized implementation of multi-scalar multiplication.
fn msm_bigint<V: VariableBaseMSM>(
  bases: &[V::MulBase],
  bigints: &[<V::ScalarField as PrimeField>::BigInt],
) -> V {
  let size = ark_std::cmp::min(bases.len(), bigints.len());
  let scalars = &bigints[..size];
  let bases = &bases[..size];
  let scalars_and_bases_iter = scalars.iter().zip(bases).filter(|(s, _)| !s.is_zero());

  let c = if size < 32 {
    3
  } else {
    ln_without_floats(size) + 2
  };

  let mut max_num_bits = 1usize;
  for bigint in bigints {
    if bigint.num_bits() as usize > max_num_bits {
      max_num_bits = bigint.num_bits() as usize;
    }

    // Hack
    if max_num_bits > 60 {
      max_num_bits = V::ScalarField::MODULUS_BIT_SIZE as usize;
      break;
    }
  }

  let num_bits = max_num_bits;
  let one = V::ScalarField::one().into_bigint();

  let zero = V::zero();
  let window_starts = (0..num_bits).step_by(c);

  // Each window is of size `c`.
  // We divide up the bits 0..num_bits into windows of size `c`, and
  // in parallel process each such window.
  let window_sums: Vec<_> = window_starts
    .map(|w_start| {
      let mut res = zero;
      // We don't need the "zero" bucket, so we only have 2^c - 1 buckets.
      let mut buckets = vec![zero; (1 << c) - 1];
      // This clone is cheap, because the iterator contains just a
      // pointer and an index into the original vectors.
      scalars_and_bases_iter.clone().for_each(|(&scalar, base)| {
        if scalar == one {
          // We only process unit scalars once in the first window.
          if w_start == 0 {
            res += base;
          }
        } else {
          let mut scalar = scalar;

          // We right-shift by w_start, thus getting rid of the
          // lower bits.
          scalar.divn(w_start as u32);

          // We mod the remaining bits by 2^{window size}, thus taking `c` bits.
          let scalar = scalar.as_ref()[0] % (1 << c);

          // If the scalar is non-zero, we update the corresponding
          // bucket.
          // (Recall that `buckets` doesn't have a zero bucket.)
          if scalar != 0 {
            buckets[(scalar - 1) as usize] += base;
          }
        }
      });

      // Compute sum_{i in 0..num_buckets} (sum_{j in i..num_buckets} bucket[j])
      // This is computed below for b buckets, using 2b curve additions.
      //
      // We could first normalize `buckets` and then use mixed-addition
      // here, but that's slower for the kinds of groups we care about
      // (Short Weierstrass curves and Twisted Edwards curves).
      // In the case of Short Weierstrass curves,
      // mixed addition saves ~4 field multiplications per addition.
      // However normalization (with the inversion batched) takes ~6
      // field multiplications per element,
      // hence batch normalization is a slowdown.

      // `running_sum` = sum_{j in i..num_buckets} bucket[j],
      // where we iterate backward from i = num_buckets to 0.
      let mut running_sum = V::zero();
      buckets.into_iter().rev().for_each(|b| {
        running_sum += &b;
        res += &running_sum;
      });
      res
    })
    .collect();

  // We store the sum for the lowest window.
  let lowest = *window_sums.first().unwrap();

  // We're traversing windows from high to low.
  lowest
    + window_sums[1..]
      .iter()
      .rev()
      .fold(zero, |mut total, sum_i| {
        total += sum_i;
        for _ in 0..c {
          total.double_in_place();
        }
        total
      })
}

fn log2_circuit(
  cs: ConstraintSystemRef<Fr>,
  x: usize
) -> Result<u32, SynthesisError> {

  let x_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(x as u64)))?;
  let zero_var = FpVar::new_constant(cs.clone(), Fr::zero())?;

  let mut power_of_two = Boolean::new_witness(
    cs.clone(), 
    || Ok(x.is_power_of_two())
  )?;

  if x == 0 {
      x_witness.enforce_equal(&zero_var);
      Ok(0 as u32)
  } else if x.is_power_of_two() {
      power_of_two.enforce_equal(&Boolean::constant(true));
      Ok(1usize.leading_zeros() - x.leading_zeros())
  } else {
      x_witness.enforce_not_equal(&zero_var);
      power_of_two.enforce_not_equal(&Boolean::constant(true));
      Ok(0usize.leading_zeros() - x.leading_zeros())
  }
}

fn ln_without_floats_circuit(
  cs: ConstraintSystemRef<Fr>,
  a: usize,
) -> Result<usize, SynthesisError> {

  let a_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(a as u64)))?;
  let log2_pre = log2_circuit(cs.clone(), a)?;
  let log2_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(log2_pre)))?;

  let sixty_nine = FpVar::new_constant(cs.clone(), Fr::from(69u8))?;
  let one_hundred = FpVar::new_constant(cs.clone(), Fr::from(100u8))?;

  let computation = log2_witness * sixty_nine;
  let numerator = log2_pre * 69; 
  let result = numerator / 100; 
  let result_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(result)))?;
  let numerator_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(numerator)))?;

  // Result * denominator = numerator
  // Enforces numerator / denominator = result
  let computation_div = (result_witness * one_hundred.clone());
  numerator_witness.enforce_equal(&computation_div)?;

  Ok(result as usize)
}

/// Enforce this as a circuit.
fn msm_bigint_circuit(
  bases: &[G1Projective],
  bigints: &[<Fr as PrimeField>::BigInt],
  cs: ConstraintSystemRef<Fr>,
) -> G1Projective {

  let size = ark_std::cmp::min(bases.len(), bigints.len());
  let size_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(size as u64))).unwrap();

  // These values are witnessed further down before they are used.
  let scalars = &bigints[..size];
  let bases = &bases[..size];
  let scalars_and_bases_iter = scalars.iter().zip(bases).filter(|(s, _)| !s.is_zero());
  
  let thirty_two = FpVar::new_constant(cs.clone(), Fr::from(32u8)).unwrap();
  
  let zero = G1Projective::zero();
  let zero_witness = FpVar::new_constant(cs.clone(), Fr::zero()).unwrap();

  // 32 - size  if negative the result is zero due to ff.
  let gt_constr = thirty_two.clone() - size_witness.clone();

  let c = if size < 32 {
    gt_constr.enforce_equal(&zero_witness);
    3
  } else {
    gt_constr.enforce_not_equal(&zero_witness);
    ln_without_floats_circuit(cs.clone(), size).unwrap() + 2
  };

  let _c_witness = FpVar::new_constant(cs.clone(), Fr::from(c as u64)).unwrap();

  let mut max_num_bits = 1usize;
  let mut max_num_bits_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(max_num_bits as u64))).unwrap();

  let mut bigint_witnesses = Vec::new();
  let sixty = FpVar::new_constant(cs.clone(), Fr::from(60u8)).unwrap();

  for (i, bigint) in bigints.iter().enumerate()  {

    bigint_witnesses.push(FpVar::new_witness(cs.clone(), || Ok(Fr::from(bigints[i]))).unwrap());
    FpVar::new_witness(cs.clone(), || Ok(Fr::from(max_num_bits as u64))).unwrap();

    // num_bits_bigint - max_num_bits; if positive the result is not zero due to ff.
    let num_bits_bigint = bigint.num_bits() as usize;
    let num_bits_bigint_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(num_bits_bigint as u64))).unwrap();

    let gt_max_num_bits = num_bits_bigint_witness.clone() - max_num_bits_witness.clone();
    let gt_sixty = num_bits_bigint_witness.clone() - sixty.clone();

    if num_bits_bigint > max_num_bits {
      gt_max_num_bits.enforce_not_equal(&zero_witness);
      max_num_bits = num_bits_bigint;
    }

    // Hack
    if max_num_bits > 60 {
      gt_sixty.enforce_not_equal(&zero_witness);
      max_num_bits = Fr::MODULUS_BIT_SIZE as usize;
      max_num_bits_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(max_num_bits as u64))).unwrap();
      break;
    }
  }

  let num_bits = max_num_bits;
  let num_bits_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(num_bits as u64))).unwrap();

  let one = Fr::one().into_bigint();
  let one_witness = FpVar::new_constant(cs.clone(), Fr::one()).unwrap();

  let window_starts = (0..num_bits).step_by(c);
  let window_sums: Vec<_> = window_starts
    .map(|w_start| {
      let mut res = zero;
      let mut res_x = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(res.x)).unwrap();
      let mut res_y = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(res.y)).unwrap();
      let mut res_z = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(res.z)).unwrap();
      //ENDED_HERE
      let w_start_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(w_start as u64))).unwrap();
      // We don't need the "zero" bucket, so we only have 2^c - 1 buckets.
      let mut buckets = vec![zero; (1 << c) - 1];
      let mut buckets_witnesses = vec![(res_x.clone(), res_y.clone(), res_z.clone()); (1 << c) - 1];
      // This clone is cheap, because the iterator contains just a
      // pointer and an index into the original vectors.
      scalars_and_bases_iter.clone().for_each(|(&scalar, base)| {
        let mut scalar_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(scalar))).unwrap();
        
        let base_x_witness = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(base.x)).unwrap();
        let base_y_witness = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(base.y)).unwrap();
        let base_z_witness = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(base.z)).unwrap();

        if scalar == one {
          scalar_witness.enforce_equal(&one_witness).unwrap();
          // We only process unit scalars once in the first window.
          if w_start == 0 {
            res += base;
            res_x += base_x_witness;
            res_y += base_y_witness;
            res_z += base_z_witness;
          }
        } else {
          scalar_witness.enforce_not_equal(&one_witness).unwrap();
          let mut scalar = scalar;
          scalar_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(scalar))).unwrap();

          // We right-shift by w_start, thus getting rid of the lower bits.
          scalar = divn_circuit(scalar, w_start as u32, cs.clone());

          // We mod the remaining bits by 2^{window size}, thus taking `c` bits.
          //TODO
          let scalar = scalar.as_ref()[0] % (1 << c);
          scalar_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(scalar))).unwrap();

          // If the scalar is non-zero, we update the corresponding
          // bucket.
          // (Recall that `buckets` doesn't have a zero bucket.)
          if scalar != 0 {
            scalar_witness.enforce_not_equal(&zero_witness).unwrap();
            buckets[(scalar - 1) as usize] += base;
            buckets_witnesses[(scalar - 1) as usize].0 += base_x_witness;
            buckets_witnesses[(scalar - 1) as usize].1 += base_y_witness;
            buckets_witnesses[(scalar - 1) as usize].2 += base_z_witness;
          }
        }
      });

      let mut running_sum_witness = zero_witness.clone();
      let mut running_sum = G1Projective::zero();
      buckets.into_iter().rev().for_each(|b| {
        running_sum += &b;
        //running_sum_witness += &b_witness
        //running_sum_witness.enforce_equal(&(running_sum.clone() + &b)).unwrap();
        res += &running_sum;
      });
      res
    })
    .collect();

  // We store the sum for the lowest window.
  let lowest = *window_sums.first().unwrap();

  // We're traversing windows from high to low.
  lowest
    + window_sums[1..]
      .iter()
      .rev()
      .fold(zero, |mut total, sum_i| {
        total += sum_i;
        for _ in 0..c {
          total.double_in_place();
        }
        total
      })
}

fn divn_circuit(
  mut scalar: <Fr as PrimeField>::BigInt,
  mut n: u32,
  cs: ConstraintSystemRef<Fr>
) -> <Fr as PrimeField>::BigInt {

  let num_limbs = (Fr::MODULUS_BIT_SIZE as usize + 63) / 64;
  let num_limbs_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(num_limbs as u32))).unwrap();

  let mut n_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(n))).unwrap();
  let sixty_four = FpVar::new_constant(cs.clone(), Fr::from(64u8)).unwrap();
  let zero_witness = FpVar::new_constant(cs.clone(), Fr::zero()).unwrap();
  
  // n - (64 * limbs) if negative the result is zero due to ff.
  let compare_constr = n_witness.clone() - (sixty_four.clone() * num_limbs_witness.clone());
  let compare_constr_2 = sixty_four.clone() * num_limbs_witness.clone();
  if n > (64 * num_limbs) as u32 {
    compare_constr.enforce_not_equal(&zero_witness);
    return <Fr as PrimeField>::BigInt::from(0u64);
  } else if n == (64 * num_limbs) as u32 {
    n_witness.enforce_equal(&compare_constr_2);
    return <Fr as PrimeField>::BigInt::from(0u64);
  }

  let compare_constr2 = sixty_four.clone() - n_witness.clone();

  while n >= 64 {

    if n > 64 {
      compare_constr2.enforce_not_equal(&zero_witness);
    } else {
      n_witness.enforce_equal(&sixty_four);
    }

    let mut t = 0;
    let mut t_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(t as u64))).unwrap();
    let mut scalar_swap_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(scalar.0[num_limbs - 0 - 1]))).unwrap();
    for i in 0..num_limbs {
        let mut i_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(i as u64))).unwrap();

        core::mem::swap(&mut t, &mut scalar.0[num_limbs - i - 1]);

        //TODO: this may need to be a bit decomp. Or an input into the circuit.
        t_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(scalar.0[num_limbs - i - 1]))).unwrap();
        scalar_swap_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(t))).unwrap()
    }
    n_witness = n_witness.clone() - sixty_four.clone();
    n -= 64;
  }

  if n > 0 {
    n_witness.enforce_not_equal(&zero_witness);
    let mut t = 0;
    let mut t_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(t as u64))).unwrap();

    #[allow(unused)]
    for i in 0..num_limbs {
        let a = &mut scalar.0[num_limbs - i - 1];
        let mut a_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(*a as u64))).unwrap();

        let two_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(2 as u32))).unwrap();
        let mut cur_power = FpVar::new_constant(cs.clone(), Fr::zero()).unwrap();
        
        for _ in 0..(64 - n) {
          cur_power = cur_power.clone() * two_witness.clone();
        }

        let t2 = *a << (64 - n);
        let t2_witness = a_witness.clone() * cur_power.clone();
        let t2_end_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(t2 as u64))).unwrap();
        t2_witness.enforce_equal(&t2_end_witness);

        let mut cur_power_2 = a_witness.clone();
        
        *a >>= n;
        for _ in 0..n {
          cur_power_2 = cur_power_2.clone() + cur_power_2.clone();
        }

        *a |= t;
        let temp = a_witness.clone() + t_witness.clone();
        let mut out = a_witness.clone() * temp.clone();
        out = out.clone() + t_witness.clone();

        let a_end_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(*a as u64))).unwrap();
        out.enforce_equal(&a_end_witness);

        t = t2;
        t_witness = t2_witness;
    }
  }
  scalar
}

// From: https://github.com/arkworks-rs/gemini/blob/main/src/kzg/msm/variable_base.rs#L20
fn make_digits(a: &impl BigInteger, w: usize, num_bits: usize) -> Vec<i64> {
  let scalar = a.as_ref();
  let radix: u64 = 1 << w;
  let window_mask: u64 = radix - 1;

  let mut carry = 0u64;
  let num_bits = if num_bits == 0 {
    a.num_bits() as usize
  } else {
    num_bits
  };
  let digits_count = (num_bits + w - 1) / w;
  let mut digits = vec![0i64; digits_count];
  for (i, digit) in digits.iter_mut().enumerate() {
    // Construct a buffer of bits of the scalar, starting at `bit_offset`.
    let bit_offset = i * w;
    let u64_idx = bit_offset / 64;
    let bit_idx = bit_offset % 64;
    // Read the bits from the scalar
    let bit_buf = if bit_idx < 64 - w || u64_idx == scalar.len() - 1 {
      // This window's bits are contained in a single u64,
      // or it's the last u64 anyway.
      scalar[u64_idx] >> bit_idx
    } else {
      // Combine the current u64's bits with the bits from the next u64
      (scalar[u64_idx] >> bit_idx) | (scalar[1 + u64_idx] << (64 - bit_idx))
    };

    // Read the actual coefficient value from the window
    let coef = carry + (bit_buf & window_mask); // coef = [0, 2^r)

    // Recenter coefficients from [0,2^w) to [-2^w/2, 2^w/2)
    carry = (coef + radix / 2) >> w;
    *digit = (coef as i64) - (carry << w) as i64;
  }

  digits[digits_count - 1] += (carry << w) as i64;

  digits
}

/// The result of this function is only approximately `ln(a)`
/// [`Explanation of usage`]
///
/// [`Explanation of usage`]: https://github.com/scipr-lab/zexe/issues/79#issue-556220473
fn ln_without_floats(a: usize) -> usize {
  // log2(a) * ln(2)
  (ark_std::log2(a) * 69 / 100) as usize
}