//! This module is an adaptation of code from Testudo and Lasso main branch.
use ark_ec::pairing::Pairing;
use std::borrow::Borrow;

use crate::{
  utils::math::Math,
  poly::unipoly::{CompressedUniPoly, UniPoly},
  utils::transcript::{AppendToTranscript, ProofTranscript},
  utils::errors::ProofVerifyError,
};
use ark_ff::{prelude::*, PrimeField};
use ark_ff::BigInt;

use ark_crypto_primitives::sponge::{
  constraints::CryptographicSpongeVar,
  poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
};
use ark_poly_commit::multilinear_pc::data_structures::Commitment;
use ark_r1cs_std::{
  alloc::{AllocVar, AllocationMode},
  fields::fp::FpVar,
  prelude::{EqGadget, FieldVar},
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};

use ark_serialize::*;
use ark_ec::CurveGroup;
use ark_r1cs_std::R1CSVar;
use ark_std::One;
use ark_ff::Field;

#[cfg(not(feature = "ark-msm"))]
use super::super::msm::VariableBaseMSM;

/* There are three main phases of Lasso verification
 Lasso's goal is to prove an opening of the Sparse Matrix Polynomial.
 It does it with:

 1. A primary sum-check.
    M (Indices) . T (Table) = A (lookup results) 
    Check the correctness of A using sum-check.

    P: But M is too big.
    A: turn M into EQ(j,r) . T[NZ_(j)] = A(r)
     EQ(x, e) = (1 if x = e; 0 otherwise.) eq is an MLE.

    P: T might still be too big.
    A: Decompoise T into subtables.
    EQ(j,r) . g(T[NZ_i(j)]...) = a(r)

    NZ_i[J] are turned into MLE DIM_i(j)
    Which is then turned into polynomial
    E_i(j)

 2. (Combined eval proof for E_i(r_z)). 
    E_i = values read from subtable.
    r_z chosen by veritfier over sum-check
    via (DotProductProof).

    dot(x, y) = Σ xi * yi
    Prover convinces Verifier that it knows two vectors x and y,
    for public value v.
    r is where the poly is evaluated.
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();
    L and R are x and y in the dot product.

 3. Memory check that uses an adapted GKR protocol.
    P: How do we know that E_i encodes the value reads from Ti.
    A: Use memory checking on E_i/T_i/DIM_i

    Checks E_i, counter_polynomials (read, final), dim_i (chuncked lookup indices)
    Commits to values that make up most of the layers. 
    Does tha13 for values near inputs (most of the gates).
*/

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct SumcheckInstanceProof<F: PrimeField> {
  compressed_polys: Vec<CompressedUniPoly<F>>,
}

/// Univariate polynomial in constraint system
#[derive(Clone)]
pub struct UniPolyVar<F: PrimeField> {
  pub coeffs: Vec<FpVar<F>>,
}

impl<F: PrimeField> AllocVar<UniPoly<F>, F> for UniPolyVar<F> {
  fn new_variable<T: Borrow<UniPoly<F>>>(
    cs: impl Into<Namespace<F>>,
    f: impl FnOnce() -> Result<T, SynthesisError>,
    mode: AllocationMode,
  ) -> Result<Self, SynthesisError> {
    f().and_then(|c| {
      let cs = cs.into();
      let cp: &UniPoly<F> = c.borrow();
      let mut coeffs_var = Vec::new();
      for coeff in cp.coeffs.iter() {
        let coeff_var = FpVar::<F>::new_variable(cs.clone(), || Ok(coeff), mode)?;
        coeffs_var.push(coeff_var);
      }
      Ok(Self { coeffs: coeffs_var })
    })
  }
}

impl<F: PrimeField> UniPolyVar<F> {
    pub fn eval_at_zero(&self) -> FpVar<F> {
      self.coeffs[0].clone()
    }
  
    pub fn eval_at_one(&self) -> FpVar<F> {
      let mut res = self.coeffs[0].clone();
      for i in 1..self.coeffs.len() {
        res = &res + &self.coeffs[i];
      }
      res
    }
  
    pub fn evaluate(&self, r: &FpVar<F>) -> FpVar<F> {
      let mut eval = self.coeffs[0].clone();
      let mut power = r.clone();
  
      for i in 1..self.coeffs.len() {
        eval += &power * &self.coeffs[i];
        power *= r;
      }
      eval
    }
}

impl<G: CurveGroup> AppendToTranscript<G> for UniPolyVar<G::ScalarField> {

    fn append_to_transcript<T: ProofTranscript<G>>(&self, label: &'static [u8], transcript: &mut T) {
      
      transcript.append_message(label, b"UniPolyVar_begin");
      
      for i in 0..self.coeffs.len() {
      
        let value = self.coeffs[i].value().unwrap();  
        transcript.append_scalar(b"coeff", &value);
        
      }
      
      transcript.append_message(label, b"UniPolyVar_end");
    }
  
  }


impl<F: PrimeField> SumcheckInstanceProof<F> {
  /// Verify this sumcheck proof.
  /// Note: Verification does not execute the final check of sumcheck protocol: g_v(r_v) = oracle_g(r),
  /// as the oracle is not passed in. Expected that the caller will implement.
  ///
  /// Params
  /// - `claim`: Claimed evaluation
  /// - `num_rounds`: Number of rounds of sumcheck, or number of variables to bind
  /// - `degree_bound`: Maximum allowed degree of the combined univariate polynomial
  /// - `transcript`: Fiat-shamir transcript
  ///
  /// Returns (e, r)
  /// - `e`: Claimed evaluation at random point
  /// - `r`: Evaluation point
  pub fn verify_sumcheck<G, T: ProofTranscript<G>>(
    &self,
    cs: ConstraintSystemRef<F>,
    claim: F,
    num_rounds: usize,
    degree_bound: usize,
    transcript: &mut T,
  ) -> Result<(F, Vec<F>), SynthesisError>
  where
    G: CurveGroup<ScalarField = F>,
  {
    let mut e = claim;
    let mut r: Vec<F> = Vec::new();

    // verify that there is a univariate polynomial for each round
    assert_eq!(self.compressed_polys.len(), num_rounds);
    for i in 0..self.compressed_polys.len() {
        let poly = self.compressed_polys[i].decompress(&e);

        let mut fpv_poly = UniPolyVar::<F>::new_variable(cs.clone(), || Ok(poly.clone()), AllocationMode::Witness)?;

        // verify degree bound
        assert_eq!(poly.degree(), degree_bound);

        // check if G_k(0) + G_k(1) = e
        assert_eq!(poly.eval_at_zero() + poly.eval_at_one(), e);
        let res = fpv_poly.eval_at_one() + fpv_poly.eval_at_zero();

        let d_e = FpVar::<F>::new_input(cs.clone(), || Ok(e))?;
        res.enforce_equal(&d_e)?;

        // append the prover's message to the transcript
        <UniPolyVar<F> as AppendToTranscript<G>>::append_to_transcript(&fpv_poly, b"fpv_poly", transcript);

        //derive the verifier's challenge for the next round
        let r_i = transcript.challenge_scalar(b"challenge_nextround");

        r.push(r_i);

        // evaluate the claimed degree-ell polynomial at r_i
        e = poly.evaluate(&r_i);
    }

    Ok((e, r))
  }

}

// Used for dot product proof in PCS.
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BulletReductionProof<G: CurveGroup> {
  L_vec: Vec<G>,
  R_vec: Vec<G>,
}

impl<G: CurveGroup> BulletReductionProof<G> {

    pub fn verification_scalars<T: ProofTranscript<G>>(
        &self,
        cs: ConstraintSystemRef<G::ScalarField>,
        transcript: &mut T,
        n: usize,
      ) -> Result<
        (
        Vec<G::ScalarField>,
        Vec<G::ScalarField>,
        Vec<G::ScalarField>,
        ), SynthesisError>
    {
        let lg_n = self.L_vec.len();
        // 4 billion multiplications should be enough for anyone
        // and this check prevents overflow in 1<<lg_n below.
        assert!(lg_n >= 32, "lg_n must be at least 32, got {lg_n}");
        assert_eq!((1 << lg_n), n);


        // 1. Recompute x_k,...,x_1 based on the proof transcript
        let mut challenges_witness = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.append_point( b"L", L);
            transcript.append_point( b"R", R);
            let c = transcript.challenge_scalar(b"u");

            let c_wit = FpVar::new_witness(cs.clone(), || Ok(c))?;
            challenges_witness.push(c_wit);
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1
        let mut challenges_inv = challenges_witness
        .iter()
        .map(|x| x.inverse().unwrap())
        .collect::<Vec<_>>();
        let mut all_inv = FpVar::<G::ScalarField>::new_witness(cs.clone(), || Ok(G::ScalarField::one()))?;
        for c in challenges_inv.iter() {
          let new_all_inv = &all_inv * c;
          new_all_inv.enforce_equal(&all_inv)?;
          all_inv = new_all_inv;  
        }

        // 3. Compute u_i^2 and (1/u_i)^2
        for i in 0..lg_n {

            let square_result = challenges_witness[i].square();
            let square_result_inv = challenges_inv[i].square();

            if let Ok(square) = square_result {
              challenges_witness[i] = square; 
            } else {
              assert!(false, "issue with square");
            }

            if let Ok(square) = square_result_inv {
              challenges_inv[i] = square; 
            } else {
              assert!(false, "issue with square");
            }

        }
        
        let challenges_sq = challenges_witness.clone();
        let challenges_inv_sq = challenges_inv.clone();

        // 4. Compute s values inductively.
        let mut s = vec![all_inv];
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [u_k,...,u_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_lg_i_sq = &challenges_sq[(lg_n - 1) - lg_i];
            let s_i_k = s[i-k].clone();
            let result = s_i_k * u_lg_i_sq;
            s.push(result.clone());
            
            let _s_wit = FpVar::new_witness(cs.clone(), || {              
              Ok(result.value().unwrap())
            })?;
        }

        let challenges_sq_fin: Vec<G::ScalarField> = challenges_witness
            .iter()
            .map(|v| v.value().unwrap()) 
            .collect();

        let challenges_inv_sq_fin: Vec<G::ScalarField> = challenges_inv
            .iter()
            .map(|v| v.value().unwrap())
            .collect();

        let s_fin: Vec<G::ScalarField> = s
            .iter()
            .map(|v| v.value().unwrap())
            .collect();

        Ok((challenges_sq_fin, challenges_inv_sq_fin, s_fin))
    }

  /// This method is for testing that proof generation work,
  /// but for efficiency the actual protocols would use `verification_scalars`
  /// method to combine inner product verification with other checks
  /// in a single multiscalar multiplication.
  pub fn verify<T: ProofTranscript<G>>(
    &self,
    cs: ConstraintSystemRef<G::ScalarField>,
    transcript: &mut T,
    n: usize,
    a: &[G::ScalarField],
    Gamma: &G,
    G: &[G],
  ) -> Result<(G, G, G::ScalarField), SynthesisError> {
    let (u_sq, u_inv_sq, s) = self.verification_scalars(cs.clone(), transcript, n)?;

    let group_element = G::normalize_batch(G);

    let G_hat = VariableBaseMSM::msm(group_element.as_ref(), s.as_ref()).unwrap();

    let a_hat = inner_product(a, &s);
    let a_hat_witness = FpVar::new_witness(cs.clone(), || Ok(a_hat))?;
    enforce_inner_product(cs, a, &s, &a_hat_witness);

    let bases = G::normalize_batch(
      [self.L_vec.as_slice(), self.R_vec.as_slice(), &[*Gamma]]
        .concat()
        .as_ref(),
    );
    let scalars = u_sq
      .into_iter()
      .chain(u_inv_sq.into_iter())
      .chain([G::ScalarField::one()])
      .collect::<Vec<_>>();

    let Gamma_hat = VariableBaseMSM::msm(bases.as_ref(), scalars.as_ref()).unwrap();

    Ok((G_hat, Gamma_hat, a_hat))
  }

}

pub fn inner_product<F: PrimeField>(a: &[F], b: &[F]) -> F {
  assert!(
    a.len() == b.len(),
    "inner_product(a,b): lengths of vectors do not match"
  );
  let mut out = F::zero();
  for i in 0..a.len() {
    out += a[i] * b[i];
  }
  out
}

fn enforce_inner_product<F: PrimeField>(
  cs: ConstraintSystemRef<F>, 
  a: &[F], 
  b: &[F],
  result: &FpVar<F>
) -> Result<(), SynthesisError> {

  assert_eq!(a.len(), b.len(), "Vectors must have equal length");

  let mut acc = FpVar::new_witness(cs.clone(), || Ok(F::zero()))?;
  for i in 0..a.len() {
      let a_var = FpVar::new_input(cs.clone(), || Ok(a[i]))?;
      let b_var = FpVar::new_input(cs.clone(), || Ok(b[i]))?;

      let mul = a_var * b_var;
      acc += mul; 
  }

  result.enforce_equal(&acc)?;

  Ok(())
}

fn enforce_variable_msm<G: CurveGroup>(
  cs: ConstraintSystemRef<G::ScalarField>,

  bases: &[FpVar<G::ScalarField>],  
  scalars: &[FpVar<G::ScalarField>],

  result: &FpVar<G::ScalarField>
) -> Result<(), SynthesisError> {

  let bigints = ark_std::cfg_into_iter!(scalars)
  .map(|s| s.value().unwrap().into_bigint())
  .collect::<Vec<_>>();

  let size = ark_std::cmp::min(bases.len(), bigints.len());
  //let scalars = &bigints[..size];
  //let bases = &bases[..size];
  let one = FpVar::<G::ScalarField>::new_input(cs.clone(), || Ok(G::ScalarField::one()))?;
  let zero = FpVar::<G::ScalarField>::new_input(cs.clone(), || Ok(G::ScalarField::zero()))?;
  let scalars_and_bases_iter = scalars.iter().zip(bases).filter(|(s, _)| (s.value().unwrap() != zero.value().unwrap()));

  let c = if size < 32 {
    3
  } else {
    ln_without_floats(size) + 2
  };

  let mut max_num_bits = 1usize;
  for bigint in &bigints {
    if bigint.num_bits() as usize > max_num_bits {
      max_num_bits = bigint.num_bits() as usize;
    }

    // Hack for early exit
    if max_num_bits > 60 {
      max_num_bits = G::ScalarField::MODULUS_BIT_SIZE as usize;
      break;
    }
  }
    
  let num_bits = max_num_bits;

  let window_starts = (0..num_bits).step_by(c);

  /*let window_sums: Vec<_> = window_starts
    .map(|w_start| {
      let mut res = zero;
      let mut buckets = vec![zero; (1 << c) - 1];
      scalars_and_bases_iter.clone().for_each(|(&scalar, base)| {
        if scalar == one {
          if w_start == 0 {
            res += base;
          }
        } else {
          let mut scalar = scalar;

          scalar.divn(w_start as u32);

          let scalar = scalar.as_ref()[0] % (1 << c);

          if scalar != 0 {
            buckets[(scalar - 1) as usize] += base;
          }
        }
      });

      let mut running_sum = V::zero();
      buckets.into_iter().rev().for_each(|b| {
        running_sum += &b;
        res += &running_sum;
      });
      res
    })
    .collect();*/

  /*// Combine window sums with constraints
  let lowest = window_sums[0].clone();
  let mut result_var = lowest;
  let mut cur = zero;

  for i in 1..window_sums.len() {
    cur = window_sums[i].clone();
    for _ in 0..c {
      let doubled = cur.double()? as FpVar<G::ScalarField>;  
      doubled.enforce_equal(&cur)?;
      cur = doubled;
    }

    let new_result = result_var.clone() + cur;
    new_result.enforce_equal(&result_var)?;
    result_var = new_result;
  }

  // Enforce final result
  result.enforce_equal(&result_var)?;*/

  Ok(());
}

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

fn ln_without_floats(a: usize) -> usize {
  // log2(a) * ln(2)
  (ark_std::log2(a) * 69 / 100) as usize
}


/// Circuit gadget that implements the sumcheck verifier
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
struct PrimarySumcheck<G: CurveGroup, const ALPHA: usize> {
  proof: SumcheckInstanceProof<G::ScalarField>,
  claimed_evaluation: G::ScalarField,
  eval_derefs: [G::ScalarField; ALPHA],
  //proof_derefs: CombinedTableEvalProof<G, ALPHA>,
}

