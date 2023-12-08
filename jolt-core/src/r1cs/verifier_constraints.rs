//! This module is an adaptation of code from Testudo and Lasso main branch.
//use ark_ec::pairing::Pairing;
use std::borrow::Borrow;

use crate::{
  poly::unipoly::{ UniPoly},
  utils::transcript::{AppendToTranscript, ProofTranscript},
};
use ark_ff::{prelude::*, PrimeField};

use ark_r1cs_std::{
  alloc::{AllocVar, AllocationMode},
  fields::nonnative::NonNativeFieldVar,
  fields::fp::{FpVar, AllocatedFp},
  prelude::{EqGadget, FieldVar},
  prelude::*,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_serialize::*;
use ark_ec::CurveGroup;
use ark_r1cs_std::R1CSVar;
use ark_std::One;
use ark_ec::AffineRepr;

use ark_bn254::Fr as Fr;
use ark_bn254::Fq as Fq;
use ark_bn254::G1Projective as G1Projective;

use std::ops::MulAssign;
use ark_r1cs_std::ToConstraintFieldGadget;

use crate::poly::commitments::MultiCommitGens;

#[cfg(not(feature = "ark-msm"))]
use super::super::msm::VariableBaseMSM;
use super::gadgets;
use ark_r1cs_std::groups::CurveVar;

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

#[derive(Debug)]
pub struct SumcheckInstanceProof {
  compressed_polys: Vec<CompressedUniPolyVar>,
}

/// Univariate polynomial in constraint system
#[derive(Clone)]
pub struct UniPolyVar {
  pub coeffs: Vec<FpVar<Fr>>,
}

#[allow(unused)]
impl AllocVar<UniPoly<Fr>, Fr> for UniPolyVar {
  fn new_variable<T: Borrow<UniPoly<Fr>>>(
    cs: impl Into<Namespace<Fr>>,
    f: impl FnOnce() -> Result<T, SynthesisError>,
    mode: AllocationMode,
  ) -> Result<Self, SynthesisError> {
    f().and_then(|c| {
      let cs = cs.into();
      let cp: &UniPoly<Fr> = c.borrow();
      let mut coeffs_var = Vec::new();
      for coeff in cp.coeffs.iter() {
        let coeff_var = FpVar::<Fr>::new_variable(cs.clone(), || Ok(coeff), mode)?;
        coeffs_var.push(coeff_var);
      }
      Ok(Self { coeffs: coeffs_var })
    })
  }
}

#[allow(unused)]
impl UniPolyVar {

    pub fn degree(&self) -> usize {
        self.coeffs.len() - 1
    }

    pub fn eval_at_zero(&self) -> FpVar<Fr> {
      self.coeffs[0].clone()
    }
  
    pub fn eval_at_one(&self) -> FpVar<Fr> {
      let mut res = self.coeffs[0].clone();
      for i in 1..self.coeffs.len() {
        res = &res + &self.coeffs[i];
      }
      res
    }
  
    pub fn evaluate(&self, r: &FpVar<Fr>) -> FpVar<Fr> {
      let mut eval = self.coeffs[0].clone();
      let mut power = r.clone();
  
      for i in 1..self.coeffs.len() {
        eval += &power * &self.coeffs[i];
        power *= r;
      }
      eval
    }

    fn append_to_transcript<T: ProofTranscript<G1Projective>>(&self, label: &'static [u8], transcript: &mut T) {
      transcript.append_message(label, b"UniPolyVar_begin");
      
      for i in 0..self.coeffs.len() {
        let value = self.coeffs[i].value().unwrap();
        transcript.append_scalar(b"coeff", &value);
      }
      
      transcript.append_message(label, b"UniPolyVar_end");
    }
}

// ax^2 + bx + c stored as vec![c,a]
// ax^3 + bx^2 + cx + d stored as vec![d,b,a]
#[derive(Debug, Clone)]
pub struct CompressedUniPolyVar {
    coeffs_except_linear_term: Vec<FpVar<Fr>>,
}

#[allow(unused)]
impl CompressedUniPolyVar {
  // we require eval(0) + eval(1) = hint, so we can solve for the linear term as:
  // linear_term = hint - 2 * constant_term - deg2 term - deg3 term
  pub fn decompress(&self, hint: &FpVar<Fr>) -> UniPolyVar {
      let mut linear_term =
          hint.clone() - self.coeffs_except_linear_term[0].clone() - self.coeffs_except_linear_term[0].clone();
      for i in 1..self.coeffs_except_linear_term.len() {
          linear_term -= self.coeffs_except_linear_term[i].clone();
      }

      let mut coeffs = vec![self.coeffs_except_linear_term[0].clone(), linear_term];
      coeffs.extend(self.coeffs_except_linear_term[1..].to_vec());
      assert_eq!(self.coeffs_except_linear_term.len() + 1, coeffs.len());
      
      UniPolyVar { coeffs }
  }
}

#[allow(unused)]
impl SumcheckInstanceProof {
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
  pub fn verify_sumcheck<G, T: ProofTranscript<G1Projective>>(
    &self,
    cs: ConstraintSystemRef<Fr>,
    claim: Fr,
    num_rounds: usize,
    degree_bound: usize,
    transcript: &mut T,
  ) -> Result<(Fr, Vec<Fr>), SynthesisError>
  where
    G: CurveGroup<ScalarField = Fr>,
  {
      let mut e_var = claim;
      let mut e_wit = FpVar::<Fr>::new_input(cs.clone(), || Ok(e_var))?;
      let mut r_vars: Vec<FpVar<Fr>> = Vec::new();

      // verify that there is a univariate polynomial for each round
      assert_eq!(self.compressed_polys.len(), num_rounds);
      for i in 0..self.compressed_polys.len() {
          let poly = self.compressed_polys[i].decompress(&e_wit);

          // verify degree bound
          assert_eq!(poly.degree(), degree_bound);

          // check if G_k(0) + G_k(1) = e
          assert_eq!(
            poly.eval_at_zero().value().unwrap() + poly.eval_at_one().value().unwrap(),
            e_wit.value().unwrap()
          );
          let res = poly.eval_at_one() + poly.eval_at_zero();

          res.enforce_equal(&e_wit)?;

          // append the prover's message to the transcript
          poly.append_to_transcript(b"poly", transcript);

          //derive the verifier's challenge for the next round
          let r_i = transcript.challenge_scalar(b"challenge_nextround");
          let r_i_wit = FpVar::<Fr>::new_input(cs.clone(), || Ok(r_i))?;

          r_vars.push(r_i_wit.clone());

          // evaluate the claimed degree-ell polynomial at r_i
          e_wit = poly.evaluate(&r_i_wit);
      }

      let r_fin: Vec<Fr> = r_vars
      .iter()
      .map(|v| v.value().unwrap())
      .collect();

      Ok((e_wit.value().unwrap(), r_fin))
  }

}


// Used for dot product proof in PCS.
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BulletReductionProof {
  L_vec: Vec<G1Projective>,
  R_vec: Vec<G1Projective>,
}


#[allow(unused)]
impl BulletReductionProof {

    pub fn verification_scalars<T: ProofTranscript<G1Projective>>(
        &self,
        cs: ConstraintSystemRef<Fr>,
        transcript: &mut T,
        n: usize,
      ) -> Result<
        (
        Vec<Fr>,
        Vec<Fr>,
        Vec<Fr>,
        ), SynthesisError>
    {
      let lg_n = self.L_vec.len();
      let lg_n_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(lg_n as u64))).unwrap();
      // 4 billion multiplications should be enough for anyone
      // and this check prevents overflow in 1<<lg_n below.
      //assert!(lg_n >= 32, "lg_n must be at least 32, got {lg_n}");
      assert_eq!((1 << lg_n), n);

      let one_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::one())).unwrap();
      //let n_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(n as u64))).unwrap();
      //let left_shift_one_witness = gadgets::left_shift(one_witness.clone(), lg_n as u64, cs.clone());

      //let _ = left_shift_one_witness.enforce_equal(&n_witness).unwrap();*/


      // 1. Recompute x_k,...,x_1 based on the proof transcript
      let mut challenges_witness = Vec::with_capacity(lg_n);
      for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
          transcript.append_point( b"L", L);
          transcript.append_point( b"R", R);
          let c = transcript.challenge_scalar(b"u");

          let c_witness = FpVar::new_witness(cs.clone(), || Ok(c))?;
          challenges_witness.push(c_witness);
      }

      // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1
      let mut challenges_inv = challenges_witness
      .iter()
      .map(|x| x.inverse().unwrap())
      .collect::<Vec<_>>();
      let mut all_inv = FpVar::<Fr>::new_witness(cs.clone(), || Ok(Fr::one()))?;
      challenges_inv.iter().for_each(|c| all_inv *= c);

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
          let _lg_i_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(lg_i as u64))).unwrap();

          let k = 1 << lg_i;
          let _k_witness = gadgets::left_shift(one_witness.clone(), lg_i as u64, cs.clone());
          // The challenges are stored in "creation order" as [u_k,...,u_1],
          // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
          let u_lg_i_sq = &challenges_sq[(lg_n - 1) - lg_i];
          let s_i_k = s[i-k].clone();
          let result = s_i_k * u_lg_i_sq;
          s.push(result.clone());
          //The above are FPVar calcs.
      }

      let challenges_sq_fin: Vec<Fr> = challenges_witness
          .iter()
          .map(|v| v.value().unwrap()) 
          .collect();

      let challenges_inv_sq_fin: Vec<Fr> = challenges_inv
          .iter()
          .map(|v| v.value().unwrap())
          .collect();

      let s_fin: Vec<Fr> = s
          .iter()
          .map(|v| v.value().unwrap())
          .collect();

      Ok((challenges_sq_fin, challenges_inv_sq_fin, s_fin))
  }

  pub fn verify<T: ProofTranscript<G1Projective>>(
    &self,
    cs: ConstraintSystemRef<Fr>,
    transcript: &mut T,
    n: usize,
    a: &[Fr],
    Gamma: &G1Projective,
    G: &[G1Projective],
  ) -> Result<(G1Projective, G1Projective, Fr), SynthesisError> {
    let (u_sq, u_inv_sq, s) = self.verification_scalars(cs.clone(), transcript, n)?;

    let G_hat : G1Projective = G1Projective::msm_circuit(G, s.as_ref(), cs.clone()).unwrap();
    //let G_hat_affine = G_hat.into_affine();
    //let x = G_hat_affine.x().unwrap();
    //let y = G_hat_affine.y().unwrap();

    //let _x_wiz = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(x)).unwrap();
    //let _y_wiz = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(y)).unwrap();

    let a_hat = inner_product_circuit(cs.clone(), a, &s);
    let a_hat_witness = FpVar::new_witness(cs.clone(), || Ok(a_hat))?;

    let bases = [
      self.L_vec.as_slice(),
      self.R_vec.as_slice(),
      &[*Gamma]
      ].concat();

    let bases = bases.as_slice();

    let scalars = u_sq
      .into_iter()
      .chain(u_inv_sq.into_iter())
      .chain([Fr::one()])
      .collect::<Vec<_>>();

    let Gamma_hat = G1Projective::msm_circuit(bases, scalars.as_ref(), cs.clone()).unwrap();

    Ok((G_hat, Gamma_hat, a_hat))

  }

}

pub struct DotProductProofGens {
  n: usize,
  pub gens_n: MultiCommitGens<G1Projective>,
  pub gens_1: MultiCommitGens<G1Projective>,
}

impl DotProductProofGens {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let (gens_n, gens_1) = MultiCommitGens::new(n + 1, label).split_at(n);
    DotProductProofGens { n, gens_n, gens_1 }
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DotProductProofLog {
  bullet_reduction_proof: BulletReductionProof,
  delta: G1Projective,
  beta: G1Projective,
  z1: Fr,
  z2: Fr,
}

impl DotProductProofLog {
  pub fn verify<T: ProofTranscript<G1Projective>>(
    &self,
    cs: ConstraintSystemRef<Fr>,
    transcript: &mut T,
    n: usize,
    gens: &DotProductProofGens,
    a: &[Fr],
    Cx: &G1Projective,
    Cy: &G1Projective,
  ) -> Result<(), SynthesisError> {
    assert_eq!(gens.n, n);
    assert_eq!(a.len(), n);

    transcript.append_point(b"Cx", Cx);
    transcript.append_point(b"Cy", Cy);
    for i in 0..a.len() {
      transcript.append_scalar(b"a", &a[i]);
    }

    let Gamma = *Cx + *Cy;

    
    /*
    The bases fed to msm are considered public inputs.
    let Cx_wit = (
      NonNativeFieldVar::<Fq, Fr>::new_input(cs.clone(), || Ok(Cx.x))?,
      NonNativeFieldVar::<Fq, Fr>::new_input(cs.clone(), || Ok(Cx.y))?,
      NonNativeFieldVar::<Fq, Fr>::new_input(cs.clone(), || Ok(Cx.z))?,
    );

    let Cy_wit = (
      NonNativeFieldVar::<Fq, Fr>::new_input(cs.clone(), || Ok(Cy.x))?,
      NonNativeFieldVar::<Fq, Fr>::new_input(cs.clone(), || Ok(Cy.y))?,
      NonNativeFieldVar::<Fq, Fr>::new_input(cs.clone(), || Ok(Cy.z))?,
    );

    //Addition works normally as these are all values in the EC base field.
    let Gamma_x = Cx_wit.0 + Cy_wit.0;
    let Gamma_y = Cx_wit.1 + Cy_wit.1;
    let Gamma_z = Cx_wit.2 + Cy_wit.2;
    */

    // G, G, and Fp elem
    let (g_hat, Gamma_hat, a_hat) =
      self
        .bullet_reduction_proof
        .verify(
          cs.clone(),
          transcript,
          n,
          a,
          &Gamma,
          &gens.gens_n.G
        )?;

    transcript.append_point(b"delta", &self.delta);
    transcript.append_point(b"beta", &self.beta);

    let c = transcript.challenge_scalar(b"c");

    let c_s = &c;
    let beta_s = self.beta;
    let a_hat_s = &a_hat;
    let delta_s = self.delta;
    let z1_s = &self.z1;
    let z2_s = &self.z2;

    //lhs in a circuit.

    let c_s_wit = FpVar::new_witness(cs.clone(), || Ok(c))?;
    let c_s_wit_bits = if let FpVar::Var(c_s_wit_bits) = c_s_wit {
      c_s_wit_bits
    } else {
        unreachable!()
    };

    let c_bits = <AllocatedFp<Fr> as ToBitsGadget<Fr>>::to_bits_le(&c_s_wit_bits).expect("Failed to convert num to bits");

    let Gamma_hat_x = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(Gamma_hat.x))?;
    let Gamma_hat_y = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(Gamma_hat.y))?;
    let Gamma_hat_z = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(Gamma_hat.z))?;

    let mut result_x = FpVar::new_witness(cs.clone(), || Ok(Fr::one())).unwrap();
    let mut result_y = FpVar::new_witness(cs.clone(), || Ok(Fr::one())).unwrap();
    let mut result_z = FpVar::new_witness(cs.clone(), || Ok(Fr::one())).unwrap();

    //Make everything into the scalar field.
    let gamma_x_scalar = &Gamma_hat_x.to_constraint_field()?[0];
    let gamma_y_scalar = &Gamma_hat_y.to_constraint_field()?[0];
    let gamma_z_scalar = &Gamma_hat_z.to_constraint_field()?[0];

    //Gamma_hat * c_s = result
    for bit in c_bits {
      let _ = result_x.square_in_place();
      let _ = result_y.square_in_place();
      let _ = result_z.square_in_place();

      if bit.value().unwrap() {
        result_x.mul_assign(gamma_x_scalar); 
        result_y.mul_assign(gamma_y_scalar); 
        result_z.mul_assign(gamma_z_scalar); 
      }
    }

    let beta_s_wit_x = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(beta_s.x))?;
    let beta_s_wit_y = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(beta_s.y))?;
    let beta_s_wit_z = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(beta_s.z))?;

    let beta_s_x_scalar = &beta_s_wit_x.to_constraint_field()?[0];
    let beta_s_y_scalar = &beta_s_wit_y.to_constraint_field()?[0];
    let beta_s_z_scalar = &beta_s_wit_z.to_constraint_field()?[0];

    //result + beta_s
    result_x = result_x + beta_s_x_scalar;
    result_y = result_y + beta_s_y_scalar;
    result_z = result_z + beta_s_z_scalar;

    // result * a_hat_s
    let a_hat_s_wit = FpVar::new_witness(cs.clone(), || Ok(a_hat_s))?;
    let a_hat_s_bits = if let FpVar::Var(a_hat_s_bits) = a_hat_s_wit {
      a_hat_s_bits
    } else {
        unreachable!()
    };

    let a_hat_s_bits = <AllocatedFp<Fr> as ToBitsGadget<Fr>>::to_bits_le(&a_hat_s_bits).expect("Failed to convert num to bits");

    // end 

    let lhs = (Gamma_hat * c_s + beta_s) * a_hat_s + delta_s;
    let rhs = (g_hat + gens.gens_1.G[0] * a_hat_s) * z1_s + gens.gens_1.h * z2_s;

    (lhs == rhs)
      .then_some(())
      .ok_or(SynthesisError::MissingCS)
  }
}

#[allow(unused)]
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

#[allow(unused)]
fn inner_product_circuit<F: PrimeField>(
  cs: ConstraintSystemRef<F>, 
  a: &[F], 
  b: &[F],
) -> F {

  assert_eq!(a.len(), b.len(), "Vectors must have equal length");

  let mut acc = FpVar::new_witness(cs.clone(), || Ok(F::zero())).unwrap();
  let mut out = FpVar::new_witness(cs.clone(), || Ok(F::zero())).unwrap();
  for i in 0..a.len() {
      let a_var = FpVar::new_input(cs.clone(), || Ok(a[i])).unwrap();
      let b_var = FpVar::new_input(cs.clone(), || Ok(b[i])).unwrap();

      let mul = a_var * b_var;
      acc += mul; 
      out += a[i] * b[i];
  }

  out.value().unwrap()
}

#[allow(unused)]
fn ln_without_floats(a: usize) -> usize {
  // log2(a) * ln(2)
  (ark_std::log2(a) * 69 / 100) as usize
}

/*
/// Circuit gadget that implements the sumcheck verifier
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
struct PrimarySumcheck<G: CurveGroup, const ALPHA: usize> {
  proof: SumcheckInstanceProof<G::ScalarField>,
  claimed_evaluation: G::ScalarField,
  eval_derefs: [G::ScalarField; ALPHA],
  //proof_derefs: CombinedTableEvalProof<G, ALPHA>,
}*/

#[cfg(test)]
mod tests {
  use super::*;
  use ark_bn254::{Fr, G1Projective};
  use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError, ConstraintSystem};
  use merlin::Transcript;
  //use serde::Serialize;

  #[test]
  fn bullet_reduction_constraint_count() -> Result<(), SynthesisError> {
    let cs = ConstraintSystem::<Fr>::new();
    let cs_ref = ConstraintSystemRef::new(cs);
    
    let l_vec = vec![G1Projective::rand(&mut ark_std::test_rng()); 5];
    let r_vec = vec![G1Projective::rand(&mut ark_std::test_rng()); 5];

    let g_vec = vec![G1Projective::rand(&mut ark_std::test_rng()); 32];
    
    let proof = BulletReductionProof {
        L_vec: l_vec,
        R_vec: r_vec,
    };

    let mut verifier_transcript = Transcript::new(b"example");
    
    let _ = proof.verify(
      cs_ref.clone(),
      &mut verifier_transcript,
      32,
      &[Fr::rand(&mut ark_std::test_rng()); 32],
      &G1Projective::rand(&mut ark_std::test_rng()),
      g_vec.as_slice(), );
    
    println!("Number of constraints: {}", cs_ref.num_constraints());

    //let serialized = serde_json::to_string(&cs).unwrap();
    //std::fs::write("constraints.json", serialized);
    
    Ok(())
  }

  #[test]
  fn sumcheck_constraint_count() -> Result<(), SynthesisError> {

      let cs = ConstraintSystem::<Fr>::new();
      let cs_ref = ConstraintSystemRef::new(cs);

      let mut transcript = Transcript::new(b"dummy-label");

      let poly_coeffs = vec![FpVar::new_input(cs_ref.clone(), || Ok(Fr::rand(&mut ark_std::test_rng()))).unwrap(); 10]; 
      let compressed_poly = CompressedUniPolyVar {
          coeffs_except_linear_term: poly_coeffs
      };

      let proof = SumcheckInstanceProof {
          compressed_polys: vec![compressed_poly; 5] 
      };

      let _ = proof.verify_sumcheck::<G1Projective, Transcript>(
          cs_ref.clone(), 
          Fr::rand(&mut ark_std::test_rng()),
          5, 
          10,
          &mut transcript,
      )?;

      println!("Number of constraints: {}", cs_ref.num_constraints());

      Ok(())
  }

}

