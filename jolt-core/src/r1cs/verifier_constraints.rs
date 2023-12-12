//! This module is an adaptation of code from Testudo and Lasso main branch.
//use ark_ec::pairing::Pairing;
use std::borrow::Borrow;
use std::marker::PhantomData;

use crate::{
  poly::unipoly::{UniPoly},
  utils::transcript::{AppendToTranscript, ProofTranscript},
  poly::dense_mlpoly::{DensePolynomial}
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

use crate::poly::commitments::{Commitments, MultiCommitGens};
use crate::poly::eq_poly::EqPolynomial;

#[cfg(not(feature = "ark-msm"))]
use super::super::msm::VariableBaseMSM;
use super::gadgets;
use ark_r1cs_std::groups::CurveVar;
use crate::utils::math::Math;

use crate::poly::structured_poly::StructuredOpeningProof;
use ark_ec::Group;

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

pub struct SurgePrimarySumcheck {
  sumcheck_proof: SumcheckInstanceProof,
  num_rounds: usize,
  claimed_evaluation: Fr,
  openings: PrimarySumcheckOpenings,
}

#[derive(Debug)]
struct PrimarySumcheckOpenings
{
    E_poly_openings: Vec<Fr>,
    E_poly_opening_proof: CombinedTableEvalProof,
}


impl PrimarySumcheckOpenings {
    fn verify_openings<T: ProofTranscript<G1Projective>>(
        &self,
        cs: ConstraintSystemRef<Fr>,
        commitment: &SurgeCommitment,
        opening_point: &Vec<Fr>,
        transcript: &mut T,
    ) -> Result<(), SynthesisError> {
        self.E_poly_opening_proof.verify(
            cs.clone(),
            opening_point,
            &self.E_poly_openings,
            &commitment.generators.E_commitment_gens,
            &commitment.E_commitment,
            transcript,
        )
    }
}

pub struct SurgeCommitment {
  generators: SurgeCommitmentGenerators,
  pub dim_read_commitment: CombinedTableCommitment,
  pub final_commitment: CombinedTableCommitment,
  pub E_commitment: CombinedTableCommitment,
}

pub struct SurgeCommitmentGenerators {
  pub dim_read_commitment_gens: PolyCommitmentGens,
  pub final_commitment_gens: PolyCommitmentGens,
  pub E_commitment_gens: PolyCommitmentGens,
}

pub struct SurgePolys {
  _group: PhantomData<G1Projective>,
  pub dim: Vec<DensePolynomial<Fr>>,
  pub read_cts: Vec<DensePolynomial<Fr>>,
  pub final_cts: Vec<DensePolynomial<Fr>>,
  pub E_polys: Vec<DensePolynomial<Fr>>,
}

#[derive(Debug)]
pub struct CombinedTableEvalProof {
    joint_proof: PolyEvalProof,
}

impl CombinedTableEvalProof {

  pub fn bound_poly_var_bot(
    cs: ConstraintSystemRef<Fr>,
    mut dense: DensePolynomial<Fr>,
    r: &Fr
  ) -> DensePolynomial<Fr> {
      let n = dense.len() / 2;
      for i in 0..n {
          let mut dense_wit_i = FpVar::new_witness(cs.clone(), || Ok(dense.Z[i])).unwrap();
          let dense_wit_1 = FpVar::new_witness(cs.clone(), || Ok(dense.Z[2 * i])).unwrap();
          let dense_wit_2 = FpVar::new_witness(cs.clone(), || Ok(dense.Z[2 * i + 1])).unwrap();
          let dense_wit_3 = FpVar::new_witness(cs.clone(), || Ok(dense.Z[2 * i])).unwrap();
          let r_wit = FpVar::new_witness(cs.clone(), || Ok(*r)).unwrap();  

          dense.Z[i] = dense.Z[2 * i] + *r * (dense.Z[2 * i + 1] - dense.Z[2 * i]);
          dense_wit_i = dense_wit_1 + r_wit * (dense_wit_2 - dense_wit_3);
      }
      dense.num_vars -= 1;
      dense.len = n;
      dense
  }
 
  fn verify_single<T: ProofTranscript<G1Projective>>(
      cs: ConstraintSystemRef<Fr>,
      proof: &PolyEvalProof,
      comm: &PolyCommitment,
      r: &[Fr],
      evals: &[Fr],
      gens: &PolyCommitmentGens,
      transcript: &mut T,
  ) -> Result<(), SynthesisError> {
    
      // append the claimed evaluations to transcript
      for i in 0..evals.len() {
        transcript.append_scalar(b"evals_ops_val", &evals[0]);
      }

      // n-to-1 reduction
      let mut challenges = Vec::with_capacity(evals.len().log_2());
      //let mut challeneges_witness = Vec::with_capacity(evals.len().log_2());

      // Might not need the challenges as witness.
      for i in 0..challenges.len() {          
          let c = transcript.challenge_scalar(b"challenge");   
          //let c_s_wit = FpVar::new_witness(cs.clone(), || Ok(c))?;    
          challenges.push(c);
          //challeneges_witness.push(c_s_wit);
      }

      let mut poly_evals = DensePolynomial::new(evals.to_vec());
      for i in (0..challenges.len()).rev() {
        poly_evals = CombinedTableEvalProof::bound_poly_var_bot(cs.clone(), poly_evals, &challenges[i]);
      }
      assert_eq!(poly_evals.len(), 1);
      let joint_claim_eval = poly_evals[0];
      let mut r_joint = challenges;
      r_joint.extend(r);

      // decommit the joint polynomial at r_joint
      transcript.append_scalar(b"joint_claim_eval", &joint_claim_eval);

      proof.verify_plain(cs.clone(), gens, transcript, &r_joint, &joint_claim_eval, comm)
  }

  // verify evaluations of both polynomials at r
  pub fn verify<T: ProofTranscript<G1Projective>>(
      &self,
      cs: ConstraintSystemRef<Fr>,
      r: &[Fr],
      evals: &[Fr],
      gens: &PolyCommitmentGens,
      comm: &CombinedTableCommitment,
      transcript: &mut T,
  ) -> Result<(), SynthesisError> {
      let mut evals = evals.to_owned();
      evals.resize(evals.len().next_power_of_two(), Fr::zero());

      CombinedTableEvalProof::verify_single(
          cs.clone(),
          &self.joint_proof,
          &comm.joint_commitment,
          r,
          &evals,
          gens,
          transcript,
      )
  }
}

#[derive(Debug)]
pub struct CombinedTableCommitment {
    joint_commitment: PolyCommitment,
}

impl CombinedTableCommitment {
    pub fn new(joint_commitment: PolyCommitment) -> Self {
        Self { joint_commitment }
    }
}

pub struct PolyCommitmentGens {
  pub gens: DotProductProofGens,
}

impl PolyCommitmentGens {
  // the number of variables in the multilinear polynomial
  pub fn new(num_vars: usize, label: &'static [u8]) -> Self {
      let (_left, right) = EqPolynomial::<Fr>::compute_factored_lens(num_vars);
      let gens = DotProductProofGens::new(right.pow2(), label);
      PolyCommitmentGens { gens }
  }
}

#[derive(Debug, PartialEq)]
pub struct PolyCommitment {
    C: Vec<G1Projective>,
}

#[derive(Debug)]
pub struct PolyEvalProof {
    proof: DotProductProof,
}

impl PolyEvalProof {

  pub fn compute_factored_lens(ell: usize) -> (usize, usize) {
    (ell / 2, ell - ell / 2)
  }

  //Using repeated squaring property of polynomials.
  pub fn evals(
    cs: ConstraintSystemRef<Fr>,
    eq: EqPolynomial<Fr>
  ) -> Vec<Fr> {
      let ell = eq.r.len();

      let one_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::one())).unwrap();
      let two_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(2 as u64))).unwrap();


      let mut evals: Vec<FpVar<Fr>> = vec![one_witness.clone(); ell.pow2()];
      let mut size = one_witness;
      let mut size_num = 1;
      for j in 0..ell {
          // in each iteration, we double the size
          size *= two_witness.clone();
          size_num *= 2;
          let eq_r_witness = FpVar::new_witness(cs.clone(), || Ok(eq.r[j])).unwrap();
          
          for i in (0..size_num).rev().step_by(2) {
              // copy each element from the prior iteration twice
              let scalar = evals[i / 2].clone();
              evals[i] = scalar.clone() * eq_r_witness.clone();
              evals[i - 1] = scalar.clone() - evals[i].clone();
          }
      }
      let mut final_evals: Vec<Fr> = vec![Fr::one(); ell.pow2()];
      for i in 0..final_evals.len() {
        final_evals[i] = evals[i].value().unwrap();
      }
      final_evals
  }

  pub fn compute_factored_evals(
    cs: ConstraintSystemRef<Fr>,
    eq: EqPolynomial<Fr>
  ) -> (Vec<Fr>, Vec<Fr>) {
      let ell = eq.r.len();
      let ell_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(ell as u64))).unwrap();

      let (left_num_vars, _right_num_vars) = PolyEvalProof::compute_factored_lens(ell);

      let one_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::one())).unwrap();
      let two_witness = FpVar::new_witness(cs.clone(), || Ok(Fr::from(2 as u64))).unwrap();

      let inv_two_witness = FpVar::new_witness(cs.clone(), || {
        let two = two_witness.value().unwrap();
        Ok(two.inverse().unwrap())
      });

      // Multiply inverse by ell_witness to calculate ell / 2
      // This works because:
      //     ell / 2 
      // = ell * (1/2)    // Divide by 2
      // = ell * inv_two  // Multiply by modular multiplicative inverse
      let left_num_vars_witness = ell_witness * inv_two_witness.unwrap();

      let L = PolyEvalProof::evals(cs.clone(), EqPolynomial::new(eq.r[..left_num_vars].to_vec()));
      let R = PolyEvalProof::evals(cs.clone(), EqPolynomial::new(eq.r[left_num_vars..ell].to_vec()));

      (L, R)
  }

  pub fn verify<T: ProofTranscript<G1Projective>>(
      &self,
      cs: ConstraintSystemRef<Fr>,
      gens: &PolyCommitmentGens,
      transcript: &mut T,
      r: &[Fr], // point at which the polynomial is evaluated
      C_Zr: &G1Projective,             // commitment to \widetilde{Z}(r)
      comm: &PolyCommitment,
  ) -> Result<(), SynthesisError> {

      let r_vec = r.to_vec();

      //add r to circuit.
      for i in 0..r_vec.len() {
        let _ = FpVar::new_witness(cs.clone(), || Ok(r_vec[i])).unwrap();
      }

      // compute L and R
      let eq: EqPolynomial<_> = EqPolynomial::new(r_vec);
      let (L, R) = PolyEvalProof::compute_factored_evals(cs.clone(), eq);

      let C_LZ = G1Projective::msm_circuit(comm.C.as_ref(), L.as_ref(), cs.clone()).unwrap();

      self.proof.verify(
          cs.clone(),
          &gens.gens.gens_1,
          &gens.gens.gens_n,
          transcript,
          &R,
          &C_LZ,
          C_Zr,
      )
  }

  pub fn verify_plain<T: ProofTranscript<G1Projective>>(
      &self,
      cs: ConstraintSystemRef<Fr>,
      gens: &PolyCommitmentGens,
      transcript: &mut T,
      r: &[Fr], // point at which the polynomial is evaluated
      Zr: &Fr,  // evaluation \widetilde{Z}(r)
      comm: &PolyCommitment,
  ) -> Result<(), SynthesisError> {
      // compute a commitment to Zr with a blind of zero
      let C_Zr = Zr.commit(&Fr::zero(), &gens.gens.gens_1);

      self.verify(cs.clone(), gens, transcript, r, &C_Zr, comm)
  }
}

#[derive(Debug, Clone)]
pub struct DotProductProof {
    delta: G1Projective,
    beta: G1Projective,
    z: Vec<Fr>,
    z_delta: Fr,
    z_beta: Fr,
}

impl DotProductProof {

  pub fn compute_dotproduct(
      cs: ConstraintSystemRef<Fr>,
      a: &[Fr],
      b: &[Fr]
    ) -> FpVar<Fr> {
      assert_eq!(a.len(), b.len());

      let mut sum = FpVar::new_witness(cs.clone(), || Ok(Fr::from(0 as u64))).unwrap();

      for i in 0..a.len() {
        let a_wit = FpVar::new_witness(cs.clone(), || Ok(a[i])).unwrap();
        let b_wit = FpVar::new_witness(cs.clone(), || Ok(b[i])).unwrap();
        sum += (a_wit * b_wit);
      }
      sum
  }
  
  fn batch_commit_blinded_r1cs(
    cs: ConstraintSystemRef<Fr>,
    inputs: &[Fr],
    blind: &Fr,
    gens_n: &MultiCommitGens<G1Projective>) -> G1Projective {
    assert_eq!(gens_n.n, inputs.len());

    let mut combined_bases = gens_n.G.clone();
    combined_bases.push(gens_n.h);

    let mut scalars = inputs.to_vec();
    scalars.push(*blind);

    G1Projective::msm_circuit(combined_bases.as_ref(), scalars.as_ref(), cs.clone()).unwrap()

  }

  pub fn verify<T: ProofTranscript<G1Projective>>(
      &self,
      cs: ConstraintSystemRef<Fr>,
      gens_1: &MultiCommitGens<G1Projective>,
      gens_n: &MultiCommitGens<G1Projective>,
      transcript: &mut T,
      a: &[Fr],
      Cx: &G1Projective,
      Cy: &G1Projective,
  ) -> Result<(), SynthesisError> {
      if a.len() != gens_n.n {
          return Err(SynthesisError::MissingCS);
      }
      if gens_1.n != 1 {
          return Err(SynthesisError::MissingCS);
      }

      transcript.append_point(b"Cx", Cx);
      transcript.append_point(b"Cy", Cy);

      for i in 0..a.len() {
        transcript.append_scalar(b"a", &a[i]);
      }
      transcript.append_point(b"delta", &self.delta);
      transcript.append_point(b"beta", &self.beta);

      let c = transcript.challenge_scalar(b"c");
      let c_witness = FpVar::new_witness(cs.clone(), || Ok(c))?;

      // Cx and delta
      let Cx_wit_x = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(Cx.x))?;
      let Cx_wit_y = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(Cx.y))?;
      let Cx_wit_z = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(Cx.z))?;

      let Delta_wit_x = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(self.delta.x))?;
      let Delta_wit_y = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(self.delta.y))?;
      let Delta_wit_z = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(self.delta.z))?;

      let Cx_wit_x_scalar = &Cx_wit_x.to_constraint_field()?[0];
      let Cx_wit_y_scalar = &Cx_wit_y.to_constraint_field()?[0];
      let Cx_wit_z_scalar = &Cx_wit_z.to_constraint_field()?[0];

      let Delta_wit_x_scalar = &Delta_wit_x.to_constraint_field()?[0];
      let Delta_wit_y_scalar = &Delta_wit_y.to_constraint_field()?[0];
      let Delta_wit_z_scalar = &Delta_wit_z.to_constraint_field()?[0];

      let Cx_wit_x_scalar_1 = &(Cx_wit_x_scalar * c_witness.clone() + Delta_wit_x_scalar);
      let Cx_wit_y_scalar_1 = &(Cx_wit_x_scalar * c_witness.clone() + Delta_wit_y_scalar);
      let Cx_wit_z_scalar_1 = &(Cx_wit_x_scalar * c_witness.clone() + Delta_wit_z_scalar);

      let msm_result = Self::batch_commit_blinded_r1cs(cs.clone(), self.z.as_ref(), &self.z_delta, gens_n);

      let msm_result_x = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(msm_result.x))?;
      let msm_result_y = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(msm_result.y))?;
      let msm_result_z = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(msm_result.z))?;

      let msm_result_x_scalar = &msm_result_x.to_constraint_field()?[0];
      let msm_result_y_scalar = &msm_result_y.to_constraint_field()?[0];
      let msm_result_z_scalar = &msm_result_z.to_constraint_field()?[0];

      // Compare in circuit below.
      let mut result = *Cx * c + self.delta == msm_result;

      let _ = Cx_wit_x_scalar_1.enforce_equal(&msm_result_x_scalar)?;
      let _ = Cx_wit_y_scalar_1.enforce_equal(&msm_result_y_scalar)?;
      let _ = Cx_wit_y_scalar_1.enforce_equal(&msm_result_y_scalar)?;

      //Cy and beta
      let Cy_wit_x = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(Cy.x))?;
      let Cy_wit_y = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(Cy.y))?;
      let Cy_wit_z = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(Cy.z))?;

      let Beta_wit_x = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(self.delta.x))?;
      let Beta_wit_y = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(self.beta.y))?;
      let Beta_wit_z = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(self.beta.z))?;

      let Cy_wit_x_scalar = &Cy_wit_x.to_constraint_field()?[0];
      let Cy_wit_y_scalar = &Cy_wit_y.to_constraint_field()?[0];
      let Cy_wit_z_scalar = &Cy_wit_z.to_constraint_field()?[0];

      let Beta_wit_x_scalar = &Beta_wit_x.to_constraint_field()?[0];
      let Beta_wit_y_scalar = &Beta_wit_y.to_constraint_field()?[0];
      let Beta_wit_z_scalar = &Beta_wit_z.to_constraint_field()?[0];

      let Cy_wit_x_scalar_1 = &(Cy_wit_x_scalar * c_witness.clone() + Delta_wit_x_scalar);
      let Cy_wit_y_scalar_1 = &(Cy_wit_y_scalar * c_witness.clone() + Delta_wit_y_scalar);
      let Cy_wit_z_scalar_1 = &(Cy_wit_z_scalar * c_witness.clone() + Delta_wit_z_scalar);

      let dotproduct_z_a = DotProductProof::compute_dotproduct(cs.clone(), &self.z, a);

      let gens_1_x = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(gens_1.G[0].x))?;
      let gens_1_y = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(gens_1.G[0].y))?;
      let gens_1_z = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(gens_1.G[0].z))?;

      let gens_1_x_scalar = &gens_1_x.to_constraint_field()?[0];
      let gens_1_y_scalar = &gens_1_y.to_constraint_field()?[0];
      let gens_1_z_scalar = &gens_1_z.to_constraint_field()?[0];

      let gens_1_h_witness_x = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(gens_1.h.x))?;
      let gens_1_h_witness_y = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(gens_1.h.y))?;
      let gens_1_h_witness_z = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(gens_1.h.z))?;

      let gens_1_h_witness_x_scalar = &gens_1_h_witness_x.to_constraint_field()?[0];
      let gens_1_h_witness_y_scalar = &gens_1_h_witness_y.to_constraint_field()?[0];
      let gens_1_h_witness_z_scalar = &gens_1_h_witness_z.to_constraint_field()?[0];

      //commit
      assert_eq!(gens_1.n, 1);
      let commit_result = gens_1.G[0] * dotproduct_z_a.value().unwrap() + gens_1.h * &self.z_beta;

      let z_beta_witness = FpVar::new_witness(cs.clone(), || Ok(self.z_beta))?;

      let commit_res_x = gens_1_x_scalar * dotproduct_z_a.clone() +
      gens_1_h_witness_x_scalar * z_beta_witness.clone();
      let commit_res_y = gens_1_y_scalar * dotproduct_z_a.clone() +
      gens_1_h_witness_y_scalar * z_beta_witness.clone();
      let commit_res_z = gens_1_z_scalar * dotproduct_z_a.clone() +
      gens_1_h_witness_z_scalar * z_beta_witness.clone();

      let _ = Cy_wit_x_scalar_1.enforce_equal(&commit_res_x)?;
      let _ = Cy_wit_y_scalar_1.enforce_equal(&commit_res_y)?;
      let _ = Cy_wit_z_scalar_1.enforce_equal(&commit_res_z)?;

      result &= *Cy * c + self.beta == commit_result;

      if result {
          Ok(())
      } else {
          Err(SynthesisError::MissingCS)
      }
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
#[derive(Debug)]
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

#[derive(Debug)]
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

  #[test]
  fn eval_proof_constraint_count() -> Result<(), SynthesisError> {

      let mut rng = ark_std::test_rng();
      let cs = ConstraintSystem::<Fr>::new();
      let cs_ref = ConstraintSystemRef::new(cs);
          
      // Generate sample data
      let r = (0..10).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();
      let evals = (0..32).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();

      let gens = PolyCommitmentGens::new(evals.len(), b"test");    
      let C: Vec<G1Projective> = (0..evals.len()).map(|_| {
          G1Projective::rand(&mut rng)
      }).collect();
      
      let commitment = PolyCommitment {
          C 
      };

      // Generate random proof data
      let z = (0..10).map(|_| Fr::rand(&mut rng)).collect();
      let z_delta = Fr::rand(&mut rng); 
      let z_beta = Fr::rand(&mut rng);
      let delta = G1Projective::rand(&mut rng);
      let beta = G1Projective::rand(&mut rng);

      let proof = PolyEvalProof {
          proof: DotProductProof {
              z,
              z_delta, 
              z_beta,
              delta,
              beta    
          }
      };

      // Verify proof 
      let mut transcript = Transcript::new(b"test");
      let result = proof.verify(
          cs_ref.clone(),
          &gens, 
          &mut transcript,
          &r,
          &G1Projective::generator(),
          &commitment,
      );

      println!("Number of constraints: {}", cs_ref.num_constraints());
      Ok(())
  }

  #[test]
  fn combined_table_eval_proof_constraint_count() -> Result<(), SynthesisError> {
      // Generate test data
      let mut rng = ark_std::test_rng();
      let cs = ConstraintSystem::<Fr>::new();
      let cs_ref = ConstraintSystemRef::new(cs);
      
      let r = vec![Fr::rand(&mut rng); 10];
      let evals = vec![Fr::rand(&mut rng); 1];
      
      let gens = PolyCommitmentGens::new(32, b"test");
      
      let commitment = CombinedTableCommitment::new({
          let C: Vec<G1Projective> = (0..32).map(|_| G1Projective::rand(&mut rng)).collect(); 
          PolyCommitment { C }
      });
      
      // Generate random proof data
      let z = (0..10).map(|_| Fr::rand(&mut rng)).collect();
      let z_delta = Fr::rand(&mut rng); 
      let z_beta = Fr::rand(&mut rng);
      let delta = G1Projective::rand(&mut rng);
      let beta = G1Projective::rand(&mut rng);

      let proof = PolyEvalProof {
          proof: DotProductProof {
              z,
              z_delta, 
              z_beta,
              delta,
              beta    
          }
      };

      let mut transcript = Transcript::new(b"test");

      // Verify proof
      let result = CombinedTableEvalProof {
          joint_proof: proof
      }
      .verify(
          cs_ref.clone(), 
          &r,
          &evals,
          &gens,
          &commitment,
          &mut transcript, 
      );
      
      println!("Number of constraints: {}", cs_ref.num_constraints());
      Ok(())
  }

}

