//! This module is an adaptation of code from Testudo and Lasso main branch.
use ark_ec::pairing::Pairing;
use std::borrow::Borrow;

use crate::{
  utils::math::Math,
  poly::unipoly::{CompressedUniPoly, UniPoly},
  utils::transcript::{AppendToTranscript, ProofTranscript},
  utils::errors::ProofVerifyError,
};
use ark_ff::PrimeField;

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

    // Challenges are witness variables
    // Points are input variables
    // Squaring is enforced as a constraint

    pub fn verification_scalars<T: ProofTranscript<G>>(
        &self,
        cs: ConstraintSystemRef<G::ScalarField>,
        n: usize,
        transcript: &mut T,
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
        let mut challenges = Vec::with_capacity(lg_n);
        let mut _challenges_witness = Vec::with_capacity(lg_n);
        for (L, R) in self.L_vec.iter().zip(self.R_vec.iter()) {
            transcript.append_point( b"L", L);
            transcript.append_point( b"R", R);
            let c = transcript.challenge_scalar(b"u");

            let c_wit = FpVar::new_witness(cs.clone(), || Ok(c))?;
            let L_scalar = (*L).into();
            //let _lv = FpVar::new_input(cs.clone(), || Ok(L_scalar))?;
            //let _rv = FpVar::new_input(cs.clone(), || Ok(*R))?;
            _challenges_witness.push(c_wit);
            challenges.push(c);
        }

        // 2. Compute 1/(u_k...u_1) and 1/u_k, ..., 1/u_1
        // let mut challenges_inv = challenges.clone();
        let mut challenges_inv = challenges
        .iter()
        .map(|x| x.inverse().unwrap())
        .collect::<Vec<_>>();
        let mut all_inv = G::ScalarField::one();
        challenges_inv.iter().for_each(|c| all_inv *= *c);

        // 3. Compute u_i^2 and (1/u_i)^2
        for i in 0..lg_n {
            challenges[i] = challenges[i].square();
            challenges_inv[i] = challenges_inv[i].square();
        }
        let challenges_sq = challenges;
        let challenges_inv_sq = challenges_inv;

        // 4. Compute s values inductively.
        let mut s = vec![all_inv];
        for i in 1..n {
            let lg_i = (32 - 1 - (i as u32).leading_zeros()) as usize;
            let k = 1 << lg_i;
            // The challenges are stored in "creation order" as [u_k,...,u_1],
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_lg_i_sq = challenges_sq[(lg_n - 1) - lg_i];
            s.push(s[i - k] * u_lg_i_sq);
        }

        Ok((challenges_sq, challenges_inv_sq, s))
    }

}

/// Circuit gadget that implements the sumcheck verifier
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
struct PrimarySumcheck<G: CurveGroup, const ALPHA: usize> {
  proof: SumcheckInstanceProof<G::ScalarField>,
  claimed_evaluation: G::ScalarField,
  eval_derefs: [G::ScalarField; ALPHA],
  //proof_derefs: CombinedTableEvalProof<G, ALPHA>,
}

