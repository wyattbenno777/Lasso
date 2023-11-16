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

        let mut fpv_poly = UniPolyVar::<>::new_variable(cs.clone(), || Ok(poly.clone()), AllocationMode::Witness)?;

        // verify degree bound
        assert_eq!(poly.degree(), degree_bound);

        // check if G_k(0) + G_k(1) = e
        assert_eq!(poly.eval_at_zero() + poly.eval_at_one(), e);
        let res = fpv_poly.eval_at_one() + fpv_poly.eval_at_zero();

        let d_e = FpVar::<F>::new_input(cs.clone(), || Ok(e))?;
        res.enforce_equal(&d_e)?;

        // append the prover's message to the transcript
        <UniPoly<F> as AppendToTranscript<G>>::append_to_transcript(&poly, b"poly", transcript);

        //derive the verifier's challenge for the next round
        let r_i = transcript.challenge_scalar(b"challenge_nextround");

        r.push(r_i);

        // evaluate the claimed degree-ell polynomial at r_i
        e = poly.evaluate(&r_i);
    }

    Ok((e, r))
  }

}

/*/// Circuit gadget that implements the sumcheck verifier
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
struct PrimarySumcheck<G: CurveGroup, const ALPHA: usize> {
  proof: SumcheckInstanceProof<G::ScalarField>,
  claimed_evaluation: G::ScalarField,
  eval_derefs: [G::ScalarField; ALPHA],
  //proof_derefs: CombinedTableEvalProof<G, ALPHA>,
}*/

