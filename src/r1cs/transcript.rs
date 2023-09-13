use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
/// Transcript is the application level transcript to derive the challenges
/// needed for Fiat Shamir during aggregation. It is given to the
/// prover/verifier so that the transcript can be fed with any other data first.
/// TODO: Make this trait the only Transcript trait
pub trait Transcript {
  fn domain_sep(&mut self);
  fn append<S: CanonicalSerialize>(&mut self, label: &'static [u8], point: &S);
  fn challenge_scalar<F: PrimeField>(&mut self, label: &'static [u8]) -> F;
  fn challenge_scalar_vec<F: PrimeField>(&mut self, label: &'static [u8], n: usize) -> Vec<F> {
    (0..n).map(|_| self.challenge_scalar(label)).collect()
  }
}

pub use crate::r1cs::poseidon_transcript::TranscriptWriter;