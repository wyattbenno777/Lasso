use ark_ff::PrimeField;
use enum_dispatch::enum_dispatch;

use crate::jolt::{subtable::LassoSubtable, vm::test_vm::TestInstructionSet};

#[enum_dispatch]
pub trait JoltInstruction {
  fn combine_lookups<F: PrimeField>(&self, vals: &[F], C: usize, M: usize) -> F;
  fn g_poly_degree(&self, C: usize) -> usize;
  fn subtables<F: PrimeField>(&self) -> Vec<Box<dyn LassoSubtable<F>>>;
  fn to_indices(&self, C: usize, M: usize) -> Vec<usize>;
}

pub trait Opcode {
  fn to_opcode(&self) -> u8 {
    unsafe { *<*const _>::from(self).cast::<u8>() }
  }
}

pub mod and;
pub mod eq;
pub mod xor;

#[cfg(test)]
pub mod test;
