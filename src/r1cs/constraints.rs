use bellpepper::gadgets::boolean::Boolean;
use bellpepper::gadgets::Assignment;
use bellpepper_core::{
  boolean::AllocatedBit,
  num::AllocatedNum,
  ConstraintSystem, LinearCombination, SynthesisError
};
use core::marker::PhantomData;
use ff::Field;
use ff::PrimeField;

use crate::utils::math::Math;
use super::sparse_mlpoly::{
  SparsePolyEntry, SparsePolynomial,
};
use crate::poly::unipoly::{CompressedUniPoly, UniPoly};

/// A helper trait for sumcheck verification part of Spartan.
pub trait SumcheckBaseCircuit<F: PrimeField>: Send + Sync + Clone {
  fn arity(&self) -> usize;

  /// Sythesize the circuit for a computation step and return variable
  /// that corresponds to the output of the step z_{i+1}
  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    z: &[AllocatedNum<F>],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>;
}

/// Allocate a variable that is set to zero
pub fn alloc_zero<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let zero = AllocatedNum::alloc(cs.namespace(|| "alloc"), || Ok(F::ZERO))?;
  cs.enforce(
    || "check zero is valid",
    |lc| lc,
    |lc| lc,
    |lc| lc + zero.get_variable(),
  );
  Ok(zero)
}

/// If condition return a otherwise b
pub fn conditionally_select<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  b: &AllocatedNum<F>,
  condition: &Boolean,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let c = AllocatedNum::alloc(cs.namespace(|| "conditional select result"), || {
    if *condition.get_value().get()? {
      Ok(*a.get_value().get()?)
    } else {
      Ok(*b.get_value().get()?)
    }
  })?;

  // a * condition + b*(1-condition) = c ->
  // a * condition - b*condition = c - b
  cs.enforce(
    || "conditional select constraint",
    |lc| lc + a.get_variable() - b.get_variable(),
    |_| condition.lc(CS::one(), F::ONE),
    |lc| lc + c.get_variable() - b.get_variable(),
  );

  Ok(c)
}

/// Allocate a variable that is set to one
pub fn alloc_one<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let one = AllocatedNum::alloc(cs.namespace(|| "alloc"), || Ok(F::ONE))?;
  cs.enforce(
    || "check one is valid",
    |lc| lc + CS::one(),
    |lc| lc + CS::one(),
    |lc| lc + one.get_variable(),
  );

  Ok(one)
}

#[allow(dead_code)]
/// c = a + b where a, b is AllocatedNum
pub fn add_allocated_num<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  a: &AllocatedNum<F>,
  b: &AllocatedNum<F>,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let c = AllocatedNum::alloc(cs.namespace(|| "c"), || {
    Ok(*a.get_value().get()? + b.get_value().get()?)
  })?;
  cs.enforce(
    || "Check u_fold",
    |lc| lc + a.get_variable() + b.get_variable(),
    |lc| lc + CS::one(),
    |lc| lc + c.get_variable(),
  );
  Ok(c)
}

#[allow(dead_code)]
/// implemented refer from https://github.com/lurk-lab/lurk-rs/blob/4335fbb3290ed1a1176e29428f7daacb47f8033d/src/circuit/gadgets/data.rs#L387-L402
pub fn alloc_const<F: PrimeField, CS: ConstraintSystem<F>>(
  mut cs: CS,
  val: F,
) -> Result<AllocatedNum<F>, SynthesisError> {
  let allocated = AllocatedNum::<F>::alloc(cs.namespace(|| "allocate const"), || Ok(val))?;

  // allocated * 1 = val
  cs.enforce(
    || "enforce constant",
    |lc| lc + allocated.get_variable(),
    |lc| lc + CS::one(),
    |_| Boolean::Constant(true).lc(CS::one(), val),
  );

  Ok(allocated)
}

#[derive(Clone, Debug, Default)]
  struct CubicCircuit<F: PrimeField> {
    _p: PhantomData<F>,
  }

  impl<F> SumcheckBaseCircuit<F> for CubicCircuit<F>
  where
    F: PrimeField,
  {
    fn arity(&self) -> usize {
      1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      // Consider a cubic equation: `x^3 + x + 5 = y`, where `x` and `y` are respectively the input and output.
      let x = &z[0];
      let x_sq = x.square(cs.namespace(|| "x_sq"))?;
      let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), x)?;
      let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
        Ok(x_cu.get_value().unwrap() + x.get_value().unwrap() + F::from(5u64))
      })?;

      cs.enforce(
        || "y = x^3 + x + 5",
        |lc| {
          lc + x_cu.get_variable()
            + x.get_variable()
            + CS::one()
            + CS::one()
            + CS::one()
            + CS::one()
            + CS::one()
        },
        |lc| lc + CS::one(),
        |lc| lc + y.get_variable(),
      );

      Ok(vec![y])
    }
  }

  impl<F> CubicCircuit<F>
  where
    F: PrimeField,
  {
    fn output(&self, z: &[F]) -> Vec<F> {
      vec![z[0] * z[0] * z[0] + z[0] + F::from(5u64)]
    }
  }