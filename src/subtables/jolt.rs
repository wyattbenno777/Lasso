use ark_ff::PrimeField;

// use super::{SubtableStrategy, and::AndSubtableStrategy, or::OrSubtableStrategy};
use ark_curve25519::Fr;
use ark_std::One;

// trait JoltStrategy<F: PrimeField,  const C: usize, const M: usize> {
//   type Instructions;
//   const C: usize;
//   const M: usize;

//   // Note: To be able to return either of these, we need them to be trait objects. This means that the trait functions
//   // all take &self as a param. We cannot statically call any more. 
//   // Worth also trying the static route with macros.
//   fn get_subtable(instruction: Self::Instructions) -> Box<dyn SubtableStrategy<F, C, M>>;
//   fn get_subtables() -> Vec<Box<dyn SubtableStrategy<F, C, M>>>;

//   fn prove(&self, instructions: Vec<Self::Instructions>) {
//     unimplemented!("JoltStrategy::prove()");
//   }

//   fn verify(&self) {
//     unimplemented!("JoltStrategy::verify()");
//   }
// }

// JOLT
trait JoltStrategy {
  type F: PrimeField;
  const M: usize;
  const NUM_INSTRUCTIONS: usize;

  fn get_instructions() -> Vec<Box<dyn InstructionStrategy<Self::F, { Self::M }>>>;
}

pub struct Wasm {}
impl JoltStrategy for Wasm {
  type F = Fr;
  const M: usize = 16;
  const NUM_INSTRUCTIONS: usize = 1;

  fn get_instructions() -> Vec<Box<dyn InstructionStrategy<Self::F, { Self::M }>>> {
      vec![Box::new(AndInstruction::<{ Self::M }> {})]
  }
}

// INSTRUCTION

trait InstructionStrategy<F: PrimeField, const M: usize> {
  fn get_subtables(&self) -> Vec<Box<dyn SubtableStrategy<F, M>>>;
}

pub struct AndInstruction<const M: usize> {}
impl<F: PrimeField, const M: usize> InstructionStrategy<F, M> for AndInstruction<M> {
  fn get_subtables(&self) -> Vec<Box<dyn SubtableStrategy<F, M>>> {
      vec![Box::new(AndSubtable {})]
  }
}

// SUBTABLE
// TODO: SUBTABLE needs its own 'C'
// - Can't add to generics or the dyn SubtableStrategy's returned above need <F, M, C> -- why?
// - Can't add to an inline const or we screw up object safety and can't make a trait object (which we need for iteration)
// - If we add it to the object itself (not constant), we can no longer make downstream constant sized arrays from it

trait SubtableStrategy<F: PrimeField, const M: usize> {
  fn materialize(&self) -> [F; M];
}

pub struct AndSubtable {}
impl<F: PrimeField, const M: usize> SubtableStrategy<F, M> for AndSubtable {
  fn materialize(&self) -> [F; M] {
    std::array::from_fn(|i| {
      F::one()
    })
  }
}


// REMOVE GENERICS STRATEGY

// trait InstructionImpl {
//   fn get_subtables(&self) -> Vec<Box<dyn SubtableImpl>>;
// }
// pub struct AndInstruction {}
// impl InstructionImpl for AndInstruction {
//   fn get_subtables(&self) -> Vec<Box<dyn SubtableImpl>> {
//       vec![Box::new(AndSubtableImpl {})]
//   }
// }

// trait SubtableImpl {
//   type F: PrimeField;
//   const C: usize;
//   const M: usize;

//   fn materialize(&self) -> [Self::F; Self::M];
// }

// pub struct AndSubtableImpl {}
// impl SubtableImpl for AndSubtableImpl {
//   type F = Fr;
//   const C: usize = 4;
//   const M: usize = 16;

//   fn materialize(&self) -> [Fr; 16] {
//     std::array::from_fn(|i| {
//       Fr::one()
//     })
//   }
// }








// TODO: Make a subtable IMPL which defines the generics F, C, M

// struct Wasm {
//     and: AndSubtableStrategy,
//     or: OrSubtableStrategy,
// }

// impl Wasm {
//     fn new() -> Self {
//         Wasm {
//             and: AndSubtableStrategy,
//             or: OrSubtableStrategy
//         }
//     }
// }

// enum WasmInstruction {
//   And(u64, u64),
//   Or(u64, u64),
// }

// impl JoltStrategy for Wasm {
//   type Instructions = WasmInstruction;

//   fn get_subtable(instruction: Instructions) -> SubtableStrategy {
//       match instruction {
//         WasmInstruction::And(_, _) => AndSubtableStrategy,
//         WasmInstruction::Or => OrSubtableStrategy
//       }
//   }
// }

// What if the match was an array lookup?
// TODO: Currently we're handing SubtableStrategy as a type, we may want it as an impl to do this mapping

// JoltSubtableStrategy - (many) -> GrandProductArgument::new<M, C>()


// Wants
// Simple instruction lookup 
// Containerization:
// - Wasm::new() should hide the selections of <C, M> required for each SubtableStrategy


// fn main() {
//   let instructions: Vec<WasmInstruction> = vec![
//     WasmInstruction::And(12, 100),
//     WasmInstruction::Or(12, 100),
//     WasmInstruction::Or(12, 100),
//     WasmInstruction::Or(12, 100),
//     WasmInstruction::And(12, 100),
//   ];

//   let wasm_vm = Wasm::new();
//   let _proof = wasm_vm.prove(instructions);
//   let _verify_result = wasm_vm.verify();
// }
