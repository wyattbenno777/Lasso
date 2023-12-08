use ark_std::vec::Vec;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::{
  alloc::AllocVar,
  fields::fp::{FpVar, AllocatedFp},
  prelude::EqGadget,
  bits::boolean::Boolean,
  prelude::*,
};
use ark_bn254::Fr as Fr;

pub fn modulo(num: FpVar<Fr>, mod_value: FpVar<Fr>) -> FpVar<Fr> {

    let num_var = if let FpVar::Var(num_var) = num {
      num_var
    } else {
        unreachable!()
    };
  
    let mod_var = if let FpVar::Var(mod_var) = mod_value {
      mod_var
    } else {
        unreachable!()
    };
  
    let num_bits = <AllocatedFp<Fr> as ToBitsGadget<Fr>>::to_bits_le(&num_var).expect("Failed to convert num to bits");
    let mod_bits = <AllocatedFp<Fr> as ToBitsGadget<Fr>>::to_bits_le(&mod_var).expect("Failed to convert mod to bits");
  
    let m = mod_bits.len();
    let n = num_bits.len();
  
    assert!(n >= m);
    
    let mut q = vec![Boolean::<Fr>::constant(false); n - m + 1];
  
    for i in (0..n - m + 1).rev() {
  
      //TODO: may need range checks for this.
      if i + m >= 254 {
        break;
      }
        
      let mut t = Boolean::<Fr>::constant(true);
      for j in (0..m).rev() {
          let t_next = q[i].clone().xor(&mod_bits[j]);
          t = t.and(&num_bits[i + j].xor(&t_next.expect("Failed to xor t_next")).unwrap()).expect("Failed to and");
      }
  
      q[i] = t.clone().xor(&num_bits[i + m]).expect("Failed to xor t and num_bits");
        
    }
  
    let r = num_bits[0..m].to_vec();
    
    Boolean::le_bits_to_fp_var(&r).expect("Failed to convert bits to FpVar")
    
}
  
/*
    1        = 2^0 = 1  
    10       = 2^1 = 2
    100      = 2^2 = 4 
    1000     = 2^3 = 8
*/
pub fn is_power_of_two(x: FpVar<Fr>) -> Result<Boolean<Fr>, SynthesisError> {
  
    let x_var = if let FpVar::Var(x_var) = x {
        x_var
    } else {
        unreachable!()
    };
  
    let x_bits = <AllocatedFp<Fr> as ToBitsGadget<Fr>>::to_bits_le(&x_var).unwrap();
  
    let mut found_one = false;
    for (i, bit) in x_bits.into_iter().enumerate() {
        if i == 0 {
          // First bit must be set
          let _ = bit.enforce_equal(&Boolean::TRUE);  
        } else if found_one {
          // Subsequent bits must be false
          let _ = bit.enforce_equal(&Boolean::FALSE);
        } else if bit.value().unwrap_or(false) {
            found_one = true; 
        }
    }
  
    Ok(Boolean::constant(found_one))
}
  
pub fn bitwise_or_assign(
    a: FpVar<Fr>, 
    t: FpVar<Fr>,
    ) -> FpVar<Fr> {
  
    // Decompose `a` into bits
    let a_var = if let FpVar::Var(a_var) = a {
      a_var
    } else {
        unreachable!()
    };
  
    // Decompose `t` into bits
    let t_var = if let FpVar::Var(t_var) = t {
      t_var
    } else {
        unreachable!()
    };
  
    // Decompose a and t into bits
    let a_bits = <AllocatedFp<Fr> as ToBitsGadget<Fr>>::to_bits_le(&a_var).unwrap();
    let t_bits = <AllocatedFp<Fr> as ToBitsGadget<Fr>>::to_bits_le(&t_var).unwrap();
  
    assert_eq!(a_bits.len(), t_bits.len());
  
    // Build result bits with bitwise OR
    let mut result_bits = vec![Boolean::FALSE; a_bits.len()];
    for ((a, t), r) in a_bits.iter().zip(t_bits.iter()).zip(result_bits.iter_mut()) {
        *r = a.or(t).unwrap(); 
    }
  
    Boolean::le_bits_to_fp_var(&result_bits).unwrap()
}
  
pub fn right_shift(a: FpVar<Fr>, shift: u64, cs: ConstraintSystemRef<Fr>) -> FpVar<Fr> {
  
    // Decompose `a` into bits
    let a_var = if let FpVar::Var(a_var) = a {
      a_var
    } else {
        unreachable!()
    };
  
    let a_bits = <AllocatedFp<Fr> as ToBitsGadget<Fr>>::to_bits_le(&a_var).unwrap();
      
    let shift_const = FpVar::new_constant(cs.clone(), Fr::from(a_bits.len() as u64 - shift as u64)).unwrap();
    let mut result_bits = vec![Boolean::FALSE; a_bits.len()];
  
    for (i, bit) in a_bits.clone().into_iter().enumerate() {
  
        let index_var = FpVar::new_witness(cs.clone(), || Ok(Fr::from(i as u64))).unwrap();
        let index_in_range = index_var.is_eq(&shift_const).unwrap();
  
        result_bits[i] = index_in_range
              .select(&bit, &Boolean::FALSE).unwrap();
    }
  
    let result_var = Boolean::le_bits_to_fp_var(&result_bits[..a_bits.len() - shift as usize]).unwrap();
  
    result_var
}

pub fn left_shift(a: FpVar<Fr>, shift: u64, cs: ConstraintSystemRef<Fr>) -> FpVar<Fr> {

    // Decompose `a` into bits
    let a_var = if let FpVar::Var(a_var) = a {
      a_var
    } else {
        unreachable!()
    };
    let a_bits = <AllocatedFp<Fr> as ToBitsGadget<Fr>>::to_bits_le(&a_var).unwrap();
      
    let mut result_bits = Vec::new();
    let shift_const = FpVar::new_constant(cs.clone(), Fr::from(shift as u64)).unwrap();
  
    // Shift the bits  
    for (i, bit) in a_bits.into_iter().enumerate() {
          // Check if index >= shift
          let index_var = FpVar::new_witness(cs.clone(), || Ok(Fr::from(i as u64))).unwrap();
          let index_in_range = index_var.is_eq(&shift_const).unwrap();
          
          // Append the bit or false based on range check
          let new_bit = index_in_range.select(&bit, &Boolean::FALSE).unwrap();
  
          result_bits.push(new_bit);
    }
  
    let result_var = Boolean::le_bits_to_fp_var(&result_bits).unwrap();
  
    result_var
}