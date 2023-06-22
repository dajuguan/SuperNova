use crate::hypercube::BooleanHypercube;
use crate::spartan::math::Math;
use crate::spartan::polynomial::MultilinearPolynomial;
use crate::utils::bit_decompose;
use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_FE_FOR_RO, NUM_HASH_BITS},
  errors::NovaError,
  gadgets::{
    nonnative::{bignat::nat_to_limbs, util::f_to_nat},
    utils::scalar_as_base,
  },
  r1cs::{R1CSInstance, R1CSShape, R1CSWitness, R1CS},
  traits::{
    commitment::CommitmentEngineTrait, commitment::CommitmentTrait, AbsorbInROTrait, Group, ROTrait,
  },
  utils::*,
  Commitment, CommitmentKey, CE,
};
use bitvec::vec;
use core::{cmp::max, marker::PhantomData};
use ff::Field;
use flate2::{write::ZlibEncoder, Compression};
use itertools::concat;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sha3::{Digest, Sha3_256};
use std::ops::{Add, Mul};
use std::sync::Arc;

use super::virtual_poly::VirtualPolynomial;
use super::CCSShape;

/// A type that holds the shape of a Committed CCS (CCCS) instance
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CCCSShape<G: Group> {
  // Sequence of sparse MLE polynomials in s+s' variables M_MLE1, ..., M_MLEt
  pub(crate) M_MLE: Vec<MultilinearPolynomial<G::Scalar>>,

  pub(crate) ccs: CCSShape<G>,
}

/// A type that holds a CCCS instance
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CCCSInstance<G: Group> {
  // Commitment to a multilinear polynomial in s' - 1 variables
  pub(crate) C: Commitment<G>,

  // $x in F^l$
  pub(crate) x: Vec<G::Scalar>,
}

// NOTE: We deal with `r` parameter later in `nimfs.rs` when running `execute_sequence` with `ro_consts`
/// A type that holds a witness for a given CCCS instance
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CCCSWitness<G: Group> {
  // Multilinear polynomial w_mle in s' - 1 variables
  pub(crate) w_mle: Vec<G::Scalar>,
}

impl<G: Group> CCCSShape<G> {
  // TODO: Sanity check this
  pub fn compute_sum_Mz(
    &self,
    M_j: &MultilinearPolynomial<G::Scalar>,
    z: &MultilinearPolynomial<G::Scalar>,
    s_prime: usize,
  ) -> MultilinearPolynomial<G::Scalar> {
    assert_eq!(M_j.get_num_vars(), s_prime);
    assert_eq!(z.get_num_vars(), s_prime);

    let num_vars = M_j.get_num_vars();
    let two_to_num_vars = (2_usize).pow(num_vars as u32);
    let mut result_coefficients = Vec::with_capacity(two_to_num_vars);

    for i in 0..two_to_num_vars {
      let r = bit_decompose(i as u64, num_vars)
        .into_iter()
        .map(|bit| G::Scalar::from(if bit { 1 } else { 0 }))
        .collect::<Vec<_>>();

      let value = M_j.evaluate(&r) * z.evaluate(&r);
      result_coefficients.push(value);
    }

    MultilinearPolynomial::new(result_coefficients)
  }

  // Computes q(x) = \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
  // polynomial over x
  pub fn compute_q(
    &self,
    z: &Vec<G::Scalar>,
  ) -> Result<MultilinearPolynomial<G::Scalar>, &'static str> {
    // XXX: Do we need to instrument this to use s_prime as n_vars somehow?
    let z_mle = MultilinearPolynomial::new(z.clone());
    if z_mle.get_num_vars() != self.ccs.s_prime {
      return Err("z_mle number of variables does not match ccs.s_prime");
    }
    let mut q = MultilinearPolynomial::new(vec![G::Scalar::ZERO; self.ccs.s]);

    for i in 0..self.ccs.q {
      let mut prod = MultilinearPolynomial::new(vec![G::Scalar::ONE; self.ccs.s]);

      for j in &self.ccs.S[i] {
        let M_j = sparse_matrix_to_mlp(&self.ccs.M[*j]);

        let sum_Mz = self.compute_sum_Mz(&M_j, &z_mle, self.ccs.s_prime);

        // Fold this sum into the running product
        prod = prod.mul(sum_Mz)?;
      }

      // Multiply the product by the coefficient c_i
      prod = prod.scalar_mul(&self.ccs.c[i]);

      // Add it to the running sum
      q = q.add(prod)?;
    }

    Ok(q)

    // Similar logic in Spartan
    //     let (mut Az, mut Bz, mut Cz) = pk.S.multiply_vec(&z)?;
    //poly_Az: MultilinearPolynomial::new(Az.clone()),
  }
}

  /// Computes Q(x) = eq(beta, x) * q(x)
  ///               = eq(beta, x) * \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
  /// polynomial over x
  pub fn compute_Q(
    &self,
    z: &Vec<G::Scalar>,
    beta: &[G::Scalar],
  ) -> Result<VirtualPolynomial<G::Scalar>, NovaError> {
    let q = self.compute_q(z)?;
    q.build_f_hat(beta)
  }
}