//! This module implements SuperNova NIVC.
// https://eprint.iacr.org/2022/1758.pdf
// By Wyatt Benno 2023.
#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(dead_code)]

use crate::ccs;

use crate::{
  constants::{NUM_CHALLENGE_BITS, NUM_FE_FOR_RO},
  errors::NovaError,
  r1cs::{R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness},
  scalar_as_base,
  traits::{
    AbsorbInROTrait, Group, ROConstants, ROConstantsCircuit, ROConstantsTrait, ROTrait,
    circuit::TrivialTestCircuit, circuit::StepCircuit,
    commitment::{CommitmentEngineTrait, CommitmentTrait}},
  Commitment, CommitmentKey, CompressedCommitment,
  circuit::{NovaAugmentedCircuit, NovaAugmentedCircuitInputs, NovaAugmentedCircuitParams},
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS}
};

use ff::Field;
use ff::PrimeField;
use core::marker::PhantomData;
use serde::{Deserialize, Serialize};

use crate::bellperson::{
  r1cs::{NovaShape, NovaWitness},
  shape_cs::ShapeCS,
  solver::SatisfyingAssignment,
};
use ::bellperson::{Circuit, ConstraintSystem};
use flate2::{write::ZlibEncoder, Compression};
use sha3::{Digest, Sha3_256};



use crate::nifs::NIFS;


fn compute_digest<G: Group, T: Serialize>(o: &T) -> G::Scalar {
  // obtain a vector of bytes representing public parameters
  let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
  bincode::serialize_into(&mut encoder, o).unwrap();
  let pp_bytes = encoder.finish().unwrap();

  // convert pp_bytes into a short digest
  let mut hasher = Sha3_256::new();
  hasher.input(&pp_bytes);
  let digest = hasher.result();

  // truncate the digest to NUM_HASH_BITS bits
  let bv = (0..NUM_HASH_BITS).map(|i| {
    let (byte_pos, bit_pos) = (i / 8, i % 8);
    let bit = (digest[byte_pos] >> bit_pos) & 1;
    bit == 1
  });

  // turn the bit vector into a scalar
  let mut digest = G::Scalar::ZERO;
  let mut coeff = G::Scalar::ONE;
  for bit in bv {
    if bit {
      digest += coeff;
    }
    coeff += coeff;
  }
  digest
}

/// A type that holds public parameters of Nova
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PublicParams<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
{
  F_arity_primary: usize,
  F_arity_secondary: usize,
  ro_consts_primary: ROConstants<G1>,
  ro_consts_circuit_primary: ROConstantsCircuit<G2>,
  ck_primary: Option<CommitmentKey<G1>>,
  r1cs_shape_primary: R1CSShape<G1>,
  ro_consts_secondary: ROConstants<G2>,
  ro_consts_circuit_secondary: ROConstantsCircuit<G1>,
  ck_secondary: Option<CommitmentKey<G2>>,
  r1cs_shape_secondary: R1CSShape<G2>,
  augmented_circuit_params_primary: NovaAugmentedCircuitParams,
  augmented_circuit_params_secondary: NovaAugmentedCircuitParams,
  digest: G1::Scalar, // digest of everything else with this field set to G1::Scalar::ZERO
  _p_c1: PhantomData<C1>,
  _p_c2: PhantomData<C2>,
}

impl<G1, G2, C1, C2> PublicParams<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
{
  /// Create a new `PublicParams`
  pub fn setup(c_primary: C1, c_secondary: C2, largest: bool) -> Self {
    let augmented_circuit_params_primary =
      NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);
    let augmented_circuit_params_secondary =
      NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, false);

    let ro_consts_primary: ROConstants<G1> = ROConstants::<G1>::new();
    let ro_consts_secondary: ROConstants<G2> = ROConstants::<G2>::new();

    let F_arity_primary = c_primary.arity();
    let F_arity_secondary = c_secondary.arity();

    // ro_consts_circuit_primary are parameterized by G2 because the type alias uses G2::Base = G1::Scalar
    let ro_consts_circuit_primary: ROConstantsCircuit<G2> = ROConstantsCircuit::<G2>::new();
    let ro_consts_circuit_secondary: ROConstantsCircuit<G1> = ROConstantsCircuit::<G1>::new();

    // Initialize ck for the primary
    let circuit_primary: NovaAugmentedCircuit<G2, C1> = NovaAugmentedCircuit::new(
      augmented_circuit_params_primary.clone(),
      None,
      c_primary,
      ro_consts_circuit_primary.clone(),
    );
    let mut cs: ShapeCS<G1> = ShapeCS::new();
    let _ = circuit_primary.synthesize(&mut cs);

    // We use the largest commitment_key for all instances
    let mut r1cs_shape_primary;
    let ck_primary;
    if largest {
      let (r1cs_shape_temp, ck_primary_temp) = cs.r1cs_shape();
      r1cs_shape_primary = r1cs_shape_temp;
      ck_primary = Some(ck_primary_temp);
    } else {
        r1cs_shape_primary = cs.r1cs_shape_supernova();
        ck_primary = None;
    }

    // Initialize ck for the secondary
    let circuit_secondary: NovaAugmentedCircuit<G1, C2> = NovaAugmentedCircuit::new(
      augmented_circuit_params_secondary.clone(),
      None,
      c_secondary,
      ro_consts_circuit_secondary.clone(),
    );
    let mut cs: ShapeCS<G2> = ShapeCS::new();
    let _ = circuit_secondary.synthesize(&mut cs);

    // We use the largest commitment_key for all instances
    let r1cs_shape_secondary;
    let ck_secondary;
    if largest {
      let (r1cs_shape_temp, ck_secondary_temp) = cs.r1cs_shape();
      r1cs_shape_secondary = r1cs_shape_temp;
      ck_secondary = Some(ck_secondary_temp);
    } else {
      r1cs_shape_secondary = cs.r1cs_shape_supernova();
      ck_secondary = None;
    }

    let mut pp = Self {
      F_arity_primary,
      F_arity_secondary,
      ro_consts_primary,
      ro_consts_circuit_primary,
      ck_primary,
      r1cs_shape_primary,
      ro_consts_secondary,
      ro_consts_circuit_secondary,
      ck_secondary,
      r1cs_shape_secondary,
      augmented_circuit_params_primary,
      augmented_circuit_params_secondary,
      digest: G1::Scalar::ZERO,
      _p_c1: Default::default(),
      _p_c2: Default::default(),
    };

    // set the digest in pp
    pp.digest = compute_digest::<G1, PublicParams<G1, G2, C1, C2>>(&pp);

    pp
  }

  /// Returns the number of constraints in the primary and secondary circuits
  pub fn num_constraints(&self) -> (usize, usize) {
    (
      self.r1cs_shape_primary.num_cons,
      self.r1cs_shape_secondary.num_cons,
    )
  }

  /// Returns the number of variables in the primary and secondary circuits
  pub fn num_variables(&self) -> (usize, usize) {
    (
      self.r1cs_shape_primary.num_vars,
      self.r1cs_shape_secondary.num_vars,
    )
  }
}

/// A SNARK that proves the correct execution of an non-uniform incremental computation
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct NivcSNARK<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
{
  r_W_primary: RelaxedR1CSWitness<G1>,
  r_U_primary: RelaxedR1CSInstance<G1>,
  r_W_secondary: RelaxedR1CSWitness<G2>,
  r_U_secondary: RelaxedR1CSInstance<G2>,
  l_w_secondary: R1CSWitness<G2>,
  l_u_secondary: R1CSInstance<G2>,
  i: usize,
  zi_primary: Vec<G1::Scalar>,
  zi_secondary: Vec<G2::Scalar>,
  _p_c1: PhantomData<C1>,
  _p_c2: PhantomData<C2>,
  program_counter: i32,
}

impl<G1, G2, C1, C2> NivcSNARK<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
{
  /// Create a new `NivcSNARK` (or updates the provided `NivcSNARK`)
  /// by executing a step of the incremental computation
  pub fn prove_step(
    pp: &PublicParams<G1, G2, C1, C2>,
    recursive_snark: Option<Self>,
    c_primary: C1,
    c_secondary: C2,
    z0_primary: Vec<G1::Scalar>,
    z0_secondary: Vec<G2::Scalar>,
  ) -> Result<Self, NovaError> {
    if z0_primary.len() != pp.F_arity_primary || z0_secondary.len() != pp.F_arity_secondary {
      return Err(NovaError::InvalidInitialInputLength);
    }

    match recursive_snark {
      None => {
        // base case for the primary
        let mut cs_primary: SatisfyingAssignment<G1> = SatisfyingAssignment::new();
        let inputs_primary: NovaAugmentedCircuitInputs<G2> = NovaAugmentedCircuitInputs::new(
          scalar_as_base::<G1>(pp.digest),
          G1::Scalar::ZERO,
          z0_primary.clone(),
          None,
          None,
          None,
          None,
        );

        let circuit_primary: NovaAugmentedCircuit<G2, C1> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_primary.clone(),
          Some(inputs_primary),
          c_primary.clone(),
          pp.ro_consts_circuit_primary.clone(),
        );
        let _ = circuit_primary.synthesize(&mut cs_primary);
        let (u_primary, w_primary) = match pp.ck_primary.as_ref() {
            Some(ck) => {
                cs_primary
                    .r1cs_instance_and_witness(&pp.r1cs_shape_primary, ck)
                    .map_err(|_e| NovaError::UnSat)?
            },
            None => {
                return Err(NovaError::MissingCK);
            },
        };
      

        // base case for the secondary
        let mut cs_secondary: SatisfyingAssignment<G2> = SatisfyingAssignment::new();
        let inputs_secondary: NovaAugmentedCircuitInputs<G1> = NovaAugmentedCircuitInputs::new(
          pp.digest,
          G2::Scalar::ZERO,
          z0_secondary.clone(),
          None,
          None,
          Some(u_primary.clone()),
          None,
        );
        let circuit_secondary: NovaAugmentedCircuit<G1, C2> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_secondary.clone(),
          Some(inputs_secondary),
          c_secondary.clone(),
          pp.ro_consts_circuit_secondary.clone(),
        );
        let _ = circuit_secondary.synthesize(&mut cs_secondary);
        let (u_secondary, w_secondary) = match pp.ck_secondary.as_ref() {
          Some(ck) => cs_secondary
              .r1cs_instance_and_witness(&pp.r1cs_shape_secondary, ck)
              .map_err(|_e| NovaError::UnSat)?,
          None => {
            return Err(NovaError::MissingCK); 
          }
        };
      

        // IVC proof for the primary circuit
        let l_w_primary = w_primary;
        let l_u_primary = u_primary;
        let r_W_primary =
          RelaxedR1CSWitness::from_r1cs_witness(&pp.r1cs_shape_primary, &l_w_primary);

        let r_U_primary = match pp.ck_primary.as_ref() {
            Some(ck) => {
                RelaxedR1CSInstance::from_r1cs_instance(
                    ck,
                    &pp.r1cs_shape_primary,
                    &l_u_primary,
                )
            },
            None => {
                return Err(NovaError::MissingCK); 
            },
        };
        

        // IVC proof of the secondary circuit
        let l_w_secondary = w_secondary;
        let l_u_secondary = u_secondary;
        let r_W_secondary = RelaxedR1CSWitness::<G2>::default(&pp.r1cs_shape_secondary);
        let r_U_secondary = match pp.ck_secondary.as_ref() {
          Some(ck) => RelaxedR1CSInstance::default(ck, &pp.r1cs_shape_secondary),
          None => return Err(NovaError::MissingCK),
        };
        

        // Outputs of the two circuits thus far
        let zi_primary = c_primary.output(&z0_primary);
        let zi_secondary = c_secondary.output(&z0_secondary);

        if zi_primary.len() != pp.F_arity_primary || zi_secondary.len() != pp.F_arity_secondary {
          return Err(NovaError::InvalidStepOutputLength);
        }

        Ok(Self {
          r_W_primary,
          r_U_primary,
          r_W_secondary,
          r_U_secondary,
          l_w_secondary,
          l_u_secondary,
          i: 1_usize,
          zi_primary,
          zi_secondary,
          _p_c1: Default::default(),
          _p_c2: Default::default(),
          program_counter: 0
        })
      }
      Some(r_snark) => {
        // fold the secondary circuit's instance

        let (nifs_secondary, (r_U_secondary, r_W_secondary)) = if let Some(ck) = pp.ck_secondary.as_ref() {
          NIFS::prove(
            ck,
            &pp.ro_consts_secondary,
            &scalar_as_base::<G1>(pp.digest),
            &pp.r1cs_shape_secondary,
            &r_snark.r_U_secondary,
            &r_snark.r_W_secondary,
            &r_snark.l_u_secondary,
            &r_snark.l_w_secondary,
          )?
        } else {
          return Err(NovaError::MissingCK);
        };

        let mut cs_primary: SatisfyingAssignment<G1> = SatisfyingAssignment::new();
        let inputs_primary: NovaAugmentedCircuitInputs<G2> = NovaAugmentedCircuitInputs::new(
          scalar_as_base::<G1>(pp.digest),
          G1::Scalar::from(r_snark.i as u64),
          z0_primary,
          Some(r_snark.zi_primary.clone()),
          Some(r_snark.r_U_secondary.clone()),
          Some(r_snark.l_u_secondary.clone()),
          Some(Commitment::<G2>::decompress(&nifs_secondary.comm_T)?),
        );

        let circuit_primary: NovaAugmentedCircuit<G2, C1> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_primary.clone(),
          Some(inputs_primary),
          c_primary.clone(),
          pp.ro_consts_circuit_primary.clone(),
        );
        let _ = circuit_primary.synthesize(&mut cs_primary);

        let (l_u_primary, l_w_primary) = if let Some(ck) = pp.ck_primary.as_ref() {
          cs_primary
              .r1cs_instance_and_witness(&pp.r1cs_shape_primary, ck)
              .map_err(|_e| NovaError::UnSat)?
        } else {
          return Err(NovaError::MissingCK);
        };
        

        let (nifs_primary, (r_U_primary, r_W_primary)) = if let Some(ck) = pp.ck_primary.as_ref() {
          NIFS::prove(
              ck,
              &pp.ro_consts_primary,
              &pp.digest,
              &pp.r1cs_shape_primary,
              &r_snark.r_U_primary,
              &r_snark.r_W_primary,
              &l_u_primary,
              &l_w_primary,
              )?
          } else {
            return Err(NovaError::MissingCK);
          };

        let mut cs_secondary: SatisfyingAssignment<G2> = SatisfyingAssignment::new();
        let inputs_secondary: NovaAugmentedCircuitInputs<G1> = NovaAugmentedCircuitInputs::new(
          pp.digest,
          G2::Scalar::from(r_snark.i as u64),
          z0_secondary,
          Some(r_snark.zi_secondary.clone()),
          Some(r_snark.r_U_primary.clone()),
          Some(l_u_primary),
          Some(Commitment::<G1>::decompress(&nifs_primary.comm_T)?),
        );

        let circuit_secondary: NovaAugmentedCircuit<G1, C2> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_secondary.clone(),
          Some(inputs_secondary),
          c_secondary.clone(),
          pp.ro_consts_circuit_secondary.clone(),
        );
        let _ = circuit_secondary.synthesize(&mut cs_secondary);

        let (l_u_secondary, l_w_secondary) = if let Some(ck) = pp.ck_secondary.as_ref() {
          cs_secondary
              .r1cs_instance_and_witness(&pp.r1cs_shape_secondary, ck)
              .map_err(|_e| NovaError::UnSat)?
        } else {
          return Err(NovaError::MissingCK);
        };

        // update the running instances and witnesses
        let zi_primary = c_primary.output(&r_snark.zi_primary);
        let zi_secondary = c_secondary.output(&r_snark.zi_secondary);

        Ok(Self {
          r_W_primary,
          r_U_primary,
          r_W_secondary,
          r_U_secondary,
          l_w_secondary,
          l_u_secondary,
          i: r_snark.i + 1,
          zi_primary,
          zi_secondary,
          _p_c1: Default::default(),
          _p_c2: Default::default(),
          program_counter: 0
        })
      }
    }
  }

  pub fn verify(
    &self,
    pp: &PublicParams<G1, G2, C1, C2>,
    num_steps: usize,
    z0_primary: Vec<G1::Scalar>,
    z0_secondary: Vec<G2::Scalar>,
  ) -> Result<(Vec<G1::Scalar>, Vec<G2::Scalar>), NovaError> {
    // number of steps cannot be zero
    if num_steps == 0 {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the provided proof has executed num_steps
    if self.i != num_steps {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the (relaxed) R1CS instances have two public outputs
    if self.l_u_secondary.X.len() != 2
      || self.r_U_primary.X.len() != 2
      || self.r_U_secondary.X.len() != 2
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the output hashes in R1CS instances point to the right running instances
    let (hash_primary, hash_secondary) = {
      let mut hasher = <G2 as Group>::RO::new(
        pp.ro_consts_secondary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_primary,
      );
      hasher.absorb(pp.digest);
      hasher.absorb(G1::Scalar::from(num_steps as u64));
      for e in &z0_primary {
        hasher.absorb(*e);
      }
      for e in &self.zi_primary {
        hasher.absorb(*e);
      }
      self.r_U_secondary.absorb_in_ro(&mut hasher);

      let mut hasher2 = <G1 as Group>::RO::new(
        pp.ro_consts_primary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_secondary,
      );
      hasher2.absorb(scalar_as_base::<G1>(pp.digest));
      hasher2.absorb(G2::Scalar::from(num_steps as u64));
      for e in &z0_secondary {
        hasher2.absorb(*e);
      }
      for e in &self.zi_secondary {
        hasher2.absorb(*e);
      }
      self.r_U_primary.absorb_in_ro(&mut hasher2);

      (
        hasher.squeeze(NUM_HASH_BITS),
        hasher2.squeeze(NUM_HASH_BITS),
      )
    };

    if hash_primary != self.l_u_secondary.X[0]
      || hash_secondary != scalar_as_base::<G2>(self.l_u_secondary.X[1])
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check the satisfiability of the provided instances
    let (res_r_primary, (res_r_secondary, res_l_secondary)) = rayon::join(
      || {
        pp.r1cs_shape_primary
          .is_sat_relaxed(&pp.ck_primary.as_ref().unwrap(), &self.r_U_primary, &self.r_W_primary)
      },
      || {
        rayon::join(
          || {
            pp.r1cs_shape_secondary.is_sat_relaxed(
              &pp.ck_secondary.as_ref().unwrap(),
              &self.r_U_secondary,
              &self.r_W_secondary,
            )
          },
          || {
            pp.r1cs_shape_secondary.is_sat(
              &pp.ck_secondary.as_ref().unwrap(),
              &self.l_u_secondary,
              &self.l_w_secondary,
            )
          },
        )
      },
    );

    // check the returned res objects
    res_r_primary?;
    res_r_secondary?;
    res_l_secondary?;

    Ok((self.zi_primary.clone(), self.zi_secondary.clone()))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  use ::bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};

  #[derive(Clone, Debug, Default)]
  struct CubicCircuit<F: PrimeField> {
    _p: PhantomData<F>,
  }

  impl<F> StepCircuit<F> for CubicCircuit<F>
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

    fn output(&self, z: &[F]) -> Vec<F> {
      vec![z[0] * z[0] * z[0] + z[0] + F::from(5u64)]
    }
  }

  /*
   SuperNova takes Ui a list of running instances. 
   One instance of will be a struct called RunningClaim.
  */
  pub struct RunningClaim<G1, G2, Ca, Cb>
  where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
    Ca: StepCircuit<G1::Scalar>,
    Cb: StepCircuit<G2::Scalar>,
  {
      _phantom: PhantomData<G1>,
      claim: Ca,
      program_counter: u64,
      largest: bool,
      params: PublicParams<G1, G2, Ca, Cb>,
  }
  

  impl<G1, G2, Ca, Cb> RunningClaim<G1, G2, Ca, Cb>
  where 
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
    Ca: StepCircuit<G1::Scalar>,
    Cb: StepCircuit<G2::Scalar>,
  {
      pub fn new(circuit_primary: Ca, circuit_secondary: Cb, is_largest: bool) -> Self {
          let claim = circuit_primary.clone();
          let program_counter = 0;
          let largest = is_largest;
  
          let pp = PublicParams::<
              G1,
              G2,
              Ca,
              Cb,
          >::setup(claim.clone(), circuit_secondary.clone(), is_largest);
  
          Self {
              _phantom: PhantomData, 
              claim,
              program_counter,
              largest,
              params: pp,
          }
      }

  }
  

  fn test_trivial_nivc_with<G1, G2>(num_steps: usize)
  where
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
  {

    let circuit_secondary = TrivialTestCircuit::default();

    // Structuring running claims     
    let test_circuit1 = CubicCircuit::default(); 
    let running_claim1 = RunningClaim::<G1, G2,
    CubicCircuit<<G1 as Group>::Scalar>,
    TrivialTestCircuit<<G2 as Group>::Scalar>>::new(test_circuit1, circuit_secondary.clone(), false);

    let test_circuit2 = TrivialTestCircuit::default();
    let running_claim2 = RunningClaim::<G1, G2,
    TrivialTestCircuit<<G1 as Group>::Scalar>,
    TrivialTestCircuit<<G2 as Group>::Scalar>>::new(test_circuit2, circuit_secondary.clone(), false);

    // The user creates a circuit like this as input to SuperNova.
    // The first circuit listed should be the largest. 
    let running_claims_tuple = (running_claim1, running_claim2);
    let num_steps = 3;

    // produce a recursive SNARK
    /*let mut recursive_snark: Option<
      NivcSNARK<
        G1,
        G2,
        CubicCircuit<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>,
      >,
    > = None;*/

    /*for i in 0..num_steps {
      let res = NivcSNARK::prove_step(
        &pp,
        recursive_snark,
        running_claims_tuple.0.claim.clone(),
        circuit_secondary.clone(),
        vec![<G1 as Group>::Scalar::ONE],
        vec![<G2 as Group>::Scalar::ZERO],
      );
      assert!(res.is_ok());
      let recursive_snark_unwrapped = res.unwrap();

      // verify the recursive snark at each step of recursion
      let res = recursive_snark_unwrapped.verify(
        &pp,
        i + 1,
        vec![<G1 as Group>::Scalar::ONE],
        vec![<G2 as Group>::Scalar::ZERO],
      );
      assert!(res.is_ok());

      // set the running variable for the next iteration
      recursive_snark = Some(recursive_snark_unwrapped);
    }*/

    //assert!(recursive_snark.is_some());
    
    /*let res = NivcSNARK::prove_step(
      &pp,
      recursive_snark,
      running_claims_tuple.0.claim.clone(),
      circuit_secondary.clone(),
      vec![<G1 as Group>::Scalar::ONE],
      vec![<G2 as Group>::Scalar::ZERO],
    );
    assert!(res.is_ok());
    let recursive_snark_unwrapped = res.unwrap();*/

    // verify the recursive snark at each step of recursion
    /*let res = recursive_snark_unwrapped.verify(
      &pp,
      num_steps + 1,
      vec![<G1 as Group>::Scalar::ONE],
      vec![<G2 as Group>::Scalar::ZERO],
    );
    assert!(res.is_ok());*/

    // set the running variable for the next iteration
    //recursive_snark = Some(recursive_snark_unwrapped);
    
    /*match res {
      Ok(val) => println!("Got an Ok result: {:?}", val),
      Err(err) => println!("Got an error: {:?}", err),
    }*/
    
  }

  #[test]
  fn test_trivial_nivc() {

      type G1 = pasta_curves::pallas::Point;
      type G2 = pasta_curves::vesta::Point;
    
      //Expirementing with selecting the running claims for nifs
      test_trivial_nivc_with::<G1, G2>(3);

  }
}
