#![allow(non_snake_case)]

// basic circuit
// initialize 
// prove, verify

use std::marker::PhantomData;

use bellperson::{gadgets::{Assignment, boolean::Boolean}, LinearCombination, SynthesisError};
use ff::{PrimeField, Field};
use nova_snark::{traits::{circuit_supernova::{StepCircuit, TrivialTestCircuit}, Group}, supernova::{RunningClaim, PublicParams, gen_commitmentkey_by_r1cs, RecursiveSNARK}, compute_digest};
use nova_snark::gadgets::utils::{alloc_const,alloc_num_equals,conditionally_select,alloc_one,add_allocated_num,alloc_zero};
use bellperson::gadgets::{num::{AllocatedNum}, boolean::AllocatedBit};
use proptest::char::range;


#[derive(Clone, Debug, Default)]
struct AddCircuit<F:PrimeField> {
    _p: PhantomData<F>,
    circuit_index: usize,
    rom_size: usize
}


// circuit: y = x + 1
impl<F> AddCircuit<F>
where F:PrimeField
{
    fn new(circuit_index: usize, rom_size: usize) -> Self {
        AddCircuit { _p: PhantomData, circuit_index, rom_size}
    }
}

impl<F> StepCircuit<F> for AddCircuit<F> 
where F:PrimeField
{
    fn arity(&self) -> usize {
        1 + self.rom_size
    }

    fn synthesize<CS: bellperson::ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: &AllocatedNum<F>,
        z: &[AllocatedNum<F>],
      ) -> Result<(AllocatedNum<F>, Vec<AllocatedNum<F>>), bellperson::SynthesisError> {
        //constrain rom[pc] == self.circuit_index, where rom = z[1...]
        let circuit_index = alloc_const(
            cs.namespace(||"circuit index"),
            F::from(self.circuit_index as u64)
        )?;

        // sumpc = SUM( (i==pc) * rom[i])
        let zero: AllocatedNum<F> = alloc_zero(cs.namespace(|| "zero"))?;
        let matched_rom_vals = z[1..].iter().enumerate()
        .map(|(i, rom_val)|{
            let alloc_i = alloc_const( cs.namespace(|| format!("i: {}", i)), F::from(i as u64))?;
            let is_pc = alloc_num_equals(
                cs.namespace(|| format!("index {} equals circuit index", i)),
                &alloc_i,
                rom_val
            )?;
            conditionally_select( 
                cs.namespace(||format!("rom_values {} conditionally_select ", i)),
                rom_val,
                &zero,
                &Boolean::from(is_pc)
            )
        }).collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?;

        let sum_pc = matched_rom_vals.iter()
        .fold(LinearCombination::<F>::zero(), |acc_lc, rom_val|{
            acc_lc + rom_val.get_variable()
        });
        cs.enforce( 
            || "rom[pc] == self.circuit_index", 
            |lc| lc + &sum_pc, 
            |lc| lc + CS::one(), 
            |lc| lc + circuit_index.get_variable());

        //constrain F: y = x + 1
        let y = AllocatedNum::alloc(cs.namespace(|| "y") , || Ok(*z[0].get_value().get()? + F::from(1)))?;
        cs.enforce(|| "Add one circuit", 
        |lc| lc + CS::one(),
        |lc| lc + CS::one() + z[0].get_variable(),
        |lc| lc + y.get_variable());

        //constrain pc + 1
        let one = alloc_one(cs.namespace(|| "alloc one"))?;
        let pc_next = add_allocated_num(
          // pc = pc + 1
          cs.namespace(|| "pc = pc + 1".to_string()),
          pc,
          &one,
        )?;
        
        let mut z_next = vec![y];
        z_next.extend(z[1..].iter().cloned());
        Ok((pc_next, z_next))
    }

}


// circuit: y = x^2
#[derive(Clone, Debug, Default)]
struct Add2Circuit<F:PrimeField> {
    _p: PhantomData<F>,
    circuit_index: usize,
    rom_size: usize
}

impl<F> Add2Circuit<F>
where F:PrimeField
{
    fn new(circuit_index: usize, rom_size: usize) -> Self {
        Add2Circuit { _p: PhantomData, circuit_index, rom_size}
    }
}

impl<F> StepCircuit<F> for Add2Circuit<F> 
where F:PrimeField
{
    fn arity(&self) -> usize {
        1 + self.rom_size
    }

    fn synthesize<CS: bellperson::ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        pc: &AllocatedNum<F>,
        z: &[AllocatedNum<F>],
      ) -> Result<(AllocatedNum<F>, Vec<AllocatedNum<F>>), bellperson::SynthesisError> {
        //constrain rom[pc] == self.circuit_index, where rom = z[1...]
        let circuit_index = alloc_const(
            cs.namespace(||"circuit index"),
            F::from(self.circuit_index as u64)
        )?;

        // sumpc = SUM( (i==pc) * rom[i])
        let zero: AllocatedNum<F> = alloc_zero(cs.namespace(|| "zero"))?;
        let matched_rom_vals = z[1..].iter().enumerate()
        .map(|(i, rom_val)|{
            let alloc_i = alloc_const( cs.namespace(|| format!("i: {}", i)), F::from(i as u64))?;
            let is_pc = alloc_num_equals(
                cs.namespace(|| format!("index {} equals circuit index", i)),
                &alloc_i,
                rom_val
            )?;
            conditionally_select( 
                cs.namespace(||format!("rom_values {} conditionally_select ", i)),
                rom_val,
                &zero,
                &Boolean::from(is_pc)
            )
        }).collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?;

        let sum_pc = matched_rom_vals.iter()
        .fold(LinearCombination::<F>::zero(), |acc_lc, rom_val|{
            acc_lc + rom_val.get_variable()
        });
        cs.enforce( 
            || "rom[pc] == self.circuit_index", 
            |lc| lc + &sum_pc, 
            |lc| lc + CS::one(), 
            |lc| lc + circuit_index.get_variable());

        //constrain F： y = x^2
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(*z[0].get_value().get()?))?;
        let y_square = z[0].square(cs.namespace(|| " y^2"))?;
        cs.enforce(|| "Add one circuit", 
        |lc| lc + z[0].get_variable(),
        |lc| lc + z[0].get_variable(),
        |lc| lc + y_square.get_variable()
        );

        //constrain pc + 1
        let one = alloc_one(cs.namespace(|| "alloc one"))?;
        let pc_next = add_allocated_num(
          // pc = pc + 1
          cs.namespace(|| "pc = pc + 1".to_string()),
          pc,
          &one,
        )?;
        
        let mut z_next = vec![y_square];
        z_next.extend(z[1..].iter().cloned());
        Ok((pc_next, z_next))
    }

}


fn main() {
    type G1 = pasta_curves::pallas::Point;
    type G2 = pasta_curves::vesta::Point;

    const OPCODE_0:usize = 0;  
    const OPCODE_1:usize = 1;  
    let rom = [OPCODE_0,OPCODE_1,OPCODE_1];
    let num_augmented_circuit = 2;
    let rom_size = rom.len();


    //create 2 F circuit
    let circuit_1 = AddCircuit::new(OPCODE_0, rom_size);
    let circuit_2 = Add2Circuit::new(OPCODE_1, rom_size);

    let circuit_secondary = TrivialTestCircuit::new(rom_size);

    //initialize 2 running instances (including create pp)
    let mut running_claim_1 = RunningClaim::<
        G1,
        G2,
        AddCircuit<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>
        >::new(
            OPCODE_0, 
            circuit_1, 
            circuit_secondary.clone(), 
            num_augmented_circuit);
    let mut running_claim_2 = RunningClaim::<
        G1,
        G2,
        Add2Circuit<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>
        >::new(
            OPCODE_1, 
            circuit_2, 
            circuit_secondary, 
            num_augmented_circuit);
    
    //**setup
    // 1.set every circuit's ck to the circuit with the most constrains
    // 2.update pp.digest

    let params = vec![running_claim_1.get_publicparams(), running_claim_2.get_publicparams()];
    let (max_index, _) = params.iter().enumerate()
    .map(|(i, claim)| -> (usize, usize) {
        println!("constrains ============> {}, {:?}", i, claim.num_constraints());
        (i, claim.num_constraints().0)
    })
    .max_by(|(_,size_1),(_,size_2)| {
       size_1.cmp(size_2)
    }).unwrap();

    let (primary_shape,second_shape) =  params[max_index].get_r1cs_shape();

    let ck_primary =  gen_commitmentkey_by_r1cs(primary_shape);
    let ck_sencodary = gen_commitmentkey_by_r1cs(second_shape);
    running_claim_1.set_commitmentkey(ck_primary.clone(), ck_sencodary.clone());
    running_claim_2.set_commitmentkey(ck_primary, ck_sencodary);

    let digest = compute_digest::<G1, PublicParams<G1, G2>>(&[
        running_claim_1.get_publicparams(),
        running_claim_2.get_publicparams(),
      ]);

    //create base super nova_snark
    let mut z0_primary = vec![<G1 as Group>::Scalar::ONE];
    z0_primary.extend(rom.iter().map(
        |op_code| <G1 as Group>::Scalar::from(*op_code as u64)
    ));
    let mut z0_secondary = vec![<G2 as Group>::Scalar::ONE];
    z0_secondary.extend(
        rom
          .iter()
          .map(|opcode| <G2 as Group>::Scalar::from(*opcode as u64)),
    );
    
    let inital_pc = <G1 as Group>::Scalar::from(0);
    let mut recursive_snark = RecursiveSNARK::iter_base_step(
        &running_claim_1,
        digest,
        inital_pc,
        OPCODE_0,
        num_augmented_circuit,
        &z0_primary,
        &z0_secondary,
        ).unwrap();

    // println!("recursive snark===========> {:?}", recursive_snark);
    
    for _ in 1..rom_size{
        let pc = recursive_snark.get_program_counter();
        let augument_circuit_index = rom[u32::from_le_bytes(
            pc.to_repr().as_ref()[0..4].try_into().unwrap()
        ) as usize];

        match augument_circuit_index {
            OPCODE_0 => {
                recursive_snark
                .prove_step(&running_claim_1, &z0_primary, &z0_secondary)
                .unwrap();
                recursive_snark
                .verify(&running_claim_1, &z0_primary, &z0_secondary)
                .unwrap();
            },
            OPCODE_1 => {
                recursive_snark
                .prove_step(&running_claim_2, &z0_primary, &z0_secondary)
                .unwrap();
                recursive_snark
                .verify(&running_claim_2, &z0_primary, &z0_secondary)
                .unwrap();
            },
            _ => unimplemented!()
        }
    }

    let RecursiveSNARK {
        zi_primary,
        ..
    } = recursive_snark;
    println!(" zi_primary is ===========> {:?}", zi_primary);
}