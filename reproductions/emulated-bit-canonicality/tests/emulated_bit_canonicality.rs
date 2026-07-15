use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_groth16::{prepare_verifying_key, Groth16};
use ark_mnt4_298::{Fq as TargetField, MNT4_298};
use ark_mnt6_298::Fq as ConstraintField;
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    convert::ToBitsGadget,
    eq::EqGadget,
    fields::{
        emulated_fp::{params::OptimizationType, AllocatedEmulatedFpVar},
        fp::FpVar,
    },
    GR1CSVar,
};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
    SynthesisMode,
};
use std::marker::PhantomData;

type EmulatedVar = AllocatedEmulatedFpVar<TargetField, ConstraintField>;

#[derive(Clone)]
struct HelperCircuit {
    value: TargetField,
    claimed_bits: Vec<bool>,
    assign_modulus: bool,
}

struct HelperEvidence {
    limb_indices: Vec<usize>,
    bit_indices: Vec<usize>,
}

impl ConstraintSynthesizer<ConstraintField> for HelperCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintField>,
    ) -> Result<(), SynthesisError> {
        generate_helper_relation(cs, self.value, &self.claimed_bits, self.assign_modulus)
            .map(|_| ())
    }
}

fn canonical_bits(value: TargetField) -> Vec<bool> {
    let mut bits = value.into_bigint().to_bits_le();
    bits.truncate(TargetField::MODULUS_BIT_SIZE as usize);
    bits
}

fn modulus_bits() -> Vec<bool> {
    let mut bits = TargetField::MODULUS.to_bits_le();
    bits.truncate(TargetField::MODULUS_BIT_SIZE as usize);
    bits
}

fn modulus_limbs() -> Vec<ConstraintField> {
    EmulatedVar::get_limbs_representations_from_big_integer(
        &TargetField::MODULUS,
        OptimizationType::Constraints,
    )
    .expect("the supported field pair must have an emulation configuration")
}

fn witness_index(variable: ark_relations::gr1cs::Variable) -> usize {
    variable
        .index()
        .expect("the public helper must allocate a witness variable")
}

fn generate_helper_relation(
    cs: ConstraintSystemRef<ConstraintField>,
    value: TargetField,
    claimed_bits: &[bool],
    assign_modulus: bool,
) -> Result<HelperEvidence, SynthesisError> {
    assert_eq!(claimed_bits.len(), TargetField::MODULUS_BIT_SIZE as usize);

    let (allocated, returned_bits) =
        EmulatedVar::new_witness_with_le_bits(cs.clone(), || Ok(value))?;
    let claimed_bits = claimed_bits
        .iter()
        .map(|bit| Boolean::new_input(cs.clone(), || Ok(*bit)))
        .collect::<Result<Vec<_>, _>>()?;
    returned_bits
        .as_slice()
        .enforce_equal(claimed_bits.as_slice())?;

    let limb_indices = allocated
        .limbs
        .iter()
        .map(|limb| match limb {
            FpVar::Var(variable) => witness_index(variable.variable),
            FpVar::Constant(_) => panic!("witness helper returned a constant limb"),
        })
        .collect::<Vec<_>>();
    let bit_indices = returned_bits
        .iter()
        .map(|bit| witness_index(bit.variable()))
        .collect::<Vec<_>>();

    if assign_modulus && !cs.is_in_setup_mode() {
        let limbs = modulus_limbs();
        let bits = modulus_bits();
        assert_eq!(limbs.len(), limb_indices.len());
        assert_eq!(bits.len(), bit_indices.len());

        // The helper closure models honest witness generation, but a proof producer
        // supplies these witness assignments directly and is not bound to that closure.
        let ConstraintSystemRef::CS(inner) = &cs else {
            return Err(SynthesisError::MissingCS);
        };
        let mut inner = inner.borrow_mut();
        for (index, limb) in limb_indices.iter().zip(limbs) {
            inner.assignments.witness_assignment[*index] = limb;
        }
        for (index, bit) in bit_indices.iter().zip(bits) {
            inner.assignments.witness_assignment[*index] = if bit {
                ConstraintField::one()
            } else {
                ConstraintField::zero()
            };
        }
    }

    Ok(HelperEvidence {
        limb_indices,
        bit_indices,
    })
}

fn synthesize_helper(
    circuit: HelperCircuit,
) -> Result<(ConstraintSystemRef<ConstraintField>, HelperEvidence), SynthesisError> {
    let cs = ConstraintSystem::<ConstraintField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
        generate_lc_assignments: false,
    });
    let evidence = generate_helper_relation(
        cs.clone(),
        circuit.value,
        &circuit.claimed_bits,
        circuit.assign_modulus,
    )?;
    cs.finalize();
    Ok((cs, evidence))
}

fn setup_cs(
    circuit: HelperCircuit,
) -> Result<ConstraintSystemRef<ConstraintField>, SynthesisError> {
    let cs = ConstraintSystem::<ConstraintField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Setup);
    circuit.generate_constraints(cs.clone())?;
    cs.finalize();
    Ok(cs)
}

fn assigned_limbs(
    cs: &ConstraintSystemRef<ConstraintField>,
    indices: &[usize],
) -> Result<Vec<ConstraintField>, SynthesisError> {
    let witness = cs.witness_assignment()?;
    Ok(indices.iter().map(|index| witness[*index]).collect())
}

fn assigned_bits(
    cs: &ConstraintSystemRef<ConstraintField>,
    indices: &[usize],
) -> Result<Vec<bool>, SynthesisError> {
    let witness = cs.witness_assignment()?;
    Ok(indices
        .iter()
        .map(|index| {
            let value = witness[*index];
            assert!(value.is_zero() || value.is_one());
            value.is_one()
        })
        .collect())
}

fn synthesize_direct_bound(
    values: &[bool],
) -> Result<ConstraintSystemRef<ConstraintField>, SynthesisError> {
    let cs = ConstraintSystem::<ConstraintField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
        generate_lc_assignments: false,
    });
    let bits = values
        .iter()
        .map(|bit| Boolean::new_witness(cs.clone(), || Ok(*bit)))
        .collect::<Result<Vec<_>, _>>()?;
    let mut upper_bound = TargetField::characteristic().to_vec();
    upper_bound[0] -= 1;
    let run = Boolean::<ConstraintField>::enforce_smaller_or_equal_than_le(&bits, upper_bound)?;
    assert!(run.is_empty());
    cs.finalize();
    Ok(cs)
}

fn synthesize_safe_conversion(
) -> Result<(ConstraintSystemRef<ConstraintField>, TargetField, Vec<bool>), SynthesisError> {
    let cs = ConstraintSystem::<ConstraintField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Prove {
        construct_matrices: true,
        generate_lc_assignments: false,
    });
    let limbs = modulus_limbs()
        .into_iter()
        .map(|limb| FpVar::new_witness(cs.clone(), || Ok(limb)))
        .collect::<Result<Vec<_>, _>>()?;
    let raw = EmulatedVar {
        cs: cs.clone(),
        limbs,
        num_of_additions_over_normal_form: ConstraintField::one(),
        is_in_the_normal_form: false,
        target_phantom: PhantomData,
    };
    let semantic_value = raw.value()?;
    let safe_bits = raw.to_bits_le()?;
    let safe_values = safe_bits
        .iter()
        .map(GR1CSVar::value)
        .collect::<Result<Vec<_>, _>>()?;
    safe_bits
        .as_slice()
        .enforce_equal(vec![Boolean::FALSE; safe_bits.len()].as_slice())?;
    cs.finalize();
    Ok((cs, semantic_value, safe_values))
}

fn public_inputs(bits: &[bool]) -> Vec<ConstraintField> {
    bits.iter()
        .map(|bit| {
            if *bit {
                ConstraintField::one()
            } else {
                ConstraintField::zero()
            }
        })
        .collect()
}

#[test]
fn witness_helper_must_not_expose_modulus_as_zero_bits() -> Result<(), SynthesisError> {
    let zero_bits = canonical_bits(TargetField::zero());
    let one_bits = canonical_bits(TargetField::one());
    let p_minus_one_bits = canonical_bits(-TargetField::one());
    let p_bits = modulus_bits();

    let canonical_zero = HelperCircuit {
        value: TargetField::zero(),
        claimed_bits: zero_bits.clone(),
        assign_modulus: false,
    };
    let canonical_one = HelperCircuit {
        value: TargetField::one(),
        claimed_bits: one_bits.clone(),
        assign_modulus: false,
    };
    let modulus_alias = HelperCircuit {
        value: TargetField::zero(),
        claimed_bits: p_bits.clone(),
        assign_modulus: true,
    };

    let victim_setup = setup_cs(canonical_zero.clone())?;
    let malicious_setup = setup_cs(modulus_alias.clone())?;
    assert_eq!(
        victim_setup.to_matrices()?,
        malicious_setup.to_matrices()?,
        "honest and adversarial assignments must use the same public-helper relation"
    );

    let (zero_cs, zero_evidence) = synthesize_helper(canonical_zero.clone())?;
    assert!(zero_cs.is_satisfied()?);
    assert_eq!(
        assigned_bits(&zero_cs, &zero_evidence.bit_indices)?,
        zero_bits
    );

    let (one_cs, one_evidence) = synthesize_helper(canonical_one.clone())?;
    assert!(one_cs.is_satisfied()?);
    assert_eq!(assigned_bits(&one_cs, &one_evidence.bit_indices)?, one_bits);

    let (malicious_cs, malicious_evidence) = synthesize_helper(modulus_alias.clone())?;
    let malicious_limbs = assigned_limbs(&malicious_cs, &malicious_evidence.limb_indices)?;
    let malicious_bits = assigned_bits(&malicious_cs, &malicious_evidence.bit_indices)?;
    assert_eq!(malicious_limbs, modulus_limbs());
    assert_eq!(malicious_bits, p_bits);
    assert_eq!(
        <TargetField as PrimeField>::BigInt::from_bits_le(&malicious_bits),
        TargetField::MODULUS,
        "the returned helper bits must encode the integer p"
    );
    assert_eq!(
        EmulatedVar::limbs_to_value(malicious_limbs, OptimizationType::Constraints),
        TargetField::zero(),
        "the same assigned limbs decode modulo p as semantic zero"
    );
    assert!(
        malicious_cs.is_satisfied()?,
        "the modulus alias currently satisfies the full public-helper relation"
    );

    let strict_valid = synthesize_direct_bound(&p_minus_one_bits)?;
    assert!(
        strict_valid.is_satisfied()?,
        "the direct p-1 bound must preserve its upper valid endpoint"
    );
    let strict_modulus = synthesize_direct_bound(&p_bits)?;
    assert!(
        !strict_modulus.is_satisfied()?,
        "the direct p-1 bound must reject the integer p"
    );

    let (safe_cs, safe_semantic_value, safe_bits) = synthesize_safe_conversion()?;
    assert_eq!(safe_semantic_value, TargetField::zero());
    assert_eq!(&safe_bits[..zero_bits.len()], zero_bits.as_slice());
    assert!(
        safe_bits.iter().all(|bit| !bit),
        "the safe conversion may pad to the BigInt width, but every bit must encode zero"
    );
    assert!(
        safe_cs.is_satisfied()?,
        "to_bits_le must reduce the raw modulus limbs to canonical zero"
    );

    let mut rng = ark_std::test_rng();
    let proving_key = Groth16::<MNT4_298>::generate_random_parameters_with_reduction(
        canonical_zero.clone(),
        &mut rng,
    )?;
    let prepared_vk = prepare_verifying_key(&proving_key.vk);

    let zero_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        canonical_zero,
        &proving_key,
        &mut rng,
    )?;
    assert!(Groth16::<MNT4_298>::verify_proof(
        &prepared_vk,
        &zero_proof,
        &public_inputs(&zero_bits)
    )?);

    let one_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        canonical_one,
        &proving_key,
        &mut rng,
    )?;
    assert!(Groth16::<MNT4_298>::verify_proof(
        &prepared_vk,
        &one_proof,
        &public_inputs(&one_bits)
    )?);

    let alias_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        modulus_alias,
        &proving_key,
        &mut rng,
    )?;
    assert!(
        Groth16::<MNT4_298>::verify_proof(&prepared_vk, &alias_proof, &public_inputs(&p_bits))?,
        "a key generated from the supported helper verifies a proof exposing p as zero's bits"
    );

    println!(
        "constraints={} witness_variables={} public_bits={} semantic_value=zero raw_encoding=modulus proof_verified=true",
        malicious_cs.num_constraints(),
        malicious_cs.num_witness_variables(),
        p_bits.len()
    );
    Ok(())
}
