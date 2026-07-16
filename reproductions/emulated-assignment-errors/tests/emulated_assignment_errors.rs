use ark_bls12_381::Fr as TargetField;
use ark_ff::{One, Zero};
use ark_groth16::{prepare_verifying_key, Groth16};
use ark_mnt4_298::{Fr as ConstraintField, MNT4_298};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    eq::EqGadget,
    fields::{
        emulated_fp::{AllocatedEmulatedFpVar, EmulatedFpVar},
        fp::FpVar,
        FieldVar,
    },
    GR1CSVar,
};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
    SynthesisMode,
};

#[derive(Clone, Copy)]
struct EmulatedEqualityCircuit {
    value: Option<TargetField>,
    expected: TargetField,
}

impl ConstraintSynthesizer<ConstraintField> for EmulatedEqualityCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintField>,
    ) -> Result<(), SynthesisError> {
        let value = EmulatedFpVar::<TargetField, ConstraintField>::new_witness(cs, || {
            self.value.ok_or(SynthesisError::AssignmentMissing)
        })?;
        value.enforce_equal(&EmulatedFpVar::constant(self.expected))
    }
}

#[derive(Clone, Copy)]
struct NativeZeroCircuit {
    value: Option<ConstraintField>,
}

impl ConstraintSynthesizer<ConstraintField> for NativeZeroCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintField>,
    ) -> Result<(), SynthesisError> {
        let value = FpVar::<ConstraintField>::new_witness(cs, || {
            self.value.ok_or(SynthesisError::AssignmentMissing)
        })?;
        value.enforce_equal(&FpVar::constant(ConstraintField::zero()))
    }
}

fn synthesize<C: ConstraintSynthesizer<ConstraintField>>(
    circuit: C,
    mode: SynthesisMode,
) -> Result<ConstraintSystemRef<ConstraintField>, SynthesisError> {
    let cs = ConstraintSystem::<ConstraintField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(mode);
    circuit.generate_constraints(cs.clone())?;
    cs.finalize();
    Ok(cs)
}

fn proving_cs<C: ConstraintSynthesizer<ConstraintField>>(
    circuit: C,
) -> Result<ConstraintSystemRef<ConstraintField>, SynthesisError> {
    synthesize(
        circuit,
        SynthesisMode::Prove {
            construct_matrices: true,
            generate_lc_assignments: false,
        },
    )
}

fn missing_emulated(expected: TargetField) -> EmulatedEqualityCircuit {
    EmulatedEqualityCircuit {
        value: None,
        expected,
    }
}

#[test]
fn proving_mode_must_propagate_emulated_allocation_errors() -> Result<(), SynthesisError> {
    let direct_cs = ConstraintSystem::<ConstraintField>::new_ref();
    let affected =
        EmulatedFpVar::<TargetField, ConstraintField>::new_witness(direct_cs.clone(), || {
            Err::<TargetField, _>(SynthesisError::AssignmentMissing)
        });
    assert!(
        affected.is_ok(),
        "the affected revision should reproduce silent replacement of AssignmentMissing"
    );
    let affected = affected?;
    assert_eq!(
        affected.value()?,
        TargetField::zero(),
        "the swallowed error must become a proof-relevant zero assignment"
    );
    affected.enforce_equal(&EmulatedFpVar::constant(TargetField::zero()))?;
    assert!(
        direct_cs.is_satisfied()?,
        "the substituted zero must satisfy a relation that permits zero"
    );

    let supported_path_cs = ConstraintSystem::<ConstraintField>::new_ref();
    let supported_path =
        AllocatedEmulatedFpVar::<TargetField, ConstraintField>::new_witness_with_le_bits(
            supported_path_cs.clone(),
            || Err::<TargetField, _>(SynthesisError::AssignmentMissing),
        );
    assert!(
        supported_path.is_ok(),
        "the downstream new_witness_with_le_bits path must reach the same owner"
    );
    let (supported_value, supported_bits) = supported_path?;
    assert_eq!(supported_value.value()?, TargetField::zero());
    assert!(supported_bits.iter().all(|bit| !bit.value().unwrap()));
    assert!(supported_path_cs.is_satisfied()?);

    let non_assignment_cs = ConstraintSystem::<ConstraintField>::new_ref();
    let non_assignment_error =
        EmulatedFpVar::<TargetField, ConstraintField>::new_witness(non_assignment_cs, || {
            Err::<TargetField, _>(SynthesisError::DivisionByZero)
        });
    assert!(
        non_assignment_error.is_ok(),
        "the owner catches every synthesis error, not only AssignmentMissing"
    );
    assert_eq!(non_assignment_error?.value()?, TargetField::zero());

    let native_assignment_cs = ConstraintSystem::<ConstraintField>::new_ref();
    let native_assignment = FpVar::<ConstraintField>::new_witness(native_assignment_cs, || {
        Err::<ConstraintField, _>(SynthesisError::AssignmentMissing)
    });
    assert!(matches!(
        native_assignment,
        Err(SynthesisError::AssignmentMissing)
    ));

    let native_division_cs = ConstraintSystem::<ConstraintField>::new_ref();
    let native_division = FpVar::<ConstraintField>::new_witness(native_division_cs, || {
        Err::<ConstraintField, _>(SynthesisError::DivisionByZero)
    });
    assert!(matches!(
        native_division,
        Err(SynthesisError::DivisionByZero)
    ));

    let no_cs = EmulatedFpVar::<TargetField, ConstraintField>::new_variable(
        ConstraintSystemRef::None,
        || Err::<TargetField, _>(SynthesisError::AssignmentMissing),
        AllocationMode::Witness,
    );
    assert!(matches!(no_cs, Err(SynthesisError::AssignmentMissing)));

    let setup_missing = synthesize(missing_emulated(TargetField::zero()), SynthesisMode::Setup)?;
    let setup_zero = synthesize(
        EmulatedEqualityCircuit {
            value: Some(TargetField::zero()),
            expected: TargetField::zero(),
        },
        SynthesisMode::Setup,
    )?;
    assert_eq!(
        setup_missing.to_matrices()?,
        setup_zero.to_matrices()?,
        "setup must remain assignment-independent"
    );

    let missing_zero = proving_cs(missing_emulated(TargetField::zero()))?;
    let valid_zero = proving_cs(EmulatedEqualityCircuit {
        value: Some(TargetField::zero()),
        expected: TargetField::zero(),
    })?;
    assert!(missing_zero.is_satisfied()?);
    assert!(valid_zero.is_satisfied()?);
    assert_eq!(
        missing_zero.to_matrices()?,
        valid_zero.to_matrices()?,
        "changing only the witness callback outcome must preserve circuit shape"
    );

    let missing_one = proving_cs(missing_emulated(TargetField::one()))?;
    assert!(
        !missing_one.is_satisfied()?,
        "the zero substitution must not bypass constraints that exclude zero"
    );

    let mut rng = ark_std::test_rng();
    let emulated_pk = Groth16::<MNT4_298>::generate_random_parameters_with_reduction(
        missing_emulated(TargetField::zero()),
        &mut rng,
    )?;
    let emulated_pvk = prepare_verifying_key(&emulated_pk.vk);

    let missing_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        missing_emulated(TargetField::zero()),
        &emulated_pk,
        &mut rng,
    )?;
    assert!(
        Groth16::<MNT4_298>::verify_proof(&emulated_pvk, &missing_proof, &[])?,
        "a proof must reproduce after AssignmentMissing is silently replaced with zero"
    );

    let valid_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        EmulatedEqualityCircuit {
            value: Some(TargetField::zero()),
            expected: TargetField::zero(),
        },
        &emulated_pk,
        &mut rng,
    )?;
    assert!(Groth16::<MNT4_298>::verify_proof(
        &emulated_pvk,
        &valid_proof,
        &[]
    )?);

    let native_pk = Groth16::<MNT4_298>::generate_random_parameters_with_reduction(
        NativeZeroCircuit { value: None },
        &mut rng,
    )?;
    let native_missing = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        NativeZeroCircuit { value: None },
        &native_pk,
        &mut rng,
    );
    assert!(matches!(
        native_missing,
        Err(SynthesisError::AssignmentMissing)
    ));

    eprintln!(
        "affected_revision=45e4e2697626a9f9481fe57e70ed29c687194102 relation_revision=845ce9d50bbe535792f04b44db78b009ee402ed7"
    );
    eprintln!(
        "affected_assignment=zero missing_satisfied={} excluded_zero_satisfied={} missing_proof_verified=true valid_proof_verified=true",
        missing_zero.is_satisfied()?,
        missing_one.is_satisfied()?
    );
    eprintln!(
        "controls=native_errors_propagate,no_cs_error_propagates,setup_shape_matches,valid_zero_verifies"
    );

    Ok(())
}
