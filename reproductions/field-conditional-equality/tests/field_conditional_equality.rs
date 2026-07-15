use ark_ff::{One, Zero};
use ark_groth16::{prepare_verifying_key, Groth16};
use ark_mnt4_298::{Fr, MNT4_298};
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    GR1CSVar,
};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
    SynthesisMode,
};

#[derive(Clone, Copy)]
struct AffectedCircuit {
    enabled: bool,
}

impl ConstraintSynthesizer<Fr> for AffectedCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let enabled = Boolean::new_input(cs, || Ok(self.enabled))?;
        FpVar::constant(Fr::one()).conditional_enforce_equal(&FpVar::constant(Fr::zero()), &enabled)
    }
}

#[derive(Clone, Copy)]
struct EqualConstantsControl {
    enabled: bool,
}

impl ConstraintSynthesizer<Fr> for EqualConstantsControl {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let enabled = Boolean::new_input(cs, || Ok(self.enabled))?;
        FpVar::constant(Fr::one()).conditional_enforce_equal(&FpVar::constant(Fr::one()), &enabled)
    }
}

#[derive(Clone, Copy)]
struct MixedVariableControl {
    enabled: bool,
}

impl ConstraintSynthesizer<Fr> for MixedVariableControl {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let enabled = Boolean::new_input(cs.clone(), || Ok(self.enabled))?;
        let zero = FpVar::new_witness(cs, || Ok(Fr::zero()))?;
        FpVar::constant(Fr::one()).conditional_enforce_equal(&zero, &enabled)
    }
}

#[derive(Clone, Copy)]
struct ContractOracle {
    enabled: bool,
}

impl ConstraintSynthesizer<Fr> for ContractOracle {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let enabled = Boolean::new_input(cs, || Ok(self.enabled))?;
        enabled.enforce_equal(&Boolean::FALSE)
    }
}

fn synthesize<C: ConstraintSynthesizer<Fr>>(
    circuit: C,
    mode: SynthesisMode,
) -> Result<ConstraintSystemRef<Fr>, SynthesisError> {
    let cs = ConstraintSystem::<Fr>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(mode);
    circuit.generate_constraints(cs.clone())?;
    cs.finalize();
    Ok(cs)
}

fn proving_cs<C: ConstraintSynthesizer<Fr>>(
    circuit: C,
) -> Result<ConstraintSystemRef<Fr>, SynthesisError> {
    synthesize(
        circuit,
        SynthesisMode::Prove {
            construct_matrices: true,
            generate_lc_assignments: false,
        },
    )
}

#[test]
fn unequal_constants_must_force_public_condition_false() -> Result<(), SynthesisError> {
    let enabled = true;
    let native_relation = !enabled || Fr::one() == Fr::zero();
    assert!(
        !native_relation,
        "the advertised native implication must be false"
    );

    let unconditional_result =
        FpVar::constant(Fr::one()).enforce_equal(&FpVar::constant(Fr::zero()));
    assert!(
        unconditional_result.is_ok(),
        "the affected unconditional API unexpectedly rejects unequal constants"
    );
    assert!(
        !FpVar::constant(Fr::one())
            .is_eq(&FpVar::constant(Fr::zero()))?
            .value()?,
        "the adjacent equality predicate must still detect unequal constants"
    );

    let affected_true = proving_cs(AffectedCircuit { enabled: true })?;
    let affected_false = proving_cs(AffectedCircuit { enabled: false })?;
    assert_eq!(
        affected_true.to_matrices()?,
        affected_false.to_matrices()?,
        "changing only the public Boolean assignment must preserve circuit shape"
    );
    assert_eq!(
        &affected_true.instance_assignment()?[1..],
        &[Fr::one()],
        "the failing assignment must expose enabled=true as its sole public input"
    );
    assert!(
        affected_true.is_satisfied()?,
        "the affected implementation should reproduce acceptance of the false implication"
    );
    assert!(
        affected_false.is_satisfied()?,
        "unequal constants must remain valid when equality is disabled"
    );

    let equal_constants = proving_cs(EqualConstantsControl { enabled: true })?;
    assert!(
        equal_constants.is_satisfied()?,
        "equal constants must remain valid when equality is enabled"
    );

    let mixed = proving_cs(MixedVariableControl { enabled: true })?;
    assert!(
        !mixed.is_satisfied()?,
        "the constrained constant/variable branch must reject the same false relation"
    );

    let oracle = proving_cs(ContractOracle { enabled: true })?;
    assert!(
        !oracle.is_satisfied()?,
        "the explicit condition-false oracle must reject enabled=true"
    );

    eprintln!(
        "affected: instances={}, witnesses={}, constraints={}",
        affected_true.num_instance_variables(),
        affected_true.num_witness_variables(),
        affected_true.num_constraints()
    );
    eprintln!(
        "controls: equal_satisfied={}, disabled_satisfied={}, mixed_satisfied={}, oracle_satisfied={}",
        equal_constants.is_satisfied()?,
        affected_false.is_satisfied()?,
        mixed.is_satisfied()?,
        oracle.is_satisfied()?
    );

    let mut rng = ark_std::test_rng();
    let proving_key = Groth16::<MNT4_298>::generate_random_parameters_with_reduction(
        AffectedCircuit { enabled: false },
        &mut rng,
    )?;
    let prepared_vk = prepare_verifying_key(&proving_key.vk);
    let proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        AffectedCircuit { enabled: true },
        &proving_key,
        &mut rng,
    )?;
    assert!(
        Groth16::<MNT4_298>::verify_proof(&prepared_vk, &proof, &[Fr::one()])?,
        "a proof for the false public implication must reproduce on the affected revision"
    );
    eprintln!("outer Groth16 proof verified for public enabled=true");

    Ok(())
}
