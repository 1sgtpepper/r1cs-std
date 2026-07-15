use ark_groth16::{prepare_verifying_key, Groth16};
use ark_mnt4_298::MNT4_298;
use ark_mnt6_298::Fq;
use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
    SynthesisMode,
};

const BASE: u64 = 0;
const FALSE_BASE: u64 = 1;
const SQUARE: u64 = 0;
const FALSE_SQUARE: u64 = 1;

#[derive(Clone, Copy)]
struct ConstantBaseCircuit {
    claimed_square: Fq,
}

impl ConstraintSynthesizer<Fq> for ConstantBaseCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let claimed_square = FpVar::new_input(cs, || Ok(self.claimed_square))?;
        FpVar::Constant(Fq::from(BASE)).square_equals(&claimed_square)
    }
}

#[derive(Clone, Copy)]
struct RawConstantBaseCircuit {
    claimed_square: Fq,
    synthetic_base: Fq,
}

impl ConstraintSynthesizer<Fq> for RawConstantBaseCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let claimed_square = FpVar::new_input(cs.clone(), || Ok(self.claimed_square))?;
        let synthetic_base = FpVar::new_witness(cs, || Ok(self.synthetic_base))?;
        synthetic_base.square_equals(&claimed_square)
    }
}

#[derive(Clone, Copy)]
struct ConstantPreservingBaseCircuit {
    claimed_square: Fq,
}

impl ConstraintSynthesizer<Fq> for ConstantPreservingBaseCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let claimed_square = FpVar::new_input(cs, || Ok(self.claimed_square))?;
        let expected_square = FpVar::Constant(Fq::from(BASE) * Fq::from(BASE));
        expected_square.enforce_equal(&claimed_square)
    }
}

#[derive(Clone, Copy)]
struct ConstantResultCircuit {
    base: Fq,
}

impl ConstraintSynthesizer<Fq> for ConstantResultCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let base = FpVar::new_input(cs, || Ok(self.base))?;
        base.square_equals(&FpVar::Constant(Fq::from(SQUARE)))
    }
}

#[derive(Clone, Copy)]
struct RawConstantResultCircuit {
    base: Fq,
    synthetic_square: Fq,
}

impl ConstraintSynthesizer<Fq> for RawConstantResultCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let base = FpVar::new_input(cs.clone(), || Ok(self.base))?;
        let synthetic_square = FpVar::new_witness(cs, || Ok(self.synthetic_square))?;
        base.square_equals(&synthetic_square)
    }
}

#[derive(Clone, Copy)]
struct ConstantPreservingResultCircuit {
    base: Fq,
}

impl ConstraintSynthesizer<Fq> for ConstantPreservingResultCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let base = FpVar::new_input(cs, || Ok(self.base))?;
        base.square()?
            .enforce_equal(&FpVar::Constant(Fq::from(SQUARE)))
    }
}

fn synthesize<C: ConstraintSynthesizer<Fq>>(
    circuit: C,
    mode: SynthesisMode,
) -> Result<ConstraintSystemRef<Fq>, SynthesisError> {
    let cs = ConstraintSystem::<Fq>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(mode);
    circuit.generate_constraints(cs.clone())?;
    cs.finalize();
    Ok(cs)
}

fn setup_matrices<C: ConstraintSynthesizer<Fq>>(
    circuit: C,
) -> Result<ConstraintSystemRef<Fq>, SynthesisError> {
    synthesize(circuit, SynthesisMode::Setup)
}

fn proving_cs<C: ConstraintSynthesizer<Fq>>(
    circuit: C,
) -> Result<ConstraintSystemRef<Fq>, SynthesisError> {
    synthesize(
        circuit,
        SynthesisMode::Prove {
            construct_matrices: true,
            generate_lc_assignments: false,
        },
    )
}

fn assert_same_matrices(
    victim: ConstraintSystemRef<Fq>,
    malicious: ConstraintSystemRef<Fq>,
) -> Result<(), SynthesisError> {
    assert_eq!(
        victim.num_instance_variables(),
        malicious.num_instance_variables()
    );
    assert_eq!(
        victim.num_witness_variables(),
        malicious.num_witness_variables()
    );
    assert_eq!(victim.num_constraints(), malicious.num_constraints());
    assert_eq!(
        victim.to_matrices()?,
        malicious.to_matrices()?,
        "victim and malicious synthesis must define identical matrices"
    );
    Ok(())
}

#[test]
fn mixed_constant_square_relations_accept_false_public_claims() -> Result<(), SynthesisError> {
    let base = Fq::from(BASE);
    let false_base = Fq::from(FALSE_BASE);
    let square = Fq::from(SQUARE);
    let false_square = Fq::from(FALSE_SQUARE);

    assert_ne!(
        base * base,
        false_square,
        "the primary public square claim must be false natively"
    );
    assert_ne!(
        false_base * false_base,
        square,
        "the opposite mixed-branch claim must be false natively"
    );

    assert_same_matrices(
        setup_matrices(ConstantBaseCircuit {
            claimed_square: square,
        })?,
        setup_matrices(RawConstantBaseCircuit {
            claimed_square: false_square,
            synthetic_base: false_base,
        })?,
    )?;

    let honest_false_base_cs = proving_cs(ConstantBaseCircuit {
        claimed_square: false_square,
    })?;
    assert_eq!(
        &honest_false_base_cs.instance_assignment()?[1..],
        &[false_square]
    );
    assert_eq!(honest_false_base_cs.witness_assignment()?, vec![base]);
    assert!(
        !honest_false_base_cs.is_satisfied()?,
        "the honest synthetic assignment must reject the false claim"
    );

    {
        let mut state = honest_false_base_cs.borrow_mut().unwrap();
        state.assignments.witness_assignment[0] = false_base;
    }
    assert!(
        honest_false_base_cs.is_satisfied()?,
        "changing only the synthetic advice must satisfy the false claim"
    );

    let malicious_base_cs = proving_cs(RawConstantBaseCircuit {
        claimed_square: false_square,
        synthetic_base: false_base,
    })?;
    assert_eq!(
        &malicious_base_cs.instance_assignment()?[1..],
        &[false_square]
    );
    assert_eq!(malicious_base_cs.witness_assignment()?, vec![false_base]);
    assert!(
        malicious_base_cs.is_satisfied()?,
        "the false public relation must satisfy the complete weakened system"
    );

    let all_variable_negative = proving_cs(RawConstantBaseCircuit {
        claimed_square: false_square,
        synthetic_base: base,
    })?;
    assert!(
        !all_variable_negative.is_satisfied()?,
        "the all-variable relation must reject the same claim when the base stays bound"
    );

    let constant_preserving_negative = proving_cs(ConstantPreservingBaseCircuit {
        claimed_square: false_square,
    })?;
    assert!(
        !constant_preserving_negative.is_satisfied()?,
        "a constant-preserving relation must reject the false square"
    );

    let valid_base_cs = proving_cs(ConstantBaseCircuit {
        claimed_square: square,
    })?;
    assert!(
        valid_base_cs.is_satisfied()?,
        "the valid constant-base relation must remain accepted"
    );

    assert_same_matrices(
        setup_matrices(ConstantResultCircuit { base })?,
        setup_matrices(RawConstantResultCircuit {
            base: false_base,
            synthetic_square: false_square,
        })?,
    )?;

    let opposite_honest_cs = proving_cs(ConstantResultCircuit { base: false_base })?;
    assert!(
        !opposite_honest_cs.is_satisfied()?,
        "the honest opposite branch must reject the false base"
    );

    {
        let mut state = opposite_honest_cs.borrow_mut().unwrap();
        state.assignments.witness_assignment[0] = false_square;
    }
    assert!(
        opposite_honest_cs.is_satisfied()?,
        "changing only the opposite branch's synthetic advice must satisfy the false claim"
    );

    let opposite_malicious_cs = proving_cs(RawConstantResultCircuit {
        base: false_base,
        synthetic_square: false_square,
    })?;
    assert!(
        opposite_malicious_cs.is_satisfied()?,
        "the opposite mixed branch must accept its false public relation"
    );

    let opposite_corrected_cs = proving_cs(ConstantPreservingResultCircuit { base: false_base })?;
    assert!(
        !opposite_corrected_cs.is_satisfied()?,
        "the constant-preserving opposite branch must reject the false base"
    );

    let opposite_valid_cs = proving_cs(ConstantResultCircuit { base })?;
    assert!(
        opposite_valid_cs.is_satisfied()?,
        "the valid constant-result relation must remain accepted"
    );

    let mut rng = ark_std::test_rng();
    let proving_key = Groth16::<MNT4_298>::generate_random_parameters_with_reduction(
        ConstantBaseCircuit {
            claimed_square: square,
        },
        &mut rng,
    )?;
    let prepared_vk = prepare_verifying_key(&proving_key.vk);

    let valid_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        ConstantBaseCircuit {
            claimed_square: square,
        },
        &proving_key,
        &mut rng,
    )?;
    assert!(Groth16::<MNT4_298>::verify_proof(
        &prepared_vk,
        &valid_proof,
        &[square]
    )?);

    let false_statement_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        RawConstantBaseCircuit {
            claimed_square: false_square,
            synthetic_base: false_base,
        },
        &proving_key,
        &mut rng,
    )?;
    assert!(
        Groth16::<MNT4_298>::verify_proof(&prepared_vk, &false_statement_proof, &[false_square])?,
        "the victim-generated key must verify the false public square claim"
    );

    Ok(())
}
