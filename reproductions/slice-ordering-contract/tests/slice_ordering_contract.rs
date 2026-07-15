use ark_ff::{One, Zero};
use ark_groth16::{prepare_verifying_key, Groth16};
use ark_mnt4_298::{Fr, MNT4_298};
use ark_r1cs_std::{alloc::AllocVar, boolean::Boolean, cmp::CmpGadget, eq::EqGadget};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
    SynthesisMode,
};

type Pair = [bool; 2];

#[derive(Clone, Copy)]
struct SliceOrderingCircuit {
    left: Pair,
    right: Pair,
}

impl ConstraintSynthesizer<Fr> for SliceOrderingCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let (left, right) = allocate_public_pairs(cs, self.left, self.right)?;
        left.as_slice()
            .is_lt(right.as_slice())?
            .enforce_equal(&Boolean::TRUE)
    }
}

#[derive(Clone, Copy)]
struct NativeEquivalentCircuit {
    left: Pair,
    right: Pair,
}

impl ConstraintSynthesizer<Fr> for NativeEquivalentCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let (left, right) = allocate_public_pairs(cs, self.left, self.right)?;

        // For two total-order elements, lexicographic less-than is decided by the
        // first element, or by the second element only when the first pair is equal.
        let first_less = left[0].is_lt(&right[0])?;
        let first_equal = left[0].is_eq(&right[0])?;
        let second_less = left[1].is_lt(&right[1])?;
        let lexicographic_less = first_less | (first_equal & second_less);
        lexicographic_less.enforce_equal(&Boolean::TRUE)
    }
}

fn allocate_public_pairs(
    cs: ConstraintSystemRef<Fr>,
    left: Pair,
    right: Pair,
) -> Result<([Boolean<Fr>; 2], [Boolean<Fr>; 2]), SynthesisError> {
    let left = [
        Boolean::new_input(cs.clone(), || Ok(left[0]))?,
        Boolean::new_input(cs.clone(), || Ok(left[1]))?,
    ];
    let right = [
        Boolean::new_input(cs.clone(), || Ok(right[0]))?,
        Boolean::new_input(cs, || Ok(right[1]))?,
    ];
    Ok((left, right))
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

fn setup_cs<C: ConstraintSynthesizer<Fr>>(
    circuit: C,
) -> Result<ConstraintSystemRef<Fr>, SynthesisError> {
    synthesize(circuit, SynthesisMode::Setup)
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

fn public_inputs(left: Pair, right: Pair) -> [Fr; 4] {
    [left[0], left[1], right[0], right[1]].map(|bit| if bit { Fr::one() } else { Fr::zero() })
}

#[test]
fn equal_length_slice_can_prove_the_opposite_native_ordering() -> Result<(), SynthesisError> {
    let wrong_left = [true, false];
    let wrong_right = [false, false];
    let valid_left = [false, false];
    let valid_right = [true, false];
    let equal = [false, false];
    let safe_left = [true, true];
    let safe_right = [false, false];

    assert!(wrong_left.as_slice() > wrong_right.as_slice());
    assert!(!(wrong_left.as_slice() < wrong_right.as_slice()));
    assert!(valid_left.as_slice() < valid_right.as_slice());
    assert!(!(equal.as_slice() < equal.as_slice()));
    assert!(!(safe_left.as_slice() < safe_right.as_slice()));
    println!(
        "native oracle: {:?} < {:?} = false",
        wrong_left, wrong_right
    );

    let valid_circuit = SliceOrderingCircuit {
        left: valid_left,
        right: valid_right,
    };
    let wrong_circuit = SliceOrderingCircuit {
        left: wrong_left,
        right: wrong_right,
    };

    let valid_setup = setup_cs(valid_circuit)?;
    let wrong_setup = setup_cs(wrong_circuit)?;
    assert_eq!(
        valid_setup.num_instance_variables(),
        wrong_setup.num_instance_variables()
    );
    assert_eq!(
        valid_setup.num_witness_variables(),
        wrong_setup.num_witness_variables()
    );
    assert_eq!(valid_setup.num_constraints(), wrong_setup.num_constraints());
    assert_eq!(
        valid_setup.to_matrices()?,
        wrong_setup.to_matrices()?,
        "valid and wrong assignments must use the same public circuit relation"
    );

    let wrong_cs = proving_cs(wrong_circuit)?;
    assert_eq!(
        &wrong_cs.instance_assignment()?[1..],
        &public_inputs(wrong_left, wrong_right)
    );
    assert!(
        wrong_cs.is_satisfied()?,
        "the affected slice gadget accepts a natively false less-than statement"
    );
    println!("affected full constraint system: satisfied = true");

    let corrected_cs = proving_cs(NativeEquivalentCircuit {
        left: wrong_left,
        right: wrong_right,
    })?;
    assert!(
        !corrected_cs.is_satisfied()?,
        "the native-equivalent first-difference rule must reject the wrong ordering"
    );
    println!("native-equivalent constraint system: satisfied = false");

    let valid_cs = proving_cs(valid_circuit)?;
    assert!(
        valid_cs.is_satisfied()?,
        "an ordinary valid ordering must pass"
    );

    let equal_cs = proving_cs(SliceOrderingCircuit {
        left: equal,
        right: equal,
    })?;
    assert!(
        !equal_cs.is_satisfied()?,
        "equal slices must not satisfy strict less-than"
    );

    let safe_opposite_cs = proving_cs(SliceOrderingCircuit {
        left: safe_left,
        right: safe_right,
    })?;
    assert!(
        !safe_opposite_cs.is_satisfied()?,
        "the branch where every position is greater remains correctly rejected"
    );
    println!("controls: valid = true, equal = false, all-greater = false");

    let mut rng = ark_std::test_rng();
    let proving_key =
        Groth16::<MNT4_298>::generate_random_parameters_with_reduction(valid_circuit, &mut rng)?;
    let prepared_vk = prepare_verifying_key(&proving_key.vk);

    let valid_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        valid_circuit,
        &proving_key,
        &mut rng,
    )?;
    assert!(Groth16::<MNT4_298>::verify_proof(
        &prepared_vk,
        &valid_proof,
        &public_inputs(valid_left, valid_right),
    )?);

    let wrong_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        wrong_circuit,
        &proving_key,
        &mut rng,
    )?;
    assert!(
        Groth16::<MNT4_298>::verify_proof(
            &prepared_vk,
            &wrong_proof,
            &public_inputs(wrong_left, wrong_right),
        )?,
        "the same key must verify a proof for the natively false public ordering"
    );
    println!("MNT4-298 Groth16: valid proof = true, wrong-order proof = true");

    Ok(())
}
