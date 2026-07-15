use ark_ec::{pairing::Pairing, PrimeGroup};
use ark_ff::{Field, One, Zero};
use ark_groth16::{prepare_verifying_key, Groth16};
use ark_mnt4_298::{
    Config as MNT4Config, Fq, Fq4, G1Prepared, G1Projective, G2Prepared, G2Projective, MNT4_298,
};
use ark_mnt6_298::MNT6_298;
use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::FieldVar,
    groups::mnt4::{G1Var, G2PreparedVar, G2Var},
    pairing::{mnt4::PairingVar as MNT4PairingVar, PairingVar},
};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
    SynthesisMode,
};

#[derive(Clone)]
struct DirectPreparedCircuit {
    claimed_q: G2Projective,
    prepared_q: G2Prepared,
}

impl ConstraintSynthesizer<Fq> for DirectPreparedCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let claimed_q = G2Var::<MNT4Config>::new_input(cs.clone(), || Ok(self.claimed_q))?;
        let claimed_q = claimed_q.to_affine()?;
        let prepared_q =
            G2PreparedVar::<MNT4Config>::new_witness(cs.clone(), || Ok(self.prepared_q))?;

        // The source point is fixed publicly; only the cached quotient and line data remain advice.
        prepared_q.x.enforce_equal(&claimed_q.x)?;
        prepared_q.y.enforce_equal(&claimed_q.y)?;

        let p = G1Var::<MNT4Config>::new_constant(cs, G1Projective::generator())?;
        let p = MNT4PairingVar::<MNT4Config>::prepare_g1(&p)?;
        let result = MNT4PairingVar::<MNT4Config>::pairing(p, prepared_q)?;
        result.enforce_equal(&FieldVar::one())
    }
}

#[derive(Clone, Copy)]
struct DerivedFalseCircuit {
    claimed_q: G2Projective,
}

impl ConstraintSynthesizer<Fq> for DerivedFalseCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let p = G1Var::<MNT4Config>::new_constant(cs.clone(), G1Projective::generator())?;
        let q = G2Var::<MNT4Config>::new_input(cs, || Ok(self.claimed_q))?;
        let p = MNT4PairingVar::<MNT4Config>::prepare_g1(&p)?;
        let q = MNT4PairingVar::<MNT4Config>::prepare_g2(&q)?;
        let result = MNT4PairingVar::<MNT4Config>::pairing(p, q)?;
        result.enforce_equal(&FieldVar::one())
    }
}

#[derive(Clone, Copy)]
struct DerivedValidCircuit {
    claimed_q: G2Projective,
}

impl ConstraintSynthesizer<Fq> for DerivedValidCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let p = G1Projective::generator();
        let p_pos = G1Var::<MNT4Config>::new_constant(cs.clone(), p)?;
        let p_neg = G1Var::<MNT4Config>::new_constant(cs.clone(), -p)?;
        let q = G2Var::<MNT4Config>::new_input(cs, || Ok(self.claimed_q))?;
        let p_pos = MNT4PairingVar::<MNT4Config>::prepare_g1(&p_pos)?;
        let p_neg = MNT4PairingVar::<MNT4Config>::prepare_g1(&p_neg)?;
        let q = MNT4PairingVar::<MNT4Config>::prepare_g2(&q)?;
        let result =
            MNT4PairingVar::<MNT4Config>::product_of_pairings(&[p_pos, p_neg], &[q.clone(), q])?;
        result.enforce_equal(&FieldVar::one())
    }
}

fn forged_preparation(p: G1Projective, q: G2Projective) -> (G2Prepared, G2Prepared) {
    let p_prepared = G1Prepared::from(p);
    let honest = G2Prepared::from(q);
    let mut forged = honest.clone();

    forged.y_over_twist = Zero::zero();
    for coefficient in &mut forged.double_coefficients {
        coefficient.c_h = Zero::zero();
        coefficient.c_4c = Zero::zero();
        coefficient.c_j = Zero::zero();
        coefficient.c_l = One::one();
    }
    for coefficient in &mut forged.addition_coefficients {
        coefficient.c_l1 = Zero::zero();
        coefficient.c_rz = p_prepared.y_twist.inverse().unwrap();
    }
    (honest, forged)
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

fn setup_cs<C: ConstraintSynthesizer<Fq>>(
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

#[test]
fn mnt4_direct_g2_preparation_must_bind_line_data() -> Result<(), SynthesisError> {
    let p = G1Projective::generator();
    let q = G2Projective::generator();
    assert_ne!(
        MNT4_298::pairing(p, q).0,
        Fq4::one(),
        "the native generator pairing must not be the target-field identity"
    );
    println!("native_generator_pairing_is_identity=false");

    let (honest, forged) = forged_preparation(p, q);
    assert_eq!(
        forged.x, honest.x,
        "the claimed G2 x-coordinate is unchanged"
    );
    assert_eq!(
        forged.y, honest.y,
        "the claimed G2 y-coordinate is unchanged"
    );
    assert_eq!(
        forged.x_over_twist, honest.x_over_twist,
        "the unused x quotient is unchanged"
    );
    assert_ne!(
        forged.y_over_twist, honest.y_over_twist,
        "the forged preparation must change proof-relevant cached data"
    );
    assert_eq!(
        forged.double_coefficients.len(),
        honest.double_coefficients.len(),
        "the forged double vector must preserve honest topology"
    );
    assert_eq!(
        forged.addition_coefficients.len(),
        honest.addition_coefficients.len(),
        "the forged addition vector must preserve honest topology"
    );
    println!(
        "honest_shape double_coefficients={} addition_coefficients={}",
        honest.double_coefficients.len(),
        honest.addition_coefficients.len()
    );

    let honest_direct = DirectPreparedCircuit {
        claimed_q: q,
        prepared_q: honest,
    };
    let forged_direct = DirectPreparedCircuit {
        claimed_q: q,
        prepared_q: forged,
    };

    let honest_setup = setup_cs(honest_direct.clone())?;
    let forged_setup = setup_cs(forged_direct.clone())?;
    assert_eq!(
        honest_setup.num_constraints(),
        forged_setup.num_constraints()
    );
    assert_eq!(
        honest_setup.num_instance_variables(),
        forged_setup.num_instance_variables()
    );
    assert_eq!(
        honest_setup.num_witness_variables(),
        forged_setup.num_witness_variables()
    );
    assert_eq!(
        honest_setup.to_matrices()?,
        forged_setup.to_matrices()?,
        "honest and forged fixed-shape preparations must define the same circuit"
    );
    println!(
        "matrix_shape instance_variables={} witness_variables={} constraints={}",
        forged_setup.num_instance_variables(),
        forged_setup.num_witness_variables(),
        forged_setup.num_constraints()
    );

    let forged_cs = proving_cs(forged_direct.clone())?;
    let forged_satisfied = forged_cs.is_satisfied()?;
    assert!(
        forged_satisfied,
        "the forged line data must satisfy the fixed-public-point circuit"
    );
    let public_inputs = forged_cs.instance_assignment()?[1..].to_vec();
    assert_eq!(
        public_inputs.len(),
        6,
        "the statement must retain all three Fq2 projective coordinates"
    );
    println!(
        "forged_full_cs_satisfied={forged_satisfied} public_inputs={}",
        public_inputs.len()
    );

    let honest_direct_cs = proving_cs(honest_direct.clone())?;
    let honest_direct_satisfied = honest_direct_cs.is_satisfied()?;
    assert_eq!(
        &honest_direct_cs.instance_assignment()?[1..],
        public_inputs.as_slice(),
        "honest and forged direct circuits must claim the same public G2 point"
    );
    assert!(
        !honest_direct_satisfied,
        "honest prepared data must preserve the native non-identity result"
    );

    let derived_false_cs = proving_cs(DerivedFalseCircuit { claimed_q: q })?;
    let derived_false_satisfied = derived_false_cs.is_satisfied()?;
    assert_eq!(
        &derived_false_cs.instance_assignment()?[1..],
        public_inputs.as_slice(),
        "the safe derived circuit must check the same public G2 point"
    );
    assert!(
        !derived_false_satisfied,
        "deriving the preparation from the public G2 point must reject the false identity"
    );

    let derived_valid_cs = proving_cs(DerivedValidCircuit { claimed_q: q })?;
    let derived_valid_satisfied = derived_valid_cs.is_satisfied()?;
    assert_eq!(
        &derived_valid_cs.instance_assignment()?[1..],
        public_inputs.as_slice(),
        "the valid control must retain the same public G2 point"
    );
    assert!(
        derived_valid_satisfied,
        "derived e(P,Q)e(-P,Q)=1 must remain satisfiable"
    );
    println!(
        "controls honest_direct_satisfied={honest_direct_satisfied} derived_false_satisfied={derived_false_satisfied} derived_valid_satisfied={derived_valid_satisfied}"
    );

    let mut rng = ark_std::test_rng();
    let proving_key =
        Groth16::<MNT6_298>::generate_random_parameters_with_reduction(honest_direct, &mut rng)?;
    let prepared_vk = prepare_verifying_key(&proving_key.vk);
    let proof = Groth16::<MNT6_298>::create_random_proof_with_reduction(
        forged_direct,
        &proving_key,
        &mut rng,
    )?;
    let proof_verified = Groth16::<MNT6_298>::verify_proof(&prepared_vk, &proof, &public_inputs)?;
    assert!(
        proof_verified,
        "the outer verifier must accept the forged proof for the public generator point"
    );
    println!("outer_mnt6_proof_verified={proof_verified}");

    Ok(())
}
