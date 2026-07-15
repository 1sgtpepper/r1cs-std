use ark_ec::{short_weierstrass::SWCurveConfig, CurveGroup, PrimeGroup};
use ark_ff::{One, Zero};
use ark_groth16::{prepare_verifying_key, Groth16};
use ark_mnt4_298::MNT4_298;
use ark_mnt6_298::{g1::Config as MNT6G1Config, Fq, G1Projective};
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::curves::short_weierstrass::ProjectiveVar,
    GR1CSVar,
};
use ark_relations::gr1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
    SynthesisMode,
};

type RelationVar = ProjectiveVar<MNT6G1Config, FpVar<Fq>>;
type Coordinates = (Fq, Fq, Fq);

#[derive(Clone, Copy)]
struct VictimCircuit {
    claimed: G1Projective,
}

impl ConstraintSynthesizer<Fq> for VictimCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let claimed = RelationVar::new_input(cs.clone(), || Ok(self.claimed))?;
        let expected = RelationVar::new_constant(cs, G1Projective::generator())?;
        claimed.enforce_equal(&expected)
    }
}

#[derive(Clone, Copy)]
struct RawCircuit {
    claimed: Coordinates,
}

impl ConstraintSynthesizer<Fq> for RawCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let claimed = raw_projective_input(cs.clone(), self.claimed)?;
        let expected = RelationVar::new_constant(cs, G1Projective::generator())?;
        claimed.enforce_equal(&expected)
    }
}

#[derive(Clone, Copy)]
struct StrictControlCircuit {
    claimed: Coordinates,
}

impl ConstraintSynthesizer<Fq> for StrictControlCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let claimed = raw_projective_input(cs.clone(), self.claimed)?;
        let expected = RelationVar::new_constant(cs, G1Projective::generator())?;
        enforce_strict_projective_equality(&claimed, &expected)
    }
}

fn raw_projective_input(
    cs: ConstraintSystemRef<Fq>,
    coordinates: Coordinates,
) -> Result<RelationVar, SynthesisError> {
    let x = FpVar::new_input(cs.clone(), || Ok(coordinates.0))?;
    let y = FpVar::new_input(cs.clone(), || Ok(coordinates.1))?;
    let z = FpVar::new_input(cs, || Ok(coordinates.2))?;
    let point = RelationVar::new(x, y, z);

    // This is the exact relation enforced by ProjectiveVar's public allocator.
    let x2 = point.x.square()?;
    let y2 = point.y.square()?;
    let z2 = point.z.square()?;
    let t = &point.x * (x2 + &z2 * MNT6G1Config::COEFF_A);
    point.z.mul_equals(&(y2 - z2 * MNT6G1Config::COEFF_B), &t)?;
    Ok(point)
}

fn enforce_strict_projective_equality(
    left: &RelationVar,
    right: &RelationVar,
) -> Result<(), SynthesisError> {
    let x_equal = (&left.x * &right.z).is_eq(&(&right.x * &left.z))?;
    let y_equal = (&left.y * &right.z).is_eq(&(&right.y * &left.z))?;
    let coordinates_equal = x_equal & y_equal;
    let left_zero = left.z.is_zero()?;
    let right_zero = right.z.is_zero()?;
    let both_zero = &left_zero & &right_zero;
    let both_nonzero = !left_zero & !right_zero;
    (both_zero | (both_nonzero & coordinates_equal)).enforce_equal(&Boolean::TRUE)
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

fn generator_coordinates() -> Coordinates {
    let generator = G1Projective::generator().into_affine();
    (generator.x, generator.y, Fq::one())
}

#[test]
fn public_all_zero_encoding_proves_generator_equality() -> Result<(), SynthesisError> {
    let generator = G1Projective::generator();
    let identity = G1Projective::zero();
    let all_zero = (Fq::zero(), Fq::zero(), Fq::zero());
    let canonical_identity = (Fq::zero(), Fq::one(), Fq::zero());

    assert_ne!(identity, generator, "native points must be unequal");

    let decoded_all_zero = RelationVar::new(
        FpVar::constant(Fq::zero()),
        FpVar::constant(Fq::zero()),
        FpVar::constant(Fq::zero()),
    );
    assert_eq!(
        decoded_all_zero.value()?,
        identity,
        "the adversarial coordinates decode as the native identity"
    );

    let victim_setup = setup_matrices(VictimCircuit { claimed: generator })?;
    let malicious_setup = setup_matrices(RawCircuit { claimed: all_zero })?;
    assert_eq!(
        victim_setup.num_instance_variables(),
        malicious_setup.num_instance_variables()
    );
    assert_eq!(
        victim_setup.num_witness_variables(),
        malicious_setup.num_witness_variables()
    );
    assert_eq!(
        victim_setup.num_constraints(),
        malicious_setup.num_constraints()
    );
    assert_eq!(
        victim_setup.to_matrices()?,
        malicious_setup.to_matrices()?,
        "the victim setup and malicious assignment must define identical matrices"
    );

    let malicious_cs = proving_cs(RawCircuit { claimed: all_zero })?;
    assert_eq!(
        &malicious_cs.instance_assignment()?[1..],
        &[Fq::zero(), Fq::zero(), Fq::zero()]
    );
    assert!(
        malicious_cs.is_satisfied()?,
        "the adversarial public assignment must satisfy the full constraint system"
    );

    let canonical_zero_cs = proving_cs(RawCircuit {
        claimed: canonical_identity,
    })?;
    assert!(
        !canonical_zero_cs.is_satisfied()?,
        "the canonical identity must not equal the generator"
    );

    let valid_cs = proving_cs(RawCircuit {
        claimed: generator_coordinates(),
    })?;
    assert!(
        valid_cs.is_satisfied()?,
        "the generator's valid projective encoding must remain accepted"
    );

    let corrected_cs = proving_cs(StrictControlCircuit { claimed: all_zero })?;
    assert!(
        !corrected_cs.is_satisfied()?,
        "a zero/nonzero-aware equality rule must reject the adversarial encoding"
    );

    let mut rng = ark_std::test_rng();
    let proving_key = Groth16::<MNT4_298>::generate_random_parameters_with_reduction(
        VictimCircuit { claimed: generator },
        &mut rng,
    )?;
    let prepared_vk = prepare_verifying_key(&proving_key.vk);

    let valid_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        VictimCircuit { claimed: generator },
        &proving_key,
        &mut rng,
    )?;
    let (generator_x, generator_y, generator_z) = generator_coordinates();
    let generator_inputs = [generator_x, generator_y, generator_z];
    assert!(Groth16::<MNT4_298>::verify_proof(
        &prepared_vk,
        &valid_proof,
        &generator_inputs
    )?);

    let forged_proof = Groth16::<MNT4_298>::create_random_proof_with_reduction(
        RawCircuit { claimed: all_zero },
        &proving_key,
        &mut rng,
    )?;
    assert!(
        Groth16::<MNT4_298>::verify_proof(
            &prepared_vk,
            &forged_proof,
            &[Fq::zero(), Fq::zero(), Fq::zero()]
        )?,
        "a victim-generated key must verify the malicious false-statement proof"
    );

    Ok(())
}
