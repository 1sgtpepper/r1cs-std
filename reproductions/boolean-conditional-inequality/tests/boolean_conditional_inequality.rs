use ark_r1cs_std::{alloc::AllocVar, boolean::Boolean, eq::EqGadget};
use ark_relations::gr1cs::ConstraintSystem;
use ark_test_curves::bls12_381::Fr;

#[derive(Debug)]
struct Outcome {
    synthesis_ok: bool,
    satisfied: bool,
}

fn native_oracle(a: bool, b: bool, condition: bool) -> bool {
    !condition || a != b
}

fn current_variable_case(a_value: bool, b_value: bool, condition_value: bool) -> Outcome {
    let cs = ConstraintSystem::<Fr>::new_ref();
    let a = Boolean::new_witness(cs.clone(), || Ok(a_value)).unwrap();
    let b = Boolean::new_witness(cs.clone(), || Ok(b_value)).unwrap();
    let condition = Boolean::new_input(cs.clone(), || Ok(condition_value)).unwrap();

    let synthesis_ok = a.conditional_enforce_not_equal(&b, &condition).is_ok();
    let satisfied = synthesis_ok && cs.is_satisfied().unwrap();
    println!(
        "current a={a_value} b={b_value} condition={condition_value} native={} synthesis_ok={synthesis_ok} satisfied={satisfied}",
        native_oracle(a_value, b_value, condition_value),
    );
    Outcome {
        synthesis_ok,
        satisfied,
    }
}

fn safe_variable_case(a_value: bool, b_value: bool, condition_value: bool) -> Outcome {
    let cs = ConstraintSystem::<Fr>::new_ref();
    let a = Boolean::new_witness(cs.clone(), || Ok(a_value)).unwrap();
    let b = Boolean::new_witness(cs.clone(), || Ok(b_value)).unwrap();
    let condition = Boolean::new_input(cs.clone(), || Ok(condition_value)).unwrap();

    let synthesis_ok = (a.is_eq(&b).unwrap() & &condition)
        .enforce_equal(&Boolean::FALSE)
        .is_ok();
    let satisfied = synthesis_ok && cs.is_satisfied().unwrap();
    println!(
        "safe a={a_value} b={b_value} condition={condition_value} native={} synthesis_ok={synthesis_ok} satisfied={satisfied}",
        native_oracle(a_value, b_value, condition_value),
    );
    Outcome {
        synthesis_ok,
        satisfied,
    }
}

#[test]
fn dynamic_false_rejects_valid_equal_variables() {
    assert!(native_oracle(true, true, false));

    let current = current_variable_case(true, true, false);
    assert!(current.synthesis_ok);
    assert!(
        !current.satisfied,
        "the affected revision should expose the dynamic-false rejection"
    );

    let safe = safe_variable_case(true, true, false);
    assert!(safe.synthesis_ok);
    assert!(
        safe.satisfied,
        "the nearest safe implication must accept the same native-valid statement"
    );

    let cs = ConstraintSystem::<Fr>::new_ref();
    let a = Boolean::new_witness(cs.clone(), || Ok(true)).unwrap();
    let b = Boolean::new_witness(cs.clone(), || Ok(true)).unwrap();
    a.conditional_enforce_not_equal(&b, &Boolean::FALSE)
        .unwrap();
    assert!(
        cs.is_satisfied().unwrap(),
        "the semantically identical literal-false guard is the negative control"
    );
}

#[test]
fn dynamic_true_and_unequal_value_controls_follow_the_oracle() {
    let unequal_true = current_variable_case(false, true, true);
    assert!(native_oracle(false, true, true));
    assert!(unequal_true.synthesis_ok && unequal_true.satisfied);

    let equal_true = current_variable_case(true, true, true);
    assert!(!native_oracle(true, true, true));
    assert!(equal_true.synthesis_ok && !equal_true.satisfied);

    let unequal_false = current_variable_case(false, true, false);
    assert!(native_oracle(false, true, false));
    assert!(unequal_false.synthesis_ok && !unequal_false.satisfied);
}
