const SOURCE_OPENING: &str = include_str!("../src/source_opening.rs");
const SHARED_LIB: &str = include_str!("../src/lib.rs");
const JOURNAL: &str = include_str!("../src/journal.rs");
const VERIFIER: &str = include_str!("../../verifier/src/lib.rs");

#[test]
fn source_transition_executes_once_and_summary_reuses_the_result() {
    let production_source = SOURCE_OPENING.split_once("#[cfg(test)]").unwrap().0;
    assert_eq!(
        production_source
            .matches("execute_state_proof_input_v1(")
            .count(),
        1,
        "the V7 source opening must execute the source transition exactly once"
    );
    assert!(
        !production_source.contains("compose_spot_recursive_leaf_summary_v1"),
        "the legacy summary composer would execute the source transition a second time"
    );
    assert!(
        production_source.contains("recompose_spot_recursive_leaf_summary_from_transition_v1"),
        "the authenticated transition must feed the transition-free summary recomposition"
    );
}

#[test]
fn pre_materialization_v1_status_and_authority_nonclaims_are_explicit() {
    assert!(SHARED_LIB.contains("no_governed_v7_image_or_receipt_materialized"));
    assert!(SHARED_LIB.contains("SPOT_SETTLEMENT_V7_RECEIPT_AUTHORITY: bool = false"));
    assert!(SHARED_LIB.contains("SPOT_SETTLEMENT_V7_SETTLEMENT_AUTHORITY: bool = false"));
    assert!(SHARED_LIB.contains("SPOT_SETTLEMENT_V7_PRODUCTION_AUTHORITY: bool = false"));
}

#[test]
fn exact_plan_bytes_sha256_is_derived_and_cross_bound() {
    assert!(JOURNAL.contains("settlement_effect_plan_bytes_sha256"));
    assert!(JOURNAL.contains("sha256_commitment(&plan_bytes, \"settlement plan bytes\")"));
    assert!(VERIFIER.contains("settlement_effect_plan_bytes_sha256"));
    assert!(VERIFIER.contains("exact_plan_b_bytes_sha256 = sha256_commitment(&exact_plan_b_bytes)"));
    assert!(VERIFIER
        .contains("output.settlement_effect_plan_bytes_sha256 == exact_plan_b_bytes_sha256"));
}
