const SOURCE_OPENING: &str = include_str!("../src/source_opening.rs");

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
