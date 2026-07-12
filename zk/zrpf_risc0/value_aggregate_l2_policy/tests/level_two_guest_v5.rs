#[path = "../../value_aggregate_shared/tests/support/mod.rs"]
mod support;

use zenodex_zrpf_protocol_v3::{
    decode_exact_value_aggregate_proposal_v5, encode_value_aggregate_proposal_v5,
};
use zenodex_zrpf_risc0_value_aggregate_l2_policy::pinned_value_aggregate_level_one_identity_v5;
use zenodex_zrpf_risc0_value_aggregate_shared::{
    compose_value_aggregate_level_two_after_receipt_verification_v5,
    recompose_expected_value_aggregate_level_one_v5,
    recompose_expected_value_aggregate_level_two_v5, ValueAggregateLevelOneInputV5,
    ValueAggregateLevelTwoInputV5, ValueAggregateRecompositionPolicyV5,
};

use support::{identity, indexed, leaf_bytes, policy, scope};

const GUEST_SOURCE: &str = include_str!("../../methods/value_aggregate_l2/src/main.rs");
const WORKSPACE_MANIFEST: &str = include_str!("../../Cargo.toml");
const METHODS_MANIFEST: &str = include_str!("../../methods/Cargo.toml");
const METHODS_BUILD: &str = include_str!("../../methods/build.rs");
const L2_MANIFEST: &str = include_str!("../../methods/value_aggregate_l2/Cargo.toml");

fn level_one_bytes(start: u64) -> Vec<u8> {
    let leaf_identity = identity(100, 70, 71);
    let input = ValueAggregateLevelOneInputV5::new(vec![
        leaf_bytes(
            start,
            indexed(60, start),
            indexed(60, start + 1),
            scope(),
            leaf_identity,
        ),
        leaf_bytes(
            start + 1,
            indexed(60, start + 1),
            indexed(60, start + 2),
            scope(),
            leaf_identity,
        ),
    ])
    .unwrap();
    let proposal = recompose_expected_value_aggregate_level_one_v5(
        &input,
        &policy(scope(), vec![leaf_identity, leaf_identity]),
    )
    .unwrap();
    encode_value_aggregate_proposal_v5(&proposal).unwrap()
}

#[test]
fn guest_source_verifies_every_exact_l1_child_before_decode_or_composition() {
    let authenticate_start = GUEST_SOURCE
        .find("pub(super) fn authenticate(input: ValueAggregateLevelTwoInputV5) -> Self")
        .unwrap();
    let compose_start = GUEST_SOURCE[authenticate_start..]
        .find("pub(super) fn compose(")
        .map(|offset| authenticate_start + offset)
        .unwrap();
    let authenticate = &GUEST_SOURCE[authenticate_start..compose_start];
    let verify = authenticate.find("env::verify(").unwrap();
    let constructed = authenticate.find("Self { input }").unwrap();
    let compose_end = GUEST_SOURCE[compose_start..]
        .find("fn governed_policy_after_receipt_verification(")
        .map(|offset| compose_start + offset)
        .unwrap();
    let compose = &GUEST_SOURCE[compose_start..compose_end];

    assert!(authenticate.contains("for child_proposal_bytes in input.child_proposal_bytes()"));
    assert!(authenticate.contains("PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5"));
    assert!(authenticate.contains("child_proposal_bytes.as_slice()"));
    assert!(verify < constructed);
    assert!(!authenticate.contains("decode_exact_value_aggregate_proposal_v5"));
    assert!(!authenticate.contains("compose_value_aggregate_level_two"));
    assert!(compose.contains("governed_policy_after_receipt_verification(&self.input)"));
    assert!(compose.contains(
        "compose_value_aggregate_level_two_after_receipt_verification_v5(&self.input, &policy)"
    ));
    assert!(GUEST_SOURCE.contains("pinned_value_aggregate_level_one_identity_v5()?"));
    assert_eq!(GUEST_SOURCE.matches("env::verify(").count(), 1);
}

#[test]
fn guest_source_commits_only_canonical_bounded_level_two_v5_proposal() {
    let main_start = GUEST_SOURCE.find("pub fn main()").unwrap();
    let main_end = GUEST_SOURCE[main_start..]
        .find("fn read_bounded_input()")
        .map(|offset| main_start + offset)
        .unwrap();
    let main = &GUEST_SOURCE[main_start..main_end];
    let markers = [
        "decode_exact_value_aggregate_guest_input_v5(&input_bytes)",
        "ValueAggregateGuestInputV5::LevelTwo(value)",
        "ReceiptVerifiedLevelTwoInputV5::authenticate(input)",
        "verified.compose()",
        "encode_value_aggregate_proposal_v5(&proposal)",
        "env::commit_slice(&proposal_bytes)",
    ];
    let positions = markers.map(|marker| main.find(marker).unwrap());
    assert_eq!(positions, {
        let mut sorted = positions;
        sorted.sort_unstable();
        sorted
    });
    assert!(GUEST_SOURCE.contains("MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5 == 524_324"));
    assert!(GUEST_SOURCE.contains("MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 == 65_536"));
    for forbidden in [
        "expected_self_image_id",
        "receipt_valid",
        "settlement_authority",
    ] {
        assert!(!GUEST_SOURCE.contains(forbidden));
    }
}

#[test]
fn level_two_method_and_l2_only_policy_are_registered() {
    assert!(WORKSPACE_MANIFEST.contains("\"value_aggregate_l2_policy\""));
    assert!(WORKSPACE_MANIFEST.contains("\"methods/value_aggregate_l2\""));
    assert!(METHODS_MANIFEST.contains("\"value_aggregate_l2\""));
    assert!(L2_MANIFEST.contains("zenodex-zrpf-risc0-value-aggregate-l2-policy"));
    assert!(
        METHODS_BUILD.contains("pub const ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L2_ELF: &[u8] = &[];")
    );
    assert!(METHODS_BUILD
        .contains("pub const ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L2_ID: [u32; 8] = [0; 8];"));
}

#[test]
fn proof_neutral_governed_l1_identity_matches_level_two_recomposition() {
    let identity = pinned_value_aggregate_level_one_identity_v5().unwrap();
    let input =
        ValueAggregateLevelTwoInputV5::new(vec![level_one_bytes(0), level_one_bytes(2)]).unwrap();
    let policy = ValueAggregateRecompositionPolicyV5::new(
        scope(),
        vec![identity; input.child_proposal_bytes().len()],
    )
    .unwrap();

    // This exercises only the deterministic post-verification kernel. It
    // authenticates no receipt and advances no settlement or release claim.
    let expected = recompose_expected_value_aggregate_level_two_v5(&input, &policy).unwrap();
    let composed =
        compose_value_aggregate_level_two_after_receipt_verification_v5(&input, &policy).unwrap();
    let encoded = encode_value_aggregate_proposal_v5(&composed).unwrap();

    assert_eq!(composed, expected);
    assert_eq!(expected.aggregate_level(), 2);
    assert_eq!(
        decode_exact_value_aggregate_proposal_v5(&encoded).unwrap(),
        expected
    );
    assert!(expected.children().iter().all(|child| {
        child.verified_program_id() == identity.expected_program_id()
            && child.proof_profile_id() == identity.expected_profile_id()
            && child.program_manifest_root() == identity.expected_manifest_root()
    }));
}
