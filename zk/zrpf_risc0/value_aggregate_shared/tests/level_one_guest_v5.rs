mod support;

use zenodex_zrpf_protocol_v3::{
    decode_exact_value_aggregate_proposal_v5, encode_value_aggregate_proposal_v5,
};
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;
use zenodex_zrpf_risc0_value_aggregate_shared::{
    compose_value_aggregate_level_one_after_receipt_verification_v5,
    recompose_expected_value_aggregate_level_one_v5, GovernedValueChildIdentityV5,
    ValueAggregateLevelOneInputV5,
};
use zenodex_zrpf_risc0_value_node_shared::{
    spot_value_leaf_manifest_root_v4, spot_value_leaf_profile_id_v4, PINNED_V1_ADAPTER_IMAGE_ID_A,
};

use support::{indexed, leaf_bytes, policy, scope};

const CURRENT_SPOT_VALUE_V4_IMAGE_ID: [u32; 8] = [
    3_987_691_741,
    2_587_475_641,
    2_746_915_647,
    3_706_005_826,
    2_272_313_699,
    2_481_545_785,
    1_563_211_015,
    1_140_320_037,
];
const GUEST_SOURCE: &str = include_str!("../../methods/value_aggregate_l1/src/main.rs");
const WORKSPACE_MANIFEST: &str = include_str!("../../Cargo.toml");
const METHODS_MANIFEST: &str = include_str!("../../methods/Cargo.toml");
const METHODS_BUILD: &str = include_str!("../../methods/build.rs");

fn current_identity() -> GovernedValueChildIdentityV5 {
    let program = program_id_from_risc0_words_v3(CURRENT_SPOT_VALUE_V4_IMAGE_ID).unwrap();
    let adapter = program_id_from_risc0_words_v3(PINNED_V1_ADAPTER_IMAGE_ID_A).unwrap();
    GovernedValueChildIdentityV5::new(
        CURRENT_SPOT_VALUE_V4_IMAGE_ID,
        program,
        spot_value_leaf_profile_id_v4().unwrap(),
        spot_value_leaf_manifest_root_v4(program, adapter).unwrap(),
    )
    .unwrap()
}

#[test]
fn guest_source_ratchets_verify_all_exact_children_before_composition() {
    let authenticate_start = GUEST_SOURCE
        .find("pub(super) fn authenticate(input: ValueAggregateLevelOneInputV5) -> Self")
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

    assert!(authenticate.contains("for child_journal_bytes in input.child_journal_bytes()"));
    assert!(authenticate.contains("PINNED_SPOT_VALUE_V4_IMAGE_ID"));
    assert!(authenticate.contains("child_journal_bytes.as_slice()"));
    assert!(verify < constructed);
    assert!(!authenticate.contains("decode_exact_node_journal_v4"));
    assert!(!authenticate.contains("compose_value_aggregate_level_one"));
    assert!(compose.contains("governed_policy_after_receipt_verification(&self.input)"));
    assert!(compose.contains(
        "compose_value_aggregate_level_one_after_receipt_verification_v5(&self.input, &policy)"
    ));
    assert_eq!(GUEST_SOURCE.matches("env::verify(").count(), 1);
}

#[test]
fn guest_source_commits_only_canonical_bounded_v5_proposal_bytes() {
    let main_start = GUEST_SOURCE.find("pub fn main()").unwrap();
    let main_end = GUEST_SOURCE[main_start..]
        .find("fn read_bounded_input()")
        .map(|offset| main_start + offset)
        .unwrap();
    let main = &GUEST_SOURCE[main_start..main_end];
    let markers = [
        "decode_exact_value_aggregate_guest_input_v5(&input_bytes)",
        "ValueAggregateGuestInputV5::LevelOne(value)",
        "ReceiptVerifiedLevelOneInputV5::authenticate(input)",
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
    assert!(!GUEST_SOURCE.contains("claim_binding"));
    assert!(!GUEST_SOURCE.contains("expected_self_image_id"));
    assert!(!GUEST_SOURCE.contains("receipt_valid"));
}

#[test]
fn guest_source_pins_the_governed_current_spot_value_v4_image() {
    let declaration = "const PINNED_SPOT_VALUE_V4_IMAGE_ID: [u32; 8] = [";
    let start = GUEST_SOURCE.find(declaration).unwrap() + declaration.len();
    let end = GUEST_SOURCE[start..].find("];").unwrap() + start;
    let words = GUEST_SOURCE[start..end]
        .lines()
        .filter_map(|line| line.trim().strip_suffix(','))
        .map(|word| word.replace('_', "").parse::<u32>().unwrap())
        .collect::<Vec<_>>();

    assert_eq!(words, CURRENT_SPOT_VALUE_V4_IMAGE_ID);
}

#[test]
fn level_one_method_is_registered_with_fail_closed_host_placeholders() {
    assert!(WORKSPACE_MANIFEST.contains("\"methods/value_aggregate_l1\""));
    assert!(METHODS_MANIFEST.contains("\"value_aggregate_l1\""));
    assert!(
        METHODS_BUILD.contains("pub const ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ELF: &[u8] = &[];")
    );
    assert!(METHODS_BUILD
        .contains("pub const ZENODEX_ZRPF_RISC0_VALUE_AGGREGATE_L1_ID: [u32; 8] = [0; 8];"));
}

#[test]
fn proof_neutral_current_spot_policy_matches_shared_recomposition() {
    let identity = current_identity();
    let child_bytes = vec![
        leaf_bytes(0, indexed(60, 0), indexed(60, 1), scope(), identity),
        leaf_bytes(1, indexed(60, 1), indexed(60, 2), scope(), identity),
    ];
    let input = ValueAggregateLevelOneInputV5::new(child_bytes).unwrap();
    let policy = policy(scope(), vec![identity, identity]);

    // These fixtures exercise the deterministic post-verification kernel. They
    // authenticate no receipt and advance no proof or settlement claim.
    let expected = recompose_expected_value_aggregate_level_one_v5(&input, &policy).unwrap();
    let composed =
        compose_value_aggregate_level_one_after_receipt_verification_v5(&input, &policy).unwrap();
    let encoded = encode_value_aggregate_proposal_v5(&composed).unwrap();

    assert_eq!(composed, expected);
    assert_eq!(
        decode_exact_value_aggregate_proposal_v5(&encoded).unwrap(),
        expected
    );
}
