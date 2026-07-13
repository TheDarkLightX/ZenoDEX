use serde_json::Value;
use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::{
    sha256_canonical_dex_snapshot_v1, DexSnapshotV1, NonceEntryV1, NonceStateV1,
};
use zenodex_zrpf_protocol_v3::{
    ApplicationIdV3, AssetEffectInputV2, AssetEffectKindV2, AssetEffectV2, AuthorizationGrantIdV1,
    AuthorizationScopeIdV1, AuthorizationSubjectIdV1, AuthorizedEconomicActionV1, CommitmentV3,
    DomainIdV3, EconomicActionBatchV1, EconomicActionRecordInputV1, EconomicActionRecordV1,
    EconomicActionTypeIdV1, LedgerCellWriteInputV2, LedgerCellWriteV2, SettlementEffectPlanInputV2,
    SettlementEffectPlanV2, ValueHashV2,
};
use zenodex_zrpf_risc0_spot_settlement_v7_effect_binding_shared::{
    bind_spot_settlement_effect_plan_v1, decode_exact_spot_settlement_v7_effect_binding_journal_v1,
    derive_expected_spot_v7_settlement_effect_plan_v1,
    derive_spot_settlement_state_effect_opening_v1,
    encode_spot_settlement_v7_effect_binding_journal_v1, SpotLedgerCellKindV1,
    SpotLedgerCellRoleV1, SpotSettlementStateEffectOpeningV1, SpotSettlementV7EffectBindingErrorV1,
    SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1,
    SPOT_SETTLEMENT_V7_EFFECT_BINDING_RECEIPT_AUTHORITY,
    SPOT_SETTLEMENT_V7_EFFECT_BINDING_SETTLEMENT_AUTHORITY,
};
use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::{
    verify_restricted_spot_state_root_v5_transition_v1, ExpectedLegacySpotCommitmentsV1,
    ExpectedSpotStateRootsV5, RestrictedSpotStateRootV5BridgeError,
    RestrictedSpotStateRootV5ProfileV1, RestrictedSpotStateRootV5TransitionInputV1,
};
use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::{
    compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1,
    decode_exact_spot_state_root_v7_semantic_journal_v1, BoundedSpotStateRootV7HostInputV1,
    LegacySpotSourceProjectionV7, SpotStateRootV7SemanticJournalV1,
};

const V5_FIXTURE: &str =
    include_str!("../../../tests/fixtures/zrpf_spot_state_root_v5_bridge_v1.json");
const V7_FIXTURE: &str =
    include_str!("../../../tests/fixtures/zrpf_spot_state_root_v7_semantic_v1.json");
const _: [(); 1] = [(); (!SPOT_SETTLEMENT_V7_EFFECT_BINDING_RECEIPT_AUTHORITY) as usize];
const _: [(); 1] = [(); (!SPOT_SETTLEMENT_V7_EFFECT_BINDING_SETTLEMENT_AUTHORITY) as usize];

struct FixtureV1 {
    journal: SpotStateRootV7SemanticJournalV1,
    pre_state: DexSnapshotV1,
    post_state: DexSnapshotV1,
}

#[derive(Clone, Copy)]
struct SourcePlanOverridesV1 {
    authorization_nonce: Option<u64>,
    authorization_subject_seed: u8,
    extra_cell_write: bool,
}

impl SourcePlanOverridesV1 {
    const NONE: Self = Self {
        authorization_nonce: None,
        authorization_subject_seed: 4,
        extra_cell_write: false,
    };
}

#[test]
fn exact_fixture_derives_plan_b_from_source_plan_a_lineage() {
    let fixture = fixture();
    let opening = fixture_opening(&fixture);
    let source = source_plan(&opening, SourcePlanOverridesV1::NONE);
    assert_eq!(source.ledger_cell_writes().len(), 1);
    assert_eq!(source.asset_effects().len(), 1);

    let expected = derive_expected_spot_v7_settlement_effect_plan_v1(&opening, &source).unwrap();
    let second = derive_expected_spot_v7_settlement_effect_plan_v1(&opening, &source).unwrap();
    assert_eq!(expected, second);
    assert_eq!(expected.ledger_cell_writes().len(), 4);
    assert_eq!(expected.asset_effects().len(), 2);

    let source_action = &source.economic_action_batch().actions()[0];
    let expected_action = &expected.economic_action_batch().actions()[0];
    assert_eq!(
        expected_action.record().application_id(),
        source_action.record().application_id()
    );
    assert_eq!(
        expected_action.record().chain_or_domain_id(),
        source_action.record().chain_or_domain_id()
    );
    assert_eq!(
        expected_action.record().authorization_subject_id(),
        source_action.record().authorization_subject_id()
    );
    assert_eq!(
        expected_action.record().action_type_id(),
        source_action.record().action_type_id()
    );
    assert_eq!(
        expected_action.record().authorization_scope_id(),
        source_action.record().authorization_scope_id()
    );
    assert_eq!(
        expected_action.record().authorization_nonce(),
        source_action.record().authorization_nonce()
    );
    assert_eq!(
        expected_action.record().valid_from_epoch(),
        source_action.record().valid_from_epoch()
    );
    assert_eq!(
        expected_action.record().valid_through_epoch(),
        source_action.record().valid_through_epoch()
    );
    assert_eq!(
        expected_action.authorization_grant_id(),
        source_action.authorization_grant_id()
    );
    assert_eq!(
        expected_action.authorization_grant_spend().unwrap(),
        source_action.authorization_grant_spend().unwrap()
    );
    assert_eq!(
        expected.economic_action_batch().epoch_id(),
        source.economic_action_batch().epoch_id()
    );
    assert_eq!(expected.public_policy_hash(), source.public_policy_hash());
    assert_eq!(
        expected_action.record().action_semantics_hash(),
        opening.action_semantics_hash()
    );
    assert_eq!(
        expected_action.record().effect_commitment(),
        opening.effect_commitment()
    );
    assert!(expected_action
        .record()
        .consumed_object_ids()
        .contains(&source.canonical_commitment().unwrap()));
    assert!(expected_action
        .record()
        .consumed_object_ids()
        .contains(&opening.source_journal_commitment()));
    for source_object in source_action.record().consumed_object_ids() {
        assert!(expected_action
            .record()
            .consumed_object_ids()
            .contains(source_object));
    }

    let bound = bind_spot_settlement_effect_plan_v1(opening, &source).unwrap();
    assert_eq!(bound.plan(), &expected);
    assert_eq!(
        bound.journal().source_settlement_plan_commitment(),
        source.canonical_commitment().unwrap()
    );
    assert_eq!(
        bound.journal().settlement_effect_plan_commitment(),
        expected.canonical_commitment().unwrap()
    );
    assert_eq!(
        bound.journal().pre_state_root(),
        bound.opening().pre_state_root()
    );
    assert_eq!(
        bound.journal().post_state_root(),
        bound.opening().post_state_root()
    );

    let encoded = encode_spot_settlement_v7_effect_binding_journal_v1(bound.journal());
    assert_eq!(
        encoded.len(),
        SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1
    );
    assert_eq!(
        decode_exact_spot_settlement_v7_effect_binding_journal_v1(&encoded).unwrap(),
        *bound.journal()
    );
    assert_ne!(
        bound.journal().canonical_commitment().unwrap().into_bytes(),
        [0; 32]
    );
}

#[test]
fn complete_opening_has_two_exact_debits_and_two_exact_credits() {
    let fixture = fixture();
    let opening = fixture_opening(&fixture);
    assert_eq!(opening.input_amount_atoms(), 1_000);
    assert_eq!(opening.output_amount_atoms(), 1_992);
    assert_eq!(opening.cell_transitions().len(), 4);
    assert_eq!(
        opening
            .cell_transitions()
            .iter()
            .filter(|change| change.pre().kind() == SpotLedgerCellKindV1::AccountBalance)
            .count(),
        2
    );
    assert_eq!(
        opening
            .cell_transitions()
            .iter()
            .filter(|change| change.pre().kind() == SpotLedgerCellKindV1::PoolReserve)
            .count(),
        2
    );
    assert_eq!(
        opening
            .cell_transitions()
            .iter()
            .filter(|change| change.role() == SpotLedgerCellRoleV1::Debit)
            .count(),
        2
    );
    assert_eq!(
        opening
            .cell_transitions()
            .iter()
            .filter(|change| change.role() == SpotLedgerCellRoleV1::Credit)
            .count(),
        2
    );
}

#[test]
fn snapshot_mutation_cannot_be_hidden_behind_the_v7_journal() {
    let mut fixture = fixture();
    fixture.post_state.balances[1].amount += 1;
    assert!(matches!(
        derive_spot_settlement_state_effect_opening_v1(
            &fixture.journal,
            &fixture.pre_state,
            &fixture.post_state
        ),
        Err(SpotSettlementV7EffectBindingErrorV1::StateRootBridge(_))
    ));
}

#[test]
fn self_consistent_fee_and_lp_mutations_reach_local_invariance_guards() {
    let fixture = fixture();

    let mut fee_post = fixture.post_state.clone();
    fee_post.fee_accumulator.dust += 1;
    assert_local_snapshot_reject(
        &fixture.pre_state,
        &fee_post,
        &fixture.journal,
        "fee accumulator changed",
    );

    let mut lp_post = fixture.post_state.clone();
    lp_post.lp_balances[0].amount += 1;
    assert_local_snapshot_reject(
        &fixture.pre_state,
        &lp_post,
        &fixture.journal,
        "LP balances changed",
    );
}

#[test]
fn self_consistent_pool_mutations_reach_local_shape_guards() {
    let fixture = fixture();

    let mut same_direction_post = fixture.post_state.clone();
    same_direction_post.pools[0].reserve1 = fixture.pre_state.pools[0].reserve1 + 1_992;
    assert_local_snapshot_reject(
        &fixture.pre_state,
        &same_direction_post,
        &fixture.journal,
        "pool reserves do not encode one exact swap",
    );

    let mut two_pool_pre = fixture.pre_state.clone();
    let mut two_pool_post = fixture.post_state.clone();
    let mut second_pre = fixture.pre_state.pools[0].clone();
    second_pre.asset0 = format!("0x{}", "33".repeat(32));
    second_pre.asset1 = format!("0x{}", "44".repeat(32));
    second_pre.pool_id = cpmm_pool_id(&second_pre.asset0, &second_pre.asset1, second_pre.fee_bps);
    second_pre.reserve0 = 700_000;
    second_pre.reserve1 = 900_000;
    let mut second_post = second_pre.clone();
    second_post.reserve0 += 500;
    second_post.reserve1 -= 499;
    two_pool_pre.pools.push(second_pre);
    two_pool_post.pools.push(second_post);
    assert_local_snapshot_reject(
        &two_pool_pre,
        &two_pool_post,
        &fixture.journal,
        "multiple pools changed",
    );
}

#[test]
fn self_consistent_account_mutations_reach_local_direction_guards() {
    let fixture = fixture();

    let mut wrong_amount_post = fixture.post_state.clone();
    wrong_amount_post.balances[0].amount -= 1;
    assert_local_snapshot_reject(
        &fixture.pre_state,
        &wrong_amount_post,
        &fixture.journal,
        "input account debit mismatch",
    );

    let mut third_pre = fixture.pre_state.clone();
    let mut third_post = fixture.post_state.clone();
    let mut extra_pre = fixture.pre_state.balances[0].clone();
    extra_pre.pubkey = format!("0x{}", "bb".repeat(48));
    extra_pre.amount = 100;
    let mut extra_post = extra_pre.clone();
    extra_post.amount = 99;
    third_pre.balances.push(extra_pre);
    third_post.balances.push(extra_post);
    assert_local_snapshot_reject(
        &third_pre,
        &third_post,
        &fixture.journal,
        "account balance change count is not two",
    );

    let mut non_sender_pre = fixture.pre_state.clone();
    let mut non_sender_post = fixture.post_state.clone();
    non_sender_post.balances[0].amount = non_sender_pre.balances[0].amount;
    let mut other_pre = fixture.pre_state.balances[0].clone();
    other_pre.pubkey = format!("0x{}", "bb".repeat(48));
    other_pre.amount = 2_000;
    let mut other_post = other_pre.clone();
    other_post.amount = 1_000;
    non_sender_pre.balances.push(other_pre);
    non_sender_post.balances.push(other_post);
    assert_local_snapshot_reject(
        &non_sender_pre,
        &non_sender_post,
        &fixture.journal,
        "input debit is not the journal sender",
    );
}

#[test]
fn source_authorization_nonce_must_match_the_reopened_ingress_nonce() {
    let fixture = fixture();
    let opening = fixture_opening(&fixture);
    let source = source_plan(
        &opening,
        SourcePlanOverridesV1 {
            authorization_nonce: Some(u64::from(opening.ingress_nonce()) + 1),
            ..SourcePlanOverridesV1::NONE
        },
    );
    assert_eq!(
        derive_expected_spot_v7_settlement_effect_plan_v1(&opening, &source).unwrap_err(),
        SpotSettlementV7EffectBindingErrorV1::ActionNonceMismatch
    );
}

#[test]
fn source_profile_and_derived_plan_resubmission_reject() {
    let fixture = fixture();
    let opening = fixture_opening(&fixture);
    let wrong_source = source_plan(
        &opening,
        SourcePlanOverridesV1 {
            extra_cell_write: true,
            ..SourcePlanOverridesV1::NONE
        },
    );
    assert_eq!(
        derive_expected_spot_v7_settlement_effect_plan_v1(&opening, &wrong_source).unwrap_err(),
        SpotSettlementV7EffectBindingErrorV1::SourcePlanProfile("one opaque cell write")
    );

    let source = source_plan(&opening, SourcePlanOverridesV1::NONE);
    let derived = derive_expected_spot_v7_settlement_effect_plan_v1(&opening, &source).unwrap();
    assert_eq!(
        bind_spot_settlement_effect_plan_v1(opening, &derived).unwrap_err(),
        SpotSettlementV7EffectBindingErrorV1::SourcePlanProfile("one opaque cell write")
    );
}

#[test]
fn authenticated_lineage_changes_are_committed_into_plan_b() {
    let fixture = fixture();
    let opening = fixture_opening(&fixture);
    let first = source_plan(&opening, SourcePlanOverridesV1::NONE);
    let second = source_plan(
        &opening,
        SourcePlanOverridesV1 {
            authorization_subject_seed: 0x44,
            ..SourcePlanOverridesV1::NONE
        },
    );
    let first_v7 = derive_expected_spot_v7_settlement_effect_plan_v1(&opening, &first).unwrap();
    let second_v7 = derive_expected_spot_v7_settlement_effect_plan_v1(&opening, &second).unwrap();
    assert_ne!(
        first_v7.economic_action_batch().actions()[0]
            .action_id()
            .unwrap(),
        second_v7.economic_action_batch().actions()[0]
            .action_id()
            .unwrap()
    );
    assert_ne!(
        first_v7.canonical_commitment().unwrap(),
        second_v7.canonical_commitment().unwrap()
    );
}

#[test]
fn binding_journal_decoder_is_exact_and_profile_bound() {
    let seed = binding_journal_bytes();
    assert!(matches!(
        decode_exact_spot_settlement_v7_effect_binding_journal_v1(&seed[..seed.len() - 1]),
        Err(SpotSettlementV7EffectBindingErrorV1::JournalLength { .. })
    ));
    let mut trailing = seed.clone();
    trailing.push(0);
    assert!(matches!(
        decode_exact_spot_settlement_v7_effect_binding_journal_v1(&trailing),
        Err(SpotSettlementV7EffectBindingErrorV1::JournalLength { .. })
    ));
    let mut version = seed.clone();
    version[..2].copy_from_slice(&2_u16.to_be_bytes());
    assert_eq!(
        decode_exact_spot_settlement_v7_effect_binding_journal_v1(&version).unwrap_err(),
        SpotSettlementV7EffectBindingErrorV1::InvalidJournalVersion(2)
    );
    let mut profile = seed.clone();
    profile[2..34].fill(0x44);
    assert_eq!(
        decode_exact_spot_settlement_v7_effect_binding_journal_v1(&profile).unwrap_err(),
        SpotSettlementV7EffectBindingErrorV1::UnexpectedCompatibilityProfile
    );
    let mut scheme = seed;
    scheme[34..66].fill(0x55);
    assert_eq!(
        decode_exact_spot_settlement_v7_effect_binding_journal_v1(&scheme).unwrap_err(),
        SpotSettlementV7EffectBindingErrorV1::UnexpectedStateRootScheme
    );
}

#[test]
fn binding_journal_boundary_frontier_is_fail_closed_and_ordered() {
    let seed = binding_journal_bytes();
    for truncated_length in 0..seed.len() {
        assert!(matches!(
            decode_exact_spot_settlement_v7_effect_binding_journal_v1(&seed[..truncated_length]),
            Err(SpotSettlementV7EffectBindingErrorV1::JournalLength { .. })
        ));
    }
    for suffix_length in 1..=3 {
        let mut extended = seed.clone();
        extended.resize(seed.len() + suffix_length, 0xa5);
        assert!(matches!(
            decode_exact_spot_settlement_v7_effect_binding_journal_v1(&extended),
            Err(SpotSettlementV7EffectBindingErrorV1::JournalLength { .. })
        ));
    }
    for field_index in 0..12 {
        let start = 2 + field_index * 32;
        let mut zero_identity = seed.clone();
        zero_identity[start..start + 32].fill(0);
        assert!(matches!(
            decode_exact_spot_settlement_v7_effect_binding_journal_v1(&zero_identity),
            Err(SpotSettlementV7EffectBindingErrorV1::DerivedCommitment(_))
        ));
    }

    let mut length_and_version = seed.clone();
    length_and_version[..2].copy_from_slice(&2_u16.to_be_bytes());
    length_and_version.push(0);
    assert!(matches!(
        decode_exact_spot_settlement_v7_effect_binding_journal_v1(&length_and_version),
        Err(SpotSettlementV7EffectBindingErrorV1::JournalLength { .. })
    ));
    let mut profile_and_scheme = seed;
    profile_and_scheme[2..34].fill(0x44);
    profile_and_scheme[34..66].fill(0x55);
    assert_eq!(
        decode_exact_spot_settlement_v7_effect_binding_journal_v1(&profile_and_scheme).unwrap_err(),
        SpotSettlementV7EffectBindingErrorV1::UnexpectedCompatibilityProfile
    );
}

#[test]
fn binding_journal_has_a_fixed_canonical_byte_and_hash_vector() {
    let fixture = fixture();
    let opening = fixture_opening(&fixture);
    let source = source_plan(&opening, SourcePlanOverridesV1::NONE);
    let bound = bind_spot_settlement_effect_plan_v1(opening, &source).unwrap();
    let bytes = encode_spot_settlement_v7_effect_binding_journal_v1(bound.journal());

    assert_eq!(
        encode_hex(&bytes),
        concat!(
            "0001c702e1e2f07cddbc5fccbfaeb39a2612d9ed6fb5fd6489a1d70c39f21d786404",
            "0e7bd17d69eebebdd30cf3b3901afd5e821050a808d2eef73b0835a4176396a6",
            "554a6cff618e1c08d2526f57d04b5e1c2f65736d10c788f155853f053178b90e",
            "faf08051ab4932f654b6f896289e890206b1e235e4bce33508b27b07cf2bad06",
            "c795554c97e28d7537bbeafcf6c7e469aaf8b2b5225ae058f7e76ecb2f61bb6c",
            "e7750210d2ebbcad884ec908e5f371405a53c423d5adbf3bc340c74dc709787b",
            "9a52703d28d50b23a7c4d9548562a1d128c8b37d233345f8c30fccb64447c1e1",
            "888ae43b877d752b5dc1b837bfcdccb38ccdb02538424fd562fbfd4dd6fa1630",
            "b9d415c3c6a6aa3eb57b861b6a2cc2c09a07826e8d7b64e6d7450f804f36815f",
            "164ac66f19c92846fa37c9a8eb7358d04b329d704b79cf7dc92bc7711b06beb8",
            "72452b05cb806b32ae8c6b9a486967f4833784266b7aa03e1030846d2ad8d232",
            "5353535353535353535353535353535353535353535353535353535353535353",
        )
    );
    assert_eq!(
        encode_hex(Sha256::digest(&bytes).as_slice()),
        "67aed46af3e39cc79d04fbf097202eb975a9f54e24b96d56ef3363e53918e45d"
    );
    assert_eq!(
        encode_hex(bound.journal().canonical_commitment().unwrap().as_bytes()),
        "c04dfecd773117c5b0291fa93bbd298739ef7369ce754ae56646bc67be423fb9"
    );
    assert_eq!(
        encode_hex(source.canonical_commitment().unwrap().as_bytes()),
        "faf08051ab4932f654b6f896289e890206b1e235e4bce33508b27b07cf2bad06"
    );
    assert_eq!(
        encode_hex(bound.plan().canonical_commitment().unwrap().as_bytes()),
        "c795554c97e28d7537bbeafcf6c7e469aaf8b2b5225ae058f7e76ecb2f61bb6c"
    );
    assert_eq!(
        encode_hex(bound.opening().cell_transitions_root().as_bytes()),
        "e7750210d2ebbcad884ec908e5f371405a53c423d5adbf3bc340c74dc709787b"
    );
    assert_eq!(
        encode_hex(
            bound.plan().economic_action_batch().actions()[0]
                .action_id()
                .unwrap()
                .as_bytes(),
        ),
        "b9d415c3c6a6aa3eb57b861b6a2cc2c09a07826e8d7b64e6d7450f804f36815f"
    );
    assert_eq!(
        encode_hex(
            bound.plan().economic_action_batch().actions()[0]
                .authorization_grant_spend()
                .unwrap()
                .as_bytes(),
        ),
        "6a4eced6b1b60c0afe95e19adeb472be183c132338d3b573a378305c8d8db32d"
    );
}

fn binding_journal_bytes() -> Vec<u8> {
    let fixture = fixture();
    let opening = fixture_opening(&fixture);
    let source = source_plan(&opening, SourcePlanOverridesV1::NONE);
    let bound = bind_spot_settlement_effect_plan_v1(opening, &source).unwrap();
    encode_spot_settlement_v7_effect_binding_journal_v1(bound.journal())
}

fn fixture() -> FixtureV1 {
    let v5: Value = serde_json::from_str(V5_FIXTURE).unwrap();
    let v7: Value = serde_json::from_str(V7_FIXTURE).unwrap();
    let pre_state = serde_json::from_value(v5["pre_state"].clone()).unwrap();
    let post_state = serde_json::from_value(v5["post_state"].clone()).unwrap();
    let journal_bytes = decode_hex(v7["journal_hex"].as_str().unwrap());
    let journal = decode_exact_spot_state_root_v7_semantic_journal_v1(&journal_bytes).unwrap();
    FixtureV1 {
        journal,
        pre_state,
        post_state,
    }
}

fn fixture_opening(fixture: &FixtureV1) -> SpotSettlementStateEffectOpeningV1 {
    derive_spot_settlement_state_effect_opening_v1(
        &fixture.journal,
        &fixture.pre_state,
        &fixture.post_state,
    )
    .unwrap()
}

fn assert_local_snapshot_reject(
    pre_state: &DexSnapshotV1,
    post_state: &DexSnapshotV1,
    base_journal: &SpotStateRootV7SemanticJournalV1,
    expected_reason: &'static str,
) {
    let journal = self_consistent_journal(pre_state, post_state, base_journal);
    assert_eq!(
        derive_spot_settlement_state_effect_opening_v1(&journal, pre_state, post_state)
            .unwrap_err(),
        SpotSettlementV7EffectBindingErrorV1::UnsupportedStateDelta(expected_reason)
    );
}

fn self_consistent_journal(
    pre_state: &DexSnapshotV1,
    post_state: &DexSnapshotV1,
    base_journal: &SpotStateRootV7SemanticJournalV1,
) -> SpotStateRootV7SemanticJournalV1 {
    let sender = format!("0x{}", encode_hex(&base_journal.sender_pubkey()));
    let ingress_nonce = u64::from(base_journal.ingress_nonce());
    let expected_source = ExpectedLegacySpotCommitmentsV1::new(
        sha256_canonical_dex_snapshot_v1(pre_state),
        sha256_canonical_dex_snapshot_v1(post_state),
        nonce_root(&sender, ingress_nonce),
        nonce_root(&sender, ingress_nonce + 1),
    );
    let (pre_root, post_root) = probe_state_roots(
        pre_state,
        post_state,
        &sender,
        ingress_nonce,
        expected_source,
    );
    let source =
        LegacySpotSourceProjectionV7::new(pre_state, &sender, ingress_nonce, expected_source);
    let host =
        BoundedSpotStateRootV7HostInputV1::new(post_state.clone(), pre_root, post_root).unwrap();
    compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1(&source, &host)
        .unwrap()
}

fn probe_state_roots(
    pre_state: &DexSnapshotV1,
    post_state: &DexSnapshotV1,
    sender: &str,
    ingress_nonce: u64,
    expected_source: ExpectedLegacySpotCommitmentsV1,
) -> ([u8; 32], [u8; 32]) {
    let pre_nonces = [NonceEntryV1 {
        pubkey: sender.into(),
        next_nonce: ingress_nonce,
    }];
    let probe = |pre_root, post_root| {
        verify_restricted_spot_state_root_v5_transition_v1(
            RestrictedSpotStateRootV5ProfileV1::governed(),
            RestrictedSpotStateRootV5TransitionInputV1::new(
                pre_state,
                post_state,
                &pre_nonces,
                sender,
                ingress_nonce,
                expected_source,
                ExpectedSpotStateRootsV5::new(pre_root, post_root),
            ),
        )
    };
    let pre_root = match probe([0; 32], [0; 32]).unwrap_err() {
        RestrictedSpotStateRootV5BridgeError::PreStateRootMismatch { actual, .. } => actual,
        error => panic!("unexpected pre-root probe result: {error}"),
    };
    let post_root = match probe(pre_root, [0; 32]).unwrap_err() {
        RestrictedSpotStateRootV5BridgeError::PostStateRootMismatch { actual, .. } => actual,
        error => panic!("unexpected post-root probe result: {error}"),
    };
    (pre_root, post_root)
}

fn nonce_root(sender: &str, next_nonce: u64) -> [u8; 32] {
    NonceStateV1::from_entries(vec![NonceEntryV1 {
        pubkey: sender.into(),
        next_nonce,
    }])
    .unwrap()
    .root()
}

fn cpmm_pool_id(asset0: &str, asset1: &str, fee_bps: u32) -> String {
    let mut hasher = Sha256::new();
    hasher.update(b"TauSwapPool");
    hasher.update(asset0.as_bytes());
    hasher.update(asset1.as_bytes());
    hasher.update(fee_bps.to_string().as_bytes());
    hasher.update(b"CPMM");
    hasher.update(b"");
    format!("0x{}", encode_hex(&hasher.finalize()))
}

fn source_plan(
    opening: &SpotSettlementStateEffectOpeningV1,
    overrides: SourcePlanOverridesV1,
) -> SettlementEffectPlanV2 {
    let source_pre_root = commitment(0x31);
    let source_record = EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
        application_id: ApplicationIdV3::new([1; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        action_type_id: EconomicActionTypeIdV1::new([3; 32]).unwrap(),
        authorization_subject_id: AuthorizationSubjectIdV1::new(
            [overrides.authorization_subject_seed; 32],
        )
        .unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([5; 32]).unwrap(),
        authorization_nonce: overrides
            .authorization_nonce
            .unwrap_or(u64::from(opening.ingress_nonce())),
        valid_from_epoch: 9,
        valid_through_epoch: 9,
        pre_state_root: source_pre_root,
        action_semantics_hash: commitment(0x32),
        effect_commitment: commitment(0x33),
        consumed_object_ids: vec![commitment(0x34)],
    })
    .unwrap();
    let source_action = AuthorizedEconomicActionV1::new(
        source_record,
        AuthorizationGrantIdV1::new([6; 32]).unwrap(),
    )
    .unwrap();
    let source_action_id = source_action.action_id().unwrap();
    let source_batch = EconomicActionBatchV1::new(9, source_pre_root, vec![source_action]).unwrap();
    let mut writes = vec![source_cell_write(source_action_id, 0x41)];
    if overrides.extra_cell_write {
        writes.push(source_cell_write(source_action_id, 0x42));
    }
    let source_effect = AssetEffectV2::new(AssetEffectInputV2 {
        kind: AssetEffectKindV2::OrdinaryTransfer,
        economic_action_id: source_action_id,
        asset_id: commitment(0x51),
        debit_atoms: 10,
        credit_atoms: 10,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_scope_id: None,
        action_authorization_binding: None,
    })
    .unwrap();
    SettlementEffectPlanV2::new(SettlementEffectPlanInputV2 {
        source_semantic_journal_hash: commitment(0x52),
        public_policy_hash: commitment(0x53),
        post_state_root: commitment(0x54),
        economic_action_batch: source_batch,
        ledger_cell_writes: writes,
        asset_effects: vec![source_effect],
        message_effects: vec![],
        carry_effects: vec![],
        reward_effects: vec![],
    })
    .unwrap()
}

fn source_cell_write(
    action_id: zenodex_zrpf_protocol_v3::EconomicActionIdV1,
    seed: u8,
) -> LedgerCellWriteV2 {
    LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
        economic_action_id: action_id,
        cell_key: commitment(seed),
        pre_value_hash: ValueHashV2::new([seed.wrapping_add(1); 32]),
        post_value_hash: ValueHashV2::new([seed.wrapping_add(2); 32]),
    })
    .unwrap()
}

fn commitment(byte: u8) -> CommitmentV3 {
    CommitmentV3::new([byte; 32]).unwrap()
}

fn decode_hex(value: &str) -> Vec<u8> {
    value
        .strip_prefix("0x")
        .unwrap()
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let pair = core::str::from_utf8(pair).unwrap();
            u8::from_str_radix(pair, 16).unwrap()
        })
        .collect()
}

fn encode_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}
