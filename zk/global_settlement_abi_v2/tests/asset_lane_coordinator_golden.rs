#[path = "support/asset_lane_coordinator.rs"]
mod support;

use support::{command, command_bytes, fixture, transfer_reject_codes, typed_vector, vector_bytes};
use zenodex_global_settlement_abi_v2::{
    canonical_bytes_v2, hash_global_v2, transition_asset_lane_v2, AssetLaneContextV2,
    AssetLaneResultV2, AssetLaneStateV2, GlobalEconomicEffectPlanV2, LaneIdV2,
    LaneModuleTransitionJournalV2, ALL_ASSET_LANE_COORDINATOR_REJECT_CODES_V2,
    ALL_MANAGED_ASSET_LIFECYCLE_REJECT_CODES_V2, MAX_ASSET_LANE_ASSETS_V2,
    MAX_ASSET_LANE_BALANCE_ROWS_V2, MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2,
};

const PLAN_SHA256: &str = "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f";

fn assert_fixture_metadata(fixture: &support::Fixture) {
    assert_eq!(
        fixture.fixture_schema,
        "zenodex/global-settlement-abi-v2-asset-lane-coordinator-golden/v1"
    );
    assert_eq!(fixture.authority, "NONE");
    assert_eq!(fixture.profile_authentication, "SHADOW");
    assert_eq!(fixture.plan_sha256, PLAN_SHA256);
    assert_eq!(fixture.limits.max_assets, MAX_ASSET_LANE_ASSETS_V2);
    assert_eq!(
        fixture.limits.max_balance_rows,
        MAX_ASSET_LANE_BALANCE_ROWS_V2
    );
    assert_eq!(
        fixture.limits.max_state_canonical_bytes,
        MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2
    );
    assert_eq!(fixture.python_source_sha256.len(), 6);
    assert!(fixture
        .python_source_sha256
        .values()
        .all(|digest| digest.len() == 64));
}

struct AcceptedSubject {
    context: AssetLaneContextV2,
    pre_state: AssetLaneStateV2,
    expected_post: AssetLaneStateV2,
    expected_effects: GlobalEconomicEffectPlanV2,
    expected_journal: LaneModuleTransitionJournalV2,
    command: zenodex_global_settlement_abi_v2::AssetLaneCommandV2,
}

fn accepted_subject(case: &support::AcceptedCase) -> AcceptedSubject {
    AcceptedSubject {
        context: typed_vector(&case.vectors, "context"),
        pre_state: typed_vector(&case.vectors, "pre_state"),
        expected_post: typed_vector(&case.vectors, "post_state"),
        expected_effects: typed_vector(&case.vectors, "effect_plan"),
        expected_journal: typed_vector(&case.vectors, "module_journal"),
        command: command(&case.vectors, &case.command_type),
    }
}

#[test]
fn fixture_scope_plan_sources_reject_registries_and_nonclaims_are_exact() {
    let fixture = fixture();
    assert_fixture_metadata(&fixture);
    assert_eq!(
        fixture.coordinator_reject_codes,
        ALL_ASSET_LANE_COORDINATOR_REJECT_CODES_V2.map(|code| code.as_str().to_owned())
    );
    assert_eq!(fixture.transfer_reject_codes, transfer_reject_codes());
    assert_eq!(
        fixture.managed_reject_codes,
        ALL_MANAGED_ASSET_LIFECYCLE_REJECT_CODES_V2.map(|code| code.as_str().to_owned())
    );
    assert_eq!(
        fixture
            .accepted
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["managed_issue", "transfer"]
    );
    assert_eq!(
        fixture.nonclaims,
        [
            "no RISC0 circuit or receipt",
            "no runtime mount, migration, or UI",
            "no settlement, release, or production authority",
        ]
    );
}

fn assert_expected_roots(case: &support::AcceptedCase, subject: &AcceptedSubject) {
    assert_eq!(
        hash_global_v2("asset-lane-context-vector-v2", &subject.context).expect("context root"),
        case.vectors["context"].expected_root
    );
    assert_eq!(
        subject.pre_state.state_root().expect("pre-state root"),
        case.vectors["pre_state"].expected_root
    );
    assert_eq!(
        subject.expected_post.state_root().expect("post-state root"),
        case.vectors["post_state"].expected_root
    );
    assert_eq!(
        subject
            .expected_effects
            .effect_plan_root()
            .expect("effect root"),
        case.vectors["effect_plan"].expected_root
    );
    assert_eq!(
        subject
            .expected_journal
            .journal_root()
            .expect("journal root"),
        case.vectors["module_journal"].expected_root
    );
}

fn assert_aggregate_bindings(
    context: &AssetLaneContextV2,
    pre_state: &AssetLaneStateV2,
    accepted: &zenodex_global_settlement_abi_v2::AssetLaneAcceptedV2,
) {
    let occurrence_id = context
        .occurrence
        .as_ref()
        .expect("accepted occurrence")
        .occurrence_id()
        .expect("occurrence id");
    assert_eq!(accepted.effects().lane_writes.len(), 1);
    assert_eq!(
        accepted.effects().lane_writes[0].lane_id,
        LaneIdV2::ASSET_TRANSFER
    );
    assert_eq!(
        accepted.effects().lane_writes[0].pre_root,
        pre_state.state_root().expect("pre-state root")
    );
    assert_eq!(
        accepted.effects().lane_writes[0].post_root,
        accepted.post_state().state_root().expect("post-state root")
    );
    assert_eq!(accepted.effects().occurrence_consumptions, [occurrence_id]);
    assert!(accepted.effects().external_outbox_enqueue.is_empty());
    assert!(accepted.module_journal().private_port_root.is_zero());
    assert!(accepted
        .module_journal()
        .terminal_obligations_root
        .is_zero());
    assert!(accepted
        .module_journal()
        .oracle_occurrence_plan_root
        .is_zero());
}

fn assert_canonical_bytes(
    case: &support::AcceptedCase,
    subject: &AcceptedSubject,
    accepted: &zenodex_global_settlement_abi_v2::AssetLaneAcceptedV2,
) {
    for (name, bytes) in [
        (
            "context",
            canonical_bytes_v2(&subject.context).expect("context bytes"),
        ),
        (
            "pre_state",
            canonical_bytes_v2(&subject.pre_state).expect("pre-state bytes"),
        ),
        ("command", command_bytes(&subject.command)),
        (
            "post_state",
            canonical_bytes_v2(accepted.post_state()).expect("post-state bytes"),
        ),
        (
            "effect_plan",
            canonical_bytes_v2(accepted.effects()).expect("effect bytes"),
        ),
        (
            "module_journal",
            canonical_bytes_v2(accepted.module_journal()).expect("journal bytes"),
        ),
    ] {
        assert_eq!(bytes, vector_bytes(&case.vectors, name));
    }
}

fn assert_accepted_case(name: &str, case: &support::AcceptedCase) {
    let subject = accepted_subject(case);
    assert_expected_roots(case, &subject);
    let first = transition_asset_lane_v2(&subject.context, &subject.pre_state, &subject.command)
        .expect("golden coordinator transition must execute");
    let second = transition_asset_lane_v2(&subject.context, &subject.pre_state, &subject.command)
        .expect("replayed coordinator transition must execute");
    assert_eq!(first, second, "{name} must be deterministic");
    let AssetLaneResultV2::Accepted(accepted) = first else {
        panic!("golden {name} unexpectedly rejected");
    };
    assert_eq!(accepted.route().as_str(), case.route);
    assert_eq!(
        accepted.source_leaf_journal_root(),
        &case.source_leaf_journal_root
    );
    assert_eq!(accepted.receipt_root(), &case.receipt_root);
    assert_eq!(accepted.post_state(), &subject.expected_post);
    assert_eq!(accepted.effects(), &subject.expected_effects);
    assert_eq!(accepted.module_journal(), &subject.expected_journal);
    assert_eq!(accepted.production_authority(), "NONE");
    assert_eq!(accepted.profile_authentication(), "SHADOW");
    assert_aggregate_bindings(&subject.context, &subject.pre_state, &accepted);
    assert_canonical_bytes(case, &subject, &accepted);
}

#[test]
fn python_and_rust_share_accepted_transfer_and_managed_bytes_roots_and_results() {
    let fixture = fixture();
    for (name, case) in &fixture.accepted {
        assert_accepted_case(name, case);
    }
}
