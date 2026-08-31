use serde_json::Value;

use super::*;
use crate::asset_transfer_types::AssetTransferCommandV2;
use crate::canonical::{decode_canonical_v2, AbiErrorV2, ValidateCanonicalV2};
use crate::effects::ExternalOutboxEnqueueV2;
use crate::managed_asset_lifecycle_types::ManagedAssetLifecycleCommandV2;

const GOLDEN: &str =
    include_str!("../../../tests/data/global_settlement_abi_v2_asset_lane_coordinator_golden.json");

fn vector_bytes(case_name: &str, vector_name: &str) -> Vec<u8> {
    let fixture: Value = serde_json::from_str(GOLDEN).expect("fixture must parse");
    serde_json::to_vec(&fixture["accepted"][case_name]["vectors"][vector_name]["canonical"])
        .expect("vector must serialize")
}

fn typed_vector<T>(case_name: &str, vector_name: &str) -> T
where
    T: serde::de::DeserializeOwned + serde::Serialize + ValidateCanonicalV2,
{
    decode_canonical_v2(&vector_bytes(case_name, vector_name)).expect("vector must decode")
}

fn transfer_subject() -> (AssetLaneContextV2, AssetLaneStateV2, AssetTransferCommandV2) {
    (
        typed_vector("transfer", "context"),
        typed_vector("transfer", "pre_state"),
        typed_vector("transfer", "command"),
    )
}

fn managed_subject() -> (
    AssetLaneContextV2,
    AssetLaneStateV2,
    ManagedAssetLifecycleCommandV2,
) {
    (
        typed_vector("managed_issue", "context"),
        typed_vector("managed_issue", "pre_state"),
        typed_vector("managed_issue", "command"),
    )
}

fn assert_coordinator_noop(
    result: AssetLaneResultV2,
    state: &AssetLaneStateV2,
    route: AssetLaneRouteV2,
    code: AssetLaneCoordinatorRejectCodeV2,
) {
    let AssetLaneResultV2::Rejected(rejected) = result else {
        panic!("mutated coordinator candidate unexpectedly accepted")
    };
    assert_eq!(rejected.route(), route);
    assert_eq!(rejected.code(), AssetLaneRejectCodeV2::Coordinator(code));
    assert_eq!(rejected.pre_state_root(), rejected.post_state_root());
    assert_eq!(
        rejected.pre_state_root(),
        &state.state_root().expect("state root")
    );
    assert!(rejected.effects().is_empty());
}

#[test]
fn forged_leaf_external_outbox_is_a_candidate_binding_noop() {
    let (context, state, command) = transfer_subject();
    let leaf = transition_asset_transfer_v2(
        &context.transfer_context(),
        &state.transfer_leaf_state(),
        &command,
    )
    .expect("leaf must execute");
    let AssetTransferResultV2::Accepted(mut accepted) = leaf else {
        panic!("fixture leaf must accept")
    };
    accepted
        .effects
        .external_outbox_enqueue
        .push(ExternalOutboxEnqueueV2 {
            effect_id: RootV2::parse(
                "0x0000000000000000000000000000000000000000000000000000000000000011",
                "test effect id",
                false,
            )
            .expect("root"),
            destination_id: "external:adapter".to_owned(),
            payload_hash: RootV2::parse(
                "0x0000000000000000000000000000000000000000000000000000000000000012",
                "test payload hash",
                false,
            )
            .expect("root"),
            adapter_profile_root: RootV2::parse(
                "0x0000000000000000000000000000000000000000000000000000000000000013",
                "test adapter root",
                false,
            )
            .expect("root"),
        });
    accepted.module_journal.effect_plan_root = accepted
        .effects
        .effect_plan_root()
        .expect("mutated effect root");
    accepted
        .validate()
        .expect("leaf wrapper does not own the coordinator outbox rule");

    let result = compose_candidate(
        &context,
        &state,
        AssetLaneRouteV2::TRANSFER,
        LeafAcceptedV2::Transfer(accepted),
    )
    .expect("coordinator must evaluate");

    assert_coordinator_noop(
        result,
        &state,
        AssetLaneRouteV2::TRANSFER,
        AssetLaneCoordinatorRejectCodeV2::CANDIDATE_BINDING_MISMATCH,
    );
}

#[test]
fn forged_leaf_context_binding_is_a_candidate_binding_noop() {
    let (context, state, command) = transfer_subject();
    let leaf = transition_asset_transfer_v2(
        &context.transfer_context(),
        &state.transfer_leaf_state(),
        &command,
    )
    .expect("leaf must execute");
    let AssetTransferResultV2::Accepted(mut accepted) = leaf else {
        panic!("fixture leaf must accept")
    };
    accepted.module_journal.chain_id = "forged-chain".to_owned();
    accepted
        .validate()
        .expect("leaf-local wrapper remains structurally valid");

    let result = compose_candidate(
        &context,
        &state,
        AssetLaneRouteV2::TRANSFER,
        LeafAcceptedV2::Transfer(accepted),
    )
    .expect("coordinator must evaluate");

    assert_coordinator_noop(
        result,
        &state,
        AssetLaneRouteV2::TRANSFER,
        AssetLaneCoordinatorRejectCodeV2::CANDIDATE_BINDING_MISMATCH,
    );
}

#[test]
fn route_to_leaf_projection_mismatch_is_a_named_noop() {
    let (context, state, command) = managed_subject();
    let leaf = transition_managed_asset_lifecycle_v2(
        &context.managed_context(),
        &state.managed_leaf_state(),
        &command,
    )
    .expect("leaf must execute");
    let ManagedAssetLifecycleResultV2::Accepted(accepted) = leaf else {
        panic!("fixture leaf must accept")
    };

    let result = compose_candidate(
        &context,
        &state,
        AssetLaneRouteV2::TRANSFER,
        LeafAcceptedV2::ManagedLifecycle(accepted),
    )
    .expect("coordinator must evaluate");

    assert_coordinator_noop(
        result,
        &state,
        AssetLaneRouteV2::TRANSFER,
        AssetLaneCoordinatorRejectCodeV2::PROJECTION_MISMATCH,
    );
}

#[test]
fn hostile_aggregate_accepted_parts_cannot_admit_an_external_outbox() {
    let (context, state, command) = transfer_subject();
    let result = transition_asset_lane_v2(&context, &state, &AssetLaneCommandV2::Transfer(command))
        .expect("coordinator must execute");
    let AssetLaneResultV2::Accepted(accepted) = result else {
        panic!("fixture coordinator must accept")
    };
    let mut effects = accepted.effects().clone();
    effects
        .external_outbox_enqueue
        .push(ExternalOutboxEnqueueV2 {
            effect_id: RootV2::parse(
                "0x0000000000000000000000000000000000000000000000000000000000000021",
                "test effect id",
                false,
            )
            .expect("root"),
            destination_id: "external:adapter".to_owned(),
            payload_hash: RootV2::parse(
                "0x0000000000000000000000000000000000000000000000000000000000000022",
                "test payload hash",
                false,
            )
            .expect("root"),
            adapter_profile_root: RootV2::parse(
                "0x0000000000000000000000000000000000000000000000000000000000000023",
                "test adapter root",
                false,
            )
            .expect("root"),
        });

    assert_eq!(
        AssetLaneAcceptedV2::new(
            accepted.route(),
            accepted.source_leaf_journal_root().clone(),
            accepted.post_state().clone(),
            effects,
            accepted.module_journal().clone(),
        ),
        Err(AbiErrorV2::InvalidBinding("asset lane accepted bindings"))
    );
}
