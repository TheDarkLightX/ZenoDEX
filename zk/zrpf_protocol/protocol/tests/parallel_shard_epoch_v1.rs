use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    canonical_empty_carry_queue_root_v1, canonical_empty_cross_shard_inbox_root_v1,
    canonical_empty_cross_shard_outbox_root_v1, decode_exact_parallel_shard_epoch_v1,
    encode_parallel_shard_epoch_v1, ApplicationIdV3, CanonicalShardStateMapV1, CommitmentV3,
    DomainIdV3, GovernedShardSetV1, NodeScopeInputV3, NodeScopeV3, ParallelShardEpochErrorV1,
    ParallelShardEpochInputV1, ParallelShardEpochV1, ProfileIdV3, ShardIdV1,
    ShardTransitionInputV1, MAX_PARALLEL_SHARD_EPOCH_BYTES_V1,
};

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed; 32]).unwrap()
}

fn profile(seed: u8) -> ProfileIdV3 {
    ProfileIdV3::new([seed; 32]).unwrap()
}

fn shard(seed: u8) -> ShardIdV1 {
    ShardIdV1::new([seed; 32]).unwrap()
}

fn scope(seed: u8) -> NodeScopeV3 {
    NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new([seed; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([seed.wrapping_add(1); 32]).unwrap(),
        epoch_start: 17,
        epoch_end: 17,
        public_policy_hash: commitment(seed.wrapping_add(2)),
        feature_suite_hash: commitment(seed.wrapping_add(3)),
        dependency_lock_hash: commitment(seed.wrapping_add(4)),
        toolchain_lock_hash: commitment(seed.wrapping_add(5)),
    })
    .unwrap()
}

fn transition(
    shard_id: ShardIdV1,
    root_seed: u8,
    scope_hash: CommitmentV3,
    semantic_profile_id: ProfileIdV3,
    state_root_scheme_id: CommitmentV3,
) -> ShardTransitionInputV1 {
    ShardTransitionInputV1 {
        shard_id,
        scope_hash,
        semantic_profile_id,
        state_root_scheme_id,
        local_pre_state_root: commitment(root_seed),
        local_post_state_root: commitment(root_seed.wrapping_add(1)),
        semantic_value_root: commitment(root_seed.wrapping_add(2)),
        shard_action_nullifiers_root: commitment(root_seed.wrapping_add(3)),
        cross_shard_outbox_root: canonical_empty_cross_shard_outbox_root_v1().unwrap(),
        cross_shard_inbox_root: canonical_empty_cross_shard_inbox_root_v1().unwrap(),
        carry_queue_pre_root: canonical_empty_carry_queue_root_v1().unwrap(),
        carry_queue_post_root: canonical_empty_carry_queue_root_v1().unwrap(),
    }
}

fn input(seed: u8, proof_tree_seed: u8) -> ParallelShardEpochInputV1 {
    let scope = scope(seed.wrapping_add(20));
    let scope_hash = scope.canonical_hash().unwrap();
    let semantic_profile_id = profile(10);
    let state_root_scheme_id = commitment(11);
    let governed_shard_ids = [shard(1), shard(2)];
    ParallelShardEpochInputV1 {
        scope,
        semantic_profile_id,
        state_root_scheme_id,
        governed_shard_ids,
        shard_transitions: [
            transition(
                governed_shard_ids[0],
                seed.wrapping_add(70),
                scope_hash,
                semantic_profile_id,
                state_root_scheme_id,
            ),
            transition(
                governed_shard_ids[1],
                seed.wrapping_add(110),
                scope_hash,
                semantic_profile_id,
                state_root_scheme_id,
            ),
        ],
        proof_tree_root: commitment(proof_tree_seed),
    }
}

fn hex(bytes: &[u8; 32]) -> String {
    let mut output = String::with_capacity(64);
    for byte in bytes {
        output.push_str(&format!("{byte:02x}"));
    }
    output
}

fn manual_keyed_root(domain: &[u8], entries: [(ShardIdV1, CommitmentV3); 2]) -> CommitmentV3 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher.update(2_u32.to_be_bytes());
    for (shard_id, value) in entries {
        hasher.update(shard_id.as_bytes());
        hasher.update(value.as_bytes());
    }
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

#[test]
fn derives_complete_keyed_map_and_exact_hash_fixture() {
    let epoch = ParallelShardEpochV1::derive(input(1, 220)).unwrap();
    let map = epoch.shard_state_map();

    assert_eq!(map.shard_ids(), [shard(1), shard(2)]);
    assert_ne!(
        map.global_pre_state_root().unwrap(),
        map.global_post_state_root().unwrap()
    );
    assert_ne!(
        map.global_pre_state_root().unwrap(),
        map.shard_semantic_values_root().unwrap()
    );
    assert_eq!(
        epoch.governed_shard_set().canonical_root().unwrap(),
        GovernedShardSetV1::new([shard(1), shard(2)])
            .unwrap()
            .canonical_root()
            .unwrap()
    );

    assert_eq!(
        hex(map.global_pre_state_root().unwrap().as_bytes()),
        "7532f870aeb05a608078ea2ec1cda8ee44c2851d30264ab2d587ce5b855db705"
    );
    assert_eq!(
        hex(map.global_post_state_root().unwrap().as_bytes()),
        "2f4de263a33dd94796302584a2a5c26c99fbfe0269d40f1942f87a1b9095663c"
    );
    assert_eq!(
        map.global_pre_state_root().unwrap(),
        manual_keyed_root(
            b"zenodex.zrpf.parallel_shard.global_pre_state.v1",
            [
                (shard(1), map.entries()[0].local_pre_state_root()),
                (shard(2), map.entries()[1].local_pre_state_root()),
            ],
        )
    );
    assert_eq!(
        map.global_post_state_root().unwrap(),
        manual_keyed_root(
            b"zenodex.zrpf.parallel_shard.global_post_state.v1",
            [
                (shard(1), map.entries()[0].local_post_state_root()),
                (shard(2), map.entries()[1].local_post_state_root()),
            ],
        )
    );

    assert_eq!(
        hex(epoch.semantic_epoch_root().as_bytes()),
        "2e834f1f594e60fc18a59558673ae85330ec780a6303634c29482f6a55202336"
    );
    assert_eq!(
        hex(epoch.proposal_hash().unwrap().as_bytes()),
        "abe385383302d94b5d81cb06746a520561d40f6cfa83957d76702126dfb31a33"
    );
}

#[test]
fn exact_codec_round_trips_and_rejects_trailing_or_oversize_input() {
    let epoch = ParallelShardEpochV1::derive(input(2, 220)).unwrap();
    let encoded = encode_parallel_shard_epoch_v1(&epoch).unwrap();
    assert_eq!(
        decode_exact_parallel_shard_epoch_v1(&encoded).unwrap(),
        epoch
    );

    let mut trailing = encoded;
    trailing.push(0);
    assert_eq!(
        decode_exact_parallel_shard_epoch_v1(&trailing).unwrap_err(),
        ParallelShardEpochErrorV1::TrailingBytes
    );
    assert_eq!(
        decode_exact_parallel_shard_epoch_v1(&[]).unwrap_err(),
        ParallelShardEpochErrorV1::EmptyInput
    );
    let oversized = vec![0_u8; MAX_PARALLEL_SHARD_EPOCH_BYTES_V1 + 1];
    assert_eq!(
        decode_exact_parallel_shard_epoch_v1(&oversized).unwrap_err(),
        ParallelShardEpochErrorV1::InputTooLarge {
            actual: MAX_PARALLEL_SHARD_EPOCH_BYTES_V1 + 1,
            maximum: MAX_PARALLEL_SHARD_EPOCH_BYTES_V1,
        }
    );
}

#[test]
fn governed_set_and_state_map_reject_noncanonical_or_incomplete_identity() {
    assert_eq!(
        GovernedShardSetV1::new([shard(2), shard(1)]).unwrap_err(),
        ParallelShardEpochErrorV1::ShardIdsNotStrictlySorted
    );
    assert_eq!(
        GovernedShardSetV1::new([shard(1), shard(1)]).unwrap_err(),
        ParallelShardEpochErrorV1::ShardIdsNotStrictlySorted
    );
    assert!(serde_json::from_value::<GovernedShardSetV1>(
        serde_json::to_value([shard(1)]).unwrap()
    )
    .is_err());
    assert!(serde_json::from_value::<GovernedShardSetV1>(
        serde_json::to_value([shard(1), shard(2), shard(3)]).unwrap()
    )
    .is_err());

    let mut swapped = input(3, 220);
    swapped.shard_transitions.swap(0, 1);
    assert_eq!(
        ParallelShardEpochV1::derive(swapped).unwrap_err(),
        ParallelShardEpochErrorV1::ShardIdsNotStrictlySorted
    );

    let mut wrong_shard = input(3, 220);
    wrong_shard.shard_transitions[1].shard_id = shard(3);
    assert_eq!(
        ParallelShardEpochV1::derive(wrong_shard).unwrap_err(),
        ParallelShardEpochErrorV1::GovernedShardMismatch
    );
}

#[test]
fn empty_only_policy_rejects_each_message_and_carry_channel() {
    let mut cases = Vec::new();

    let mut outbox = input(4, 220);
    outbox.shard_transitions[0].cross_shard_outbox_root = commitment(240);
    cases.push((
        outbox,
        ParallelShardEpochErrorV1::NonEmptyCrossShardOutbox { shard_index: 0 },
    ));

    let mut inbox = input(4, 220);
    inbox.shard_transitions[0].cross_shard_inbox_root = commitment(240);
    cases.push((
        inbox,
        ParallelShardEpochErrorV1::NonEmptyCrossShardInbox { shard_index: 0 },
    ));

    let mut carry_pre = input(4, 220);
    carry_pre.shard_transitions[0].carry_queue_pre_root = commitment(240);
    cases.push((
        carry_pre,
        ParallelShardEpochErrorV1::NonEmptyCarryQueuePre { shard_index: 0 },
    ));

    let mut carry_post = input(4, 220);
    carry_post.shard_transitions[0].carry_queue_post_root = commitment(240);
    cases.push((
        carry_post,
        ParallelShardEpochErrorV1::NonEmptyCarryQueuePost { shard_index: 0 },
    ));

    for (candidate, expected) in cases {
        assert_eq!(
            ParallelShardEpochV1::derive(candidate).unwrap_err(),
            expected
        );
    }
}

#[test]
fn all_shards_must_bind_the_epoch_scope_profile_and_state_scheme() {
    let mut wrong_scope = input(5, 220);
    wrong_scope.shard_transitions[1].scope_hash = commitment(241);
    assert_eq!(
        ParallelShardEpochV1::derive(wrong_scope).unwrap_err(),
        ParallelShardEpochErrorV1::ScopeMismatch { shard_index: 1 }
    );

    let mut wrong_profile = input(5, 220);
    wrong_profile.shard_transitions[1].semantic_profile_id = profile(241);
    assert!(serde_json::from_value::<CanonicalShardStateMapV1>(
        serde_json::to_value(&wrong_profile.shard_transitions).unwrap()
    )
    .is_err());
    assert_eq!(
        ParallelShardEpochV1::derive(wrong_profile).unwrap_err(),
        ParallelShardEpochErrorV1::SemanticProfileMismatch { shard_index: 1 }
    );

    let mut wrong_scheme = input(5, 220);
    wrong_scheme.shard_transitions[1].state_root_scheme_id = commitment(241);
    assert_eq!(
        ParallelShardEpochV1::derive(wrong_scheme).unwrap_err(),
        ParallelShardEpochErrorV1::StateRootSchemeMismatch { shard_index: 1 }
    );
}

#[test]
fn semantic_root_is_topology_independent_while_proposal_hash_binds_topology() {
    for seed in 1_u8..=32 {
        let first = ParallelShardEpochV1::derive(input(seed, 220)).unwrap();
        let second = ParallelShardEpochV1::derive(input(seed, 221)).unwrap();

        assert_eq!(first.semantic_epoch_root(), second.semantic_epoch_root());
        assert_eq!(
            first.shard_state_map().global_pre_state_root().unwrap(),
            second.shard_state_map().global_pre_state_root().unwrap()
        );
        assert_ne!(first.proof_tree_root(), second.proof_tree_root());
        assert_ne!(
            first.proposal_hash().unwrap(),
            second.proposal_hash().unwrap()
        );
    }
}

#[test]
fn keyed_roots_change_when_state_assignments_change() {
    for seed in 1_u8..=32 {
        let base_input = input(seed, 220);
        let base = ParallelShardEpochV1::derive(base_input.clone()).unwrap();

        let mut reassigned = base_input;
        let first_pre = reassigned.shard_transitions[0].local_pre_state_root;
        reassigned.shard_transitions[0].local_pre_state_root =
            reassigned.shard_transitions[1].local_pre_state_root;
        reassigned.shard_transitions[1].local_pre_state_root = first_pre;
        let reassigned = ParallelShardEpochV1::derive(reassigned).unwrap();

        assert_ne!(
            base.shard_state_map().global_pre_state_root().unwrap(),
            reassigned
                .shard_state_map()
                .global_pre_state_root()
                .unwrap()
        );
        assert_eq!(
            base.shard_state_map().global_post_state_root().unwrap(),
            reassigned
                .shard_state_map()
                .global_post_state_root()
                .unwrap()
        );
        assert_ne!(base.semantic_epoch_root(), reassigned.semantic_epoch_root());
    }
}

#[test]
fn scope_replay_rejects_until_each_shard_is_rebound_and_then_changes_semantic_identity() {
    let original_input = input(6, 220);
    let original = ParallelShardEpochV1::derive(original_input.clone()).unwrap();

    let mut replay = original_input;
    replay.scope = scope(90);
    assert_eq!(
        ParallelShardEpochV1::derive(replay.clone()).unwrap_err(),
        ParallelShardEpochErrorV1::ScopeMismatch { shard_index: 0 }
    );

    let rebound_scope_hash = replay.scope.canonical_hash().unwrap();
    for transition in &mut replay.shard_transitions {
        transition.scope_hash = rebound_scope_hash;
    }
    let rebound = ParallelShardEpochV1::derive(replay).unwrap();
    assert_ne!(
        original.semantic_epoch_root(),
        rebound.semantic_epoch_root()
    );
}

#[test]
fn serde_validation_rejects_unknown_fields_and_forged_semantic_root() {
    let epoch = ParallelShardEpochV1::derive(input(7, 220)).unwrap();
    let mut value = serde_json::to_value(&epoch).unwrap();
    value
        .as_object_mut()
        .unwrap()
        .insert("uncommitted_authority".to_string(), serde_json::json!(true));
    assert!(serde_json::from_value::<ParallelShardEpochV1>(value).is_err());

    let mut forged = serde_json::to_value(&epoch).unwrap();
    forged.as_object_mut().unwrap().insert(
        "semantic_epoch_root".to_string(),
        serde_json::to_value(commitment(242)).unwrap(),
    );
    assert!(serde_json::from_value::<ParallelShardEpochV1>(forged).is_err());
}
