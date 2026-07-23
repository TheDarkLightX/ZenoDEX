mod sparse_merkle_batch_support;

use sparse_merkle_batch_support::{
    action, batch_input_for_steps, canonical_batch_input, commitment, value,
};
use zenodex_zrpf_protocol_v3::{
    decode_exact_sparse_merkle_batch_transition_v1, encode_sparse_merkle_batch_transition_v1,
    expected_sparse_merkle_batch_transition_bytes_v1, LedgerCellWriteInputV2, LedgerCellWriteV2,
    SparseMerkleBatchEntryInputV1, SparseMerkleBatchEntryV1, SparseMerkleBatchTransitionErrorV1,
    ValidatedSparseMerkleBatchTransitionV1, MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1,
    MAX_SPARSE_MERKLE_BATCH_TRANSITION_BYTES_V1, SPARSE_MERKLE_BATCH_ENTRY_BYTES_V1,
    SPARSE_MERKLE_BATCH_FIXED_BYTES_V1,
};

fn batch(count: usize) -> ValidatedSparseMerkleBatchTransitionV1 {
    ValidatedSparseMerkleBatchTransitionV1::new(canonical_batch_input(count)).unwrap()
}

#[test]
fn manual_root_chain_mirror_matches_every_validated_entry() {
    let batch = batch(4);
    let entries = batch.entries();
    assert_eq!(
        entries[0].witness().claimed_pre_root(),
        batch.batch_pre_root()
    );
    for (index, entry) in entries.iter().enumerate() {
        assert_eq!(entry.write_id(), entry.cell_write().economic_action_id());
        assert_eq!(entry.cell_key(), entry.cell_write().cell_key());
        assert_eq!(entry.witness().cell_key(), entry.cell_write().cell_key());
        assert_eq!(
            entry.witness().economic_action_id(),
            entry.cell_write().economic_action_id()
        );
        if index > 0 {
            assert_eq!(
                entry.witness().claimed_pre_root(),
                entries[index - 1].witness().claimed_post_root()
            );
        }
    }
    assert_eq!(
        entries.last().unwrap().witness().claimed_post_root(),
        batch.batch_post_root()
    );
}

#[test]
fn only_the_strictly_increasing_permutation_is_accepted() {
    let canonical = canonical_batch_input(3);
    for permutation in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let mut input = canonical.clone();
        input.entries = permutation
            .into_iter()
            .map(|index| canonical.entries[index].clone())
            .collect();
        let result = ValidatedSparseMerkleBatchTransitionV1::new(input);
        if permutation == [0, 1, 2] {
            assert!(result.is_ok());
        } else {
            assert_eq!(
                result,
                Err(SparseMerkleBatchTransitionErrorV1::NonCanonicalCellKeyOrder)
            );
        }
    }
}

#[test]
fn a_valid_but_noncontiguous_witness_rejects_the_root_gap() {
    let mut canonical = canonical_batch_input(2);
    let isolated_second = batch_input_for_steps(&[(1, 0x42, 0x82)]);
    canonical.entries[1] = isolated_second.entries[0].clone();
    assert_eq!(
        ValidatedSparseMerkleBatchTransitionV1::new(canonical),
        Err(SparseMerkleBatchTransitionErrorV1::RootChainDiscontinuity { index: 1 })
    );
}

#[test]
fn duplicate_key_and_duplicate_write_id_reject_before_root_admission() {
    assert_eq!(
        ValidatedSparseMerkleBatchTransitionV1::new(batch_input_for_steps(&[
            (0, 0x41, 0x81),
            (0, 0x42, 0x82),
        ])),
        Err(SparseMerkleBatchTransitionErrorV1::DuplicateCellKey)
    );
    assert_eq!(
        ValidatedSparseMerkleBatchTransitionV1::new(batch_input_for_steps(&[
            (0, 0x41, 0x81),
            (1, 0x41, 0x82),
        ])),
        Err(SparseMerkleBatchTransitionErrorV1::DuplicateWriteId)
    );
}

#[test]
fn key_and_action_mutations_cannot_rebind_a_valid_witness() {
    let input = canonical_batch_input(1);
    let original = &input.entries[0];
    let key_mutated = LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
        economic_action_id: original.cell_write().economic_action_id(),
        cell_key: commitment(0xf1),
        pre_value_hash: original.cell_write().pre_value_hash(),
        post_value_hash: original.cell_write().post_value_hash(),
    })
    .unwrap();
    assert_eq!(
        SparseMerkleBatchEntryV1::new(SparseMerkleBatchEntryInputV1 {
            cell_write: key_mutated,
            witness: original.witness().clone(),
        }),
        Err(SparseMerkleBatchTransitionErrorV1::CellTransition(
            zenodex_zrpf_protocol_v3::SparseMerkleCellTransitionErrorV1::CellKeyMismatch
        ))
    );
    let action_mutated = LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
        economic_action_id: action(0xf2),
        cell_key: original.cell_write().cell_key(),
        pre_value_hash: original.cell_write().pre_value_hash(),
        post_value_hash: original.cell_write().post_value_hash(),
    })
    .unwrap();
    assert_eq!(
        SparseMerkleBatchEntryV1::new(SparseMerkleBatchEntryInputV1 {
            cell_write: action_mutated,
            witness: original.witness().clone(),
        }),
        Err(SparseMerkleBatchTransitionErrorV1::CellTransition(
            zenodex_zrpf_protocol_v3::SparseMerkleCellTransitionErrorV1::EconomicActionMismatch
        ))
    );
}

#[test]
fn batch_boundary_root_mutations_reject() {
    let mut pre = canonical_batch_input(2);
    pre.batch_pre_root = commitment(0xe1);
    assert_eq!(
        ValidatedSparseMerkleBatchTransitionV1::new(pre),
        Err(SparseMerkleBatchTransitionErrorV1::BatchPreRootMismatch)
    );
    let mut post = canonical_batch_input(2);
    post.batch_post_root = commitment(0xe2);
    assert_eq!(
        ValidatedSparseMerkleBatchTransitionV1::new(post),
        Err(SparseMerkleBatchTransitionErrorV1::BatchPostRootMismatch)
    );
}

#[test]
fn count_bounds_reject_before_batch_allocation_or_validation() {
    assert_eq!(
        expected_sparse_merkle_batch_transition_bytes_v1(usize::MAX),
        Err(SparseMerkleBatchTransitionErrorV1::TooManyEntries {
            actual: usize::MAX,
            maximum: MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1,
        })
    );
    let mut stale = canonical_batch_input(1);
    stale.batch_version += 1;
    assert_eq!(
        ValidatedSparseMerkleBatchTransitionV1::new(stale),
        Err(SparseMerkleBatchTransitionErrorV1::InvalidBatchVersion(2))
    );
    let empty = canonical_batch_input(1);
    assert_eq!(
        ValidatedSparseMerkleBatchTransitionV1::new(
            zenodex_zrpf_protocol_v3::SparseMerkleBatchTransitionInputV1 {
                entries: Vec::new(),
                ..empty
            }
        ),
        Err(SparseMerkleBatchTransitionErrorV1::EmptyBatch)
    );
    let mut oversized = canonical_batch_input(MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1);
    oversized
        .entries
        .push(oversized.entries.last().unwrap().clone());
    assert_eq!(
        ValidatedSparseMerkleBatchTransitionV1::new(oversized),
        Err(SparseMerkleBatchTransitionErrorV1::TooManyEntries {
            actual: MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1 + 1,
            maximum: MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1,
        })
    );
}

#[test]
fn exact_codec_size_formula_round_trips_one_and_maximum_batches() {
    for count in [1, 4, MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1] {
        let batch = batch(count);
        let encoded = encode_sparse_merkle_batch_transition_v1(&batch).unwrap();
        let expected =
            SPARSE_MERKLE_BATCH_FIXED_BYTES_V1 + count * SPARSE_MERKLE_BATCH_ENTRY_BYTES_V1;
        assert_eq!(encoded.len(), expected);
        assert!(encoded.len() <= MAX_SPARSE_MERKLE_BATCH_TRANSITION_BYTES_V1);
        assert_eq!(
            decode_exact_sparse_merkle_batch_transition_v1(&encoded),
            Ok(batch)
        );
    }
}

#[test]
fn exact_codec_rejects_malformed_count_trailing_oversize_and_nonminimal_version() {
    assert_eq!(
        decode_exact_sparse_merkle_batch_transition_v1(&[]),
        Err(SparseMerkleBatchTransitionErrorV1::EmptyInput)
    );
    assert_eq!(
        decode_exact_sparse_merkle_batch_transition_v1(&[1, 65]),
        Err(SparseMerkleBatchTransitionErrorV1::PostcardDecode)
    );
    let encoded = encode_sparse_merkle_batch_transition_v1(&batch(2)).unwrap();
    for end in [1, 64, encoded.len() / 2, encoded.len() - 1] {
        assert_eq!(
            decode_exact_sparse_merkle_batch_transition_v1(&encoded[..end]),
            Err(SparseMerkleBatchTransitionErrorV1::PostcardDecode)
        );
    }
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_sparse_merkle_batch_transition_v1(&trailing),
        Err(SparseMerkleBatchTransitionErrorV1::TrailingBytes)
    );
    let oversized = vec![0; MAX_SPARSE_MERKLE_BATCH_TRANSITION_BYTES_V1 + 1];
    assert_eq!(
        decode_exact_sparse_merkle_batch_transition_v1(&oversized),
        Err(SparseMerkleBatchTransitionErrorV1::InputTooLarge {
            actual: oversized.len(),
            maximum: MAX_SPARSE_MERKLE_BATCH_TRANSITION_BYTES_V1,
        })
    );
    let mut nonminimal = encoded;
    nonminimal.splice(0..1, [0x81, 0x00]);
    assert_eq!(
        decode_exact_sparse_merkle_batch_transition_v1(&nonminimal),
        Err(SparseMerkleBatchTransitionErrorV1::NonCanonicalEncoding)
    );
}

#[test]
fn encoded_nested_root_mutation_rejects_before_batch_typestate_exists() {
    let batch = batch(2);
    let mut encoded = encode_sparse_merkle_batch_transition_v1(&batch).unwrap();
    let root = batch.entries()[0].witness().claimed_pre_root().into_bytes();
    let offset = encoded
        .windows(32)
        .position(|window| window == root)
        .unwrap();
    encoded[offset] ^= 1;
    assert_eq!(
        decode_exact_sparse_merkle_batch_transition_v1(&encoded),
        Err(SparseMerkleBatchTransitionErrorV1::PostcardDecode)
    );
}

#[test]
fn write_value_mutation_remains_a_cell_binding_error() {
    let input = canonical_batch_input(1);
    let original = &input.entries[0];
    let mutated = LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
        economic_action_id: original.cell_write().economic_action_id(),
        cell_key: original.cell_write().cell_key(),
        pre_value_hash: value(0xf3),
        post_value_hash: original.cell_write().post_value_hash(),
    })
    .unwrap();
    assert_eq!(
        SparseMerkleBatchEntryV1::new(SparseMerkleBatchEntryInputV1 {
            cell_write: mutated,
            witness: original.witness().clone(),
        }),
        Err(SparseMerkleBatchTransitionErrorV1::CellTransition(
            zenodex_zrpf_protocol_v3::SparseMerkleCellTransitionErrorV1::PreValueMismatch
        ))
    );
}

mod jmt_storage_update_plan_v1_tests {
    use super::sparse_merkle_batch_support::{canonical_batch_input, commitment};
    use sha2::{Digest, Sha256};
    use zenodex_zrpf_protocol_v3::{
        decode_exact_jmt_storage_update_plan_v1, derive_jmt_storage_new_nodes_v1,
        derive_jmt_storage_update_plan_commitment_v1, encode_jmt_storage_update_plan_v1,
        JmtNibblePathV1, JmtNodeKeyV1, JmtNodeRecordV1, JmtStaleNodeIndexV1,
        JmtStorageUpdatePlanErrorV1, JmtStorageUpdatePlanInputV1, ValidatedJmtStorageUpdatePlanV1,
        ValidatedSparseMerkleBatchTransitionV1, JMT_NIBBLE_PATH_MAX_NIBBLES_V1,
        JMT_STORAGE_PROFILE_SPARSE_MERKLE_BRIDGE_V1, JMT_STORAGE_UPDATE_PLAN_VERSION_V1,
        MAX_JMT_STORAGE_NEW_NODES_V1, MAX_JMT_STORAGE_STALE_NODES_V1,
        MAX_JMT_STORAGE_UPDATE_PLAN_BYTES_V1,
    };

    const PLAN_HASH_DOMAIN: &[u8] = b"zenodex.zrpf.jmt_storage_update_plan_hash.v1";

    fn path(first_byte: u8, nibble_count: u8) -> JmtNibblePathV1 {
        let mut key = [0_u8; 32];
        key[0] = first_byte;
        JmtNibblePathV1::from_key_prefix(key, nibble_count).unwrap()
    }

    fn batch_with_count(count: usize) -> ValidatedSparseMerkleBatchTransitionV1 {
        ValidatedSparseMerkleBatchTransitionV1::new(canonical_batch_input(count)).unwrap()
    }

    fn batch() -> ValidatedSparseMerkleBatchTransitionV1 {
        batch_with_count(1)
    }

    fn valid_input() -> JmtStorageUpdatePlanInputV1 {
        let transition = batch();
        let base_version = 7;
        let target_version = 8;
        let new_nodes = derive_jmt_storage_new_nodes_v1(&transition, target_version).unwrap();
        let stale_root = JmtNodeKeyV1::new(base_version, JmtNibblePathV1::root());
        JmtStorageUpdatePlanInputV1 {
            plan_version: JMT_STORAGE_UPDATE_PLAN_VERSION_V1,
            storage_profile: JMT_STORAGE_PROFILE_SPARSE_MERKLE_BRIDGE_V1,
            tree_id: commitment(0xd0),
            base_version,
            target_version,
            base_root: transition.batch_pre_root(),
            post_root: transition.batch_post_root(),
            stale_nodes: vec![JmtStaleNodeIndexV1::new(
                target_version,
                stale_root,
                transition.batch_pre_root(),
            )],
            transition,
            new_nodes,
        }
    }

    fn plan() -> ValidatedJmtStorageUpdatePlanV1 {
        ValidatedJmtStorageUpdatePlanV1::new(valid_input()).unwrap()
    }

    #[test]
    fn valid_plan_binds_tree_versions_roots_transition_and_derived_storage_batches() {
        let plan = plan();
        assert_eq!(plan.plan_version(), JMT_STORAGE_UPDATE_PLAN_VERSION_V1);
        assert_eq!(
            plan.storage_profile(),
            JMT_STORAGE_PROFILE_SPARSE_MERKLE_BRIDGE_V1
        );
        assert_eq!(plan.tree_id(), commitment(0xd0));
        assert_eq!(plan.base_version(), 7);
        assert_eq!(plan.target_version(), 8);
        assert_eq!(plan.base_root(), plan.transition().batch_pre_root());
        assert_eq!(plan.post_root(), plan.transition().batch_post_root());
        assert_eq!(plan.new_nodes().len(), 65);
        assert_eq!(plan.stale_nodes().len(), 1);
        assert!(plan.new_nodes()[0].node_key().nibble_path().is_root());
        assert_eq!(plan.new_nodes()[0].node_hash(), plan.post_root());
        let expected =
            derive_jmt_storage_new_nodes_v1(plan.transition(), plan.target_version()).unwrap();
        assert_eq!(plan.new_nodes(), expected.as_slice());
    }

    #[test]
    fn shared_paths_use_the_final_sequential_boundary_commitment() {
        let transition = batch_with_count(2);
        let nodes = derive_jmt_storage_new_nodes_v1(&transition, 11).unwrap();
        assert!(nodes.len() >= 65);
        assert!(nodes.len() < 130);
        assert!(nodes[0].node_key().nibble_path().is_root());
        assert_eq!(nodes[0].node_hash(), transition.batch_post_root());
        assert!(nodes
            .windows(2)
            .all(|pair| pair[0].node_key().nibble_path() < pair[1].node_key().nibble_path()));
        assert!(nodes.iter().all(|node| node.node_key().version() == 11));
    }

    #[test]
    fn nibble_paths_are_unique_canonical_prefix_values() {
        assert_eq!(JmtNibblePathV1::root().packed_nibbles(), &[0_u8; 32]);
        assert!(JmtNibblePathV1::root().is_root());

        let mut key = [0xff_u8; 32];
        key[0] = 0xab;
        let one = JmtNibblePathV1::from_key_prefix(key, 1).unwrap();
        assert_eq!(one.nibble_count(), 1);
        assert_eq!(one.packed_nibbles()[0], 0xa0);
        assert!(one.packed_nibbles()[1..].iter().all(|byte| *byte == 0));

        let two = JmtNibblePathV1::from_key_prefix(key, 2).unwrap();
        assert_eq!(two.packed_nibbles()[0], 0xab);
        assert!(two.packed_nibbles()[1..].iter().all(|byte| *byte == 0));

        let full = JmtNibblePathV1::from_key_prefix(key, JMT_NIBBLE_PATH_MAX_NIBBLES_V1).unwrap();
        assert_eq!(full.packed_nibbles(), &key);

        let mut noncanonical = [0_u8; 32];
        noncanonical[0] = 0xab;
        assert_eq!(
            JmtNibblePathV1::new(1, noncanonical),
            Err(JmtStorageUpdatePlanErrorV1::NonCanonicalNibblePath)
        );
        assert_eq!(
            JmtNibblePathV1::new(JMT_NIBBLE_PATH_MAX_NIBBLES_V1 + 1, [0; 32]),
            Err(JmtStorageUpdatePlanErrorV1::InvalidNibbleCount(65))
        );
    }

    #[test]
    fn plan_and_storage_profile_versions_fail_closed() {
        let mut input = valid_input();
        input.plan_version += 1;
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::InvalidPlanVersion(2))
        );

        let mut input = valid_input();
        input.storage_profile += 1;
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::InvalidStorageProfile(2))
        );
    }

    #[test]
    fn tree_version_is_one_strict_successor() {
        let mut input = valid_input();
        input.target_version += 1;
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::NonSuccessorVersion {
                base_version: 7,
                target_version: 9,
            })
        );

        let mut input = valid_input();
        input.base_version = u64::MAX;
        input.target_version = u64::MAX;
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::VersionOverflow)
        );
    }

    #[test]
    fn envelope_roots_must_equal_the_validated_transition() {
        let mut input = valid_input();
        input.base_root = commitment(0xe1);
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::BaseRootMismatch)
        );

        let mut input = valid_input();
        input.post_root = commitment(0xe2);
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::PostRootMismatch)
        );
    }

    #[test]
    fn new_nodes_must_exactly_equal_the_transition_derived_set() {
        let mut input = valid_input();
        let record = input.new_nodes[0];
        input.new_nodes[0] = JmtNodeRecordV1::new(
            JmtNodeKeyV1::new(input.target_version + 1, record.node_key().nibble_path()),
            record.node_hash(),
        );
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::NewNodeVersionMismatch {
                index: 0,
                actual: 9,
                expected: 8,
            })
        );

        let mut input = valid_input();
        input.new_nodes.swap(0, 1);
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::NonCanonicalNewNodeOrder { index: 1 })
        );

        let mut input = valid_input();
        input.new_nodes[1] = input.new_nodes[0];
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::DuplicateNewNodeKey { index: 1 })
        );

        let mut input = valid_input();
        let _ = input.new_nodes.pop();
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::NewNodeCountMismatch {
                actual: 64,
                expected: 65,
            })
        );

        let mut input = valid_input();
        let index = 1;
        let original = input.new_nodes[index];
        input.new_nodes[index] = JmtNodeRecordV1::new(original.node_key(), commitment(0xe3));
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::NewNodeMismatch { index })
        );

        let mut input = valid_input();
        input.new_nodes.clear();
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::EmptyNewNodeBatch)
        );
    }

    #[test]
    fn stale_indices_are_path_unique_historical_and_hash_bound_to_base_state() {
        let mut input = valid_input();
        let stale = input.stale_nodes[0];
        input.stale_nodes[0] = JmtStaleNodeIndexV1::new(
            input.target_version + 1,
            stale.node_key(),
            stale.expected_node_hash(),
        );
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::StaleSinceVersionMismatch {
                index: 0,
                actual: 9,
                expected: 8,
            })
        );

        let mut input = valid_input();
        input.stale_nodes[0] = JmtStaleNodeIndexV1::new(
            input.target_version,
            JmtNodeKeyV1::new(input.target_version, JmtNibblePathV1::root()),
            input.base_root,
        );
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::FutureStaleNode {
                index: 0,
                node_version: 8,
                base_version: 7,
            })
        );

        let mut input = valid_input();
        let stale = input.stale_nodes[0];
        input.stale_nodes[0] = JmtStaleNodeIndexV1::new(
            stale.stale_since_version(),
            stale.node_key(),
            commitment(0xe4),
        );
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::StaleNodeHashMismatch { index: 0 })
        );

        let mut input = valid_input();
        input.stale_nodes[0] = JmtStaleNodeIndexV1::new(
            input.target_version,
            JmtNodeKeyV1::new(input.base_version, path(0xf0, 1)),
            input.base_root,
        );
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::UntouchedStalePath { index: 0 })
        );

        let mut input = valid_input();
        let root = input.stale_nodes[0];
        input.stale_nodes.push(JmtStaleNodeIndexV1::new(
            input.target_version,
            JmtNodeKeyV1::new(input.base_version - 1, JmtNibblePathV1::root()),
            root.expected_node_hash(),
        ));
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::DuplicateStalePath { index: 1 })
        );

        let mut input = valid_input();
        let child = input.new_nodes[1];
        input.stale_nodes.push(JmtStaleNodeIndexV1::new(
            input.target_version,
            JmtNodeKeyV1::new(input.base_version, child.node_key().nibble_path()),
            commitment(0xe5),
        ));
        input.stale_nodes.swap(0, 1);
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::NonCanonicalStaleNodeOrder { index: 1 })
        );

        let mut input = valid_input();
        input.stale_nodes.clear();
        assert!(ValidatedJmtStorageUpdatePlanV1::new(input).is_ok());
    }

    #[test]
    fn node_and_stale_count_bounds_run_before_deeper_validation() {
        let mut input = valid_input();
        input.new_nodes = vec![input.new_nodes[0]; MAX_JMT_STORAGE_NEW_NODES_V1 + 1];
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::TooManyNewNodes {
                actual: MAX_JMT_STORAGE_NEW_NODES_V1 + 1,
                maximum: MAX_JMT_STORAGE_NEW_NODES_V1,
            })
        );

        let mut input = valid_input();
        input.stale_nodes = vec![input.stale_nodes[0]; MAX_JMT_STORAGE_STALE_NODES_V1 + 1];
        assert_eq!(
            ValidatedJmtStorageUpdatePlanV1::new(input),
            Err(JmtStorageUpdatePlanErrorV1::TooManyStaleNodes {
                actual: MAX_JMT_STORAGE_STALE_NODES_V1 + 1,
                maximum: MAX_JMT_STORAGE_STALE_NODES_V1,
            })
        );
    }

    #[test]
    fn exact_codec_round_trips_and_rejects_trailing_nonminimal_and_oversize_bytes() {
        let plan = plan();
        let encoded = encode_jmt_storage_update_plan_v1(&plan).unwrap();
        assert!(!encoded.is_empty());
        assert!(encoded.len() <= MAX_JMT_STORAGE_UPDATE_PLAN_BYTES_V1);
        assert_eq!(
            decode_exact_jmt_storage_update_plan_v1(&encoded),
            Ok(plan.clone())
        );

        assert_eq!(
            decode_exact_jmt_storage_update_plan_v1(&[]),
            Err(JmtStorageUpdatePlanErrorV1::EmptyInput)
        );

        let mut trailing = encoded.clone();
        trailing.push(0);
        assert_eq!(
            decode_exact_jmt_storage_update_plan_v1(&trailing),
            Err(JmtStorageUpdatePlanErrorV1::TrailingBytes)
        );

        let mut nonminimal = encoded;
        let _ = nonminimal.splice(0..1, [0x81, 0x00]);
        assert_eq!(
            decode_exact_jmt_storage_update_plan_v1(&nonminimal),
            Err(JmtStorageUpdatePlanErrorV1::NonCanonicalEncoding)
        );

        let oversized = vec![0; MAX_JMT_STORAGE_UPDATE_PLAN_BYTES_V1 + 1];
        assert_eq!(
            decode_exact_jmt_storage_update_plan_v1(&oversized),
            Err(JmtStorageUpdatePlanErrorV1::InputTooLarge {
                actual: oversized.len(),
                maximum: MAX_JMT_STORAGE_UPDATE_PLAN_BYTES_V1,
            })
        );
    }

    #[test]
    fn canonical_hash_binds_the_exact_plan_bytes_and_tree_identity() {
        let plan = plan();
        let encoded = encode_jmt_storage_update_plan_v1(&plan).unwrap();
        let mut hasher = Sha256::new();
        hasher.update(u16::try_from(PLAN_HASH_DOMAIN.len()).unwrap().to_be_bytes());
        hasher.update(PLAN_HASH_DOMAIN);
        hasher.update(&encoded);
        let expected: [u8; 32] = hasher.finalize().into();

        assert_eq!(
            derive_jmt_storage_update_plan_commitment_v1(&plan)
                .unwrap()
                .into_bytes(),
            expected
        );
        assert_eq!(
            plan.canonical_hash().unwrap(),
            derive_jmt_storage_update_plan_commitment_v1(&plan).unwrap()
        );

        let mut changed = valid_input();
        changed.tree_id = commitment(0xd1);
        let changed = ValidatedJmtStorageUpdatePlanV1::new(changed).unwrap();
        assert_ne!(
            plan.canonical_hash().unwrap(),
            changed.canonical_hash().unwrap()
        );
    }
}
