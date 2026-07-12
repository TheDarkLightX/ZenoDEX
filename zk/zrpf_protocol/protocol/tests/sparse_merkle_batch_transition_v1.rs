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
