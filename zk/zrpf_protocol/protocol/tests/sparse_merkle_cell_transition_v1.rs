use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    bind_sparse_merkle_cell_transition_v1, decode_exact_sparse_merkle_cell_transition_witness_v1,
    derive_sparse_merkle_internal_commitment_v1, derive_sparse_merkle_leaf_commitment_v1,
    derive_sparse_merkle_root_v1, encode_sparse_merkle_cell_transition_witness_v1, CommitmentV3,
    EconomicActionIdV1, LedgerCellWriteInputV2, LedgerCellWriteV2,
    SparseMerkleCellTransitionErrorV1, SparseMerkleCellTransitionWitnessInputV1,
    SparseMerkleCellTransitionWitnessV1, SparseMerkleSiblingPathV1, ValueHashV2,
    MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1,
    SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1, SPARSE_MERKLE_TREE_DEPTH_V1,
    SPARSE_MERKLE_WITNESS_VERSION_V1,
};

const LEAF_DOMAIN: &[u8] = b"zenodex.zrpf.sparse_merkle_leaf.v1";
const INTERNAL_DOMAIN: &[u8] = b"zenodex.zrpf.sparse_merkle_internal.v1";

fn bytes(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new(bytes(seed)).unwrap()
}

fn action(seed: u8) -> EconomicActionIdV1 {
    EconomicActionIdV1::new(bytes(seed)).unwrap()
}

fn value(seed: u8) -> ValueHashV2 {
    ValueHashV2::new(bytes(seed))
}

fn sibling_path() -> SparseMerkleSiblingPathV1 {
    let siblings = core::array::from_fn(|depth| {
        let mut raw = [0_u8; 32];
        raw[..8].copy_from_slice(&(u64::try_from(depth).unwrap() + 1).to_be_bytes());
        raw[31] = 0xa5;
        CommitmentV3::new(raw).unwrap()
    });
    SparseMerkleSiblingPathV1::new(siblings)
}

fn base_input() -> SparseMerkleCellTransitionWitnessInputV1 {
    let cell_key = commitment(0xa5);
    let pre_value_hash = value(0x31);
    let post_value_hash = value(0x32);
    let sibling_commitments = sibling_path();
    let claimed_pre_root =
        derive_sparse_merkle_root_v1(cell_key, pre_value_hash, &sibling_commitments).unwrap();
    let claimed_post_root =
        derive_sparse_merkle_root_v1(cell_key, post_value_hash, &sibling_commitments).unwrap();
    SparseMerkleCellTransitionWitnessInputV1 {
        witness_version: SPARSE_MERKLE_WITNESS_VERSION_V1,
        economic_action_id: action(0x21),
        cell_key,
        pre_value_hash,
        post_value_hash,
        sibling_commitments,
        claimed_pre_root,
        claimed_post_root,
    }
}

fn witness() -> SparseMerkleCellTransitionWitnessV1 {
    SparseMerkleCellTransitionWitnessV1::new(base_input()).unwrap()
}

fn write_for(value: &SparseMerkleCellTransitionWitnessV1) -> LedgerCellWriteV2 {
    LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
        economic_action_id: value.economic_action_id(),
        cell_key: value.cell_key(),
        pre_value_hash: value.pre_value_hash(),
        post_value_hash: value.post_value_hash(),
    })
    .unwrap()
}

fn manual_domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

fn manual_leaf(key: CommitmentV3, value: ValueHashV2) -> [u8; 32] {
    let mut hasher = manual_domain_hasher(LEAF_DOMAIN);
    hasher.update(key.as_bytes());
    hasher.update(value.as_bytes());
    hasher.finalize().into()
}

fn manual_internal(depth: usize, left: CommitmentV3, right: CommitmentV3) -> [u8; 32] {
    let mut hasher = manual_domain_hasher(INTERNAL_DOMAIN);
    hasher.update(u16::try_from(depth).unwrap().to_be_bytes());
    hasher.update(left.as_bytes());
    hasher.update(right.as_bytes());
    hasher.finalize().into()
}

#[test]
fn fixed_leaf_and_internal_preimages_match_independent_hashes() {
    let leaf = derive_sparse_merkle_leaf_commitment_v1(commitment(0x11), value(0x22)).unwrap();
    let internal =
        derive_sparse_merkle_internal_commitment_v1(255, commitment(0x33), commitment(0x44))
            .unwrap();
    let expected_leaf = [
        0xec, 0xb3, 0x62, 0x34, 0xe7, 0x96, 0x96, 0xed, 0x1a, 0x93, 0xb2, 0x1d, 0xf4, 0x02, 0x12,
        0x02, 0xd1, 0xbd, 0xcd, 0xc0, 0x41, 0xf6, 0x8a, 0x81, 0x53, 0xde, 0x0a, 0xca, 0xbe, 0x4d,
        0x94, 0x37,
    ];
    let expected_internal = [
        0xaa, 0xb5, 0xde, 0xe8, 0x9b, 0x7e, 0xd1, 0xe5, 0xa4, 0xed, 0x9f, 0x81, 0x23, 0x37, 0xa0,
        0xe2, 0xd8, 0x1e, 0x6c, 0x22, 0x88, 0x26, 0x43, 0x1e, 0x06, 0xc3, 0x9b, 0x46, 0xe5, 0xdb,
        0xeb, 0x3b,
    ];

    assert_eq!(
        leaf.into_bytes(),
        manual_leaf(commitment(0x11), value(0x22))
    );
    assert_eq!(
        internal.into_bytes(),
        manual_internal(255, commitment(0x33), commitment(0x44))
    );
    assert_eq!(leaf.into_bytes(), expected_leaf);
    assert_eq!(internal.into_bytes(), expected_internal);
    assert_ne!(
        internal,
        derive_sparse_merkle_internal_commitment_v1(255, commitment(0x44), commitment(0x33))
            .unwrap()
    );
    for depth in 0..255 {
        assert_ne!(
            internal,
            derive_sparse_merkle_internal_commitment_v1(depth, commitment(0x33), commitment(0x44))
                .unwrap()
        );
    }
}

#[test]
fn root_derivation_uses_msb_first_key_bits_and_root_to_leaf_siblings() {
    let input = base_input();
    let manual = input
        .sibling_commitments
        .as_array()
        .iter()
        .enumerate()
        .rev()
        .try_fold(
            derive_sparse_merkle_leaf_commitment_v1(input.cell_key, input.pre_value_hash).unwrap(),
            |current, (depth, sibling)| {
                let byte = input.cell_key.as_bytes()[depth / 8];
                let bit = (byte >> (7 - (depth % 8))) & 1;
                if bit == 0 {
                    derive_sparse_merkle_internal_commitment_v1(depth, current, *sibling)
                } else {
                    derive_sparse_merkle_internal_commitment_v1(depth, *sibling, current)
                }
            },
        );

    assert_eq!(manual.unwrap(), input.claimed_pre_root);
}

#[test]
fn constructor_derives_both_roots_and_binding_matches_one_complete_cell_write() {
    let witness = witness();
    let transition = bind_sparse_merkle_cell_transition_v1(&witness, &write_for(&witness)).unwrap();

    assert_eq!(
        transition.economic_action_id(),
        witness.economic_action_id()
    );
    assert_eq!(transition.cell_key(), witness.cell_key());
    assert_eq!(transition.pre_value_hash(), witness.pre_value_hash());
    assert_eq!(transition.post_value_hash(), witness.post_value_hash());
    assert_eq!(transition.derived_pre_root(), witness.claimed_pre_root());
    assert_eq!(transition.derived_post_root(), witness.claimed_post_root());
}

#[test]
fn every_key_path_bit_mutation_rejects_the_supplied_roots() {
    let baseline = base_input();
    for bit_index in 0..SPARSE_MERKLE_TREE_DEPTH_V1 {
        let mut input = baseline.clone();
        let mut key = input.cell_key.into_bytes();
        key[bit_index / 8] ^= 1 << (7 - (bit_index % 8));
        input.cell_key = CommitmentV3::new(key).unwrap();
        assert_eq!(
            SparseMerkleCellTransitionWitnessV1::new(input),
            Err(SparseMerkleCellTransitionErrorV1::ClaimedPreRootMismatch),
            "key bit {bit_index}"
        );
    }
}

#[test]
fn every_sibling_mutation_rejects_the_supplied_roots() {
    let baseline = base_input();
    for depth in 0..SPARSE_MERKLE_TREE_DEPTH_V1 {
        let mut input = baseline.clone();
        let mut siblings = *input.sibling_commitments.as_array();
        let mut mutated = siblings[depth].into_bytes();
        mutated[31] ^= 1;
        siblings[depth] = CommitmentV3::new(mutated).unwrap();
        input.sibling_commitments = SparseMerkleSiblingPathV1::new(siblings);
        assert_eq!(
            SparseMerkleCellTransitionWitnessV1::new(input),
            Err(SparseMerkleCellTransitionErrorV1::ClaimedPreRootMismatch),
            "sibling depth {depth}"
        );
    }
}

#[test]
fn every_value_bit_and_each_supplied_root_mutation_fail_closed() {
    let baseline = base_input();
    for bit_index in 0..256 {
        let mut pre = baseline.clone();
        let mut raw = pre.pre_value_hash.into_bytes();
        raw[bit_index / 8] ^= 1 << (7 - (bit_index % 8));
        pre.pre_value_hash = ValueHashV2::new(raw);
        assert_eq!(
            SparseMerkleCellTransitionWitnessV1::new(pre),
            Err(SparseMerkleCellTransitionErrorV1::ClaimedPreRootMismatch),
            "pre-value bit {bit_index}"
        );

        let mut post = baseline.clone();
        let mut raw = post.post_value_hash.into_bytes();
        raw[bit_index / 8] ^= 1 << (7 - (bit_index % 8));
        post.post_value_hash = ValueHashV2::new(raw);
        assert_eq!(
            SparseMerkleCellTransitionWitnessV1::new(post),
            Err(SparseMerkleCellTransitionErrorV1::ClaimedPostRootMismatch),
            "post-value bit {bit_index}"
        );
    }
    let mut pre_root = baseline.clone();
    pre_root.claimed_pre_root = commitment(0x51);
    assert_eq!(
        SparseMerkleCellTransitionWitnessV1::new(pre_root),
        Err(SparseMerkleCellTransitionErrorV1::ClaimedPreRootMismatch)
    );
    let mut post_root = baseline;
    post_root.claimed_post_root = commitment(0x52);
    assert_eq!(
        SparseMerkleCellTransitionWitnessV1::new(post_root),
        Err(SparseMerkleCellTransitionErrorV1::ClaimedPostRootMismatch)
    );
}

#[test]
fn invalid_version_unchanged_value_and_out_of_range_depth_reject() {
    let mut wrong_version = base_input();
    wrong_version.witness_version += 1;
    assert_eq!(
        SparseMerkleCellTransitionWitnessV1::new(wrong_version),
        Err(SparseMerkleCellTransitionErrorV1::InvalidWitnessVersion(2))
    );
    let mut unchanged = base_input();
    unchanged.post_value_hash = unchanged.pre_value_hash;
    assert_eq!(
        SparseMerkleCellTransitionWitnessV1::new(unchanged),
        Err(SparseMerkleCellTransitionErrorV1::UnchangedValue)
    );
    assert_eq!(
        derive_sparse_merkle_internal_commitment_v1(
            SPARSE_MERKLE_TREE_DEPTH_V1,
            commitment(1),
            commitment(2)
        ),
        Err(SparseMerkleCellTransitionErrorV1::DepthOutOfRange(
            SPARSE_MERKLE_TREE_DEPTH_V1
        ))
    );
}

#[test]
fn binding_rejects_each_mismatched_cell_write_field() {
    let witness = witness();
    let cases = [
        (
            LedgerCellWriteInputV2 {
                economic_action_id: action(0x71),
                cell_key: witness.cell_key(),
                pre_value_hash: witness.pre_value_hash(),
                post_value_hash: witness.post_value_hash(),
            },
            SparseMerkleCellTransitionErrorV1::EconomicActionMismatch,
        ),
        (
            LedgerCellWriteInputV2 {
                economic_action_id: witness.economic_action_id(),
                cell_key: commitment(0x72),
                pre_value_hash: witness.pre_value_hash(),
                post_value_hash: witness.post_value_hash(),
            },
            SparseMerkleCellTransitionErrorV1::CellKeyMismatch,
        ),
        (
            LedgerCellWriteInputV2 {
                economic_action_id: witness.economic_action_id(),
                cell_key: witness.cell_key(),
                pre_value_hash: value(0x73),
                post_value_hash: witness.post_value_hash(),
            },
            SparseMerkleCellTransitionErrorV1::PreValueMismatch,
        ),
        (
            LedgerCellWriteInputV2 {
                economic_action_id: witness.economic_action_id(),
                cell_key: witness.cell_key(),
                pre_value_hash: witness.pre_value_hash(),
                post_value_hash: value(0x74),
            },
            SparseMerkleCellTransitionErrorV1::PostValueMismatch,
        ),
    ];
    for (input, expected) in cases {
        let write = LedgerCellWriteV2::new(input).unwrap();
        assert_eq!(
            bind_sparse_merkle_cell_transition_v1(&witness, &write),
            Err(expected)
        );
    }
}

#[test]
fn exact_bounded_postcard_codec_round_trips_and_rejects_malformed_inputs() {
    let witness = witness();
    let encoded = encode_sparse_merkle_cell_transition_witness_v1(&witness).unwrap();
    assert_eq!(
        encoded.len(),
        SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1
    );
    assert!(encoded.len() <= MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1);
    assert_eq!(
        decode_exact_sparse_merkle_cell_transition_witness_v1(&encoded),
        Ok(witness)
    );
    assert_eq!(
        decode_exact_sparse_merkle_cell_transition_witness_v1(&[]),
        Err(SparseMerkleCellTransitionErrorV1::EmptyInput)
    );
    for end in [1, 33, encoded.len() / 2, encoded.len() - 1] {
        assert_eq!(
            decode_exact_sparse_merkle_cell_transition_witness_v1(&encoded[..end]),
            Err(SparseMerkleCellTransitionErrorV1::PostcardDecode)
        );
    }
    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_sparse_merkle_cell_transition_witness_v1(&trailing),
        Err(SparseMerkleCellTransitionErrorV1::TrailingBytes)
    );
    let oversized = vec![0; MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1 + 1];
    assert_eq!(
        decode_exact_sparse_merkle_cell_transition_witness_v1(&oversized),
        Err(SparseMerkleCellTransitionErrorV1::InputTooLarge {
            actual: oversized.len(),
            maximum: MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1,
        })
    );
    let mut nonminimal = encoded;
    nonminimal.splice(0..1, [0x81, 0x00]);
    assert_eq!(
        decode_exact_sparse_merkle_cell_transition_witness_v1(&nonminimal),
        Err(SparseMerkleCellTransitionErrorV1::NonCanonicalEncoding)
    );
}

#[test]
fn encoded_zero_sibling_is_rejected_before_a_witness_exists() {
    let mut encoded = encode_sparse_merkle_cell_transition_witness_v1(&witness()).unwrap();
    let sibling_start = 1 + (4 * 32);
    encoded[sibling_start..sibling_start + 32].fill(0);
    assert_eq!(
        decode_exact_sparse_merkle_cell_transition_witness_v1(&encoded),
        Err(SparseMerkleCellTransitionErrorV1::PostcardDecode)
    );
}
