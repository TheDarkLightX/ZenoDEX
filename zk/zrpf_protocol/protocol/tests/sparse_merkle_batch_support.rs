use std::collections::BTreeMap;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    derive_sparse_merkle_internal_commitment_v1, derive_sparse_merkle_leaf_commitment_v1,
    CommitmentV3, EconomicActionIdV1, LedgerCellWriteInputV2, LedgerCellWriteV2,
    SparseMerkleBatchEntryInputV1, SparseMerkleBatchEntryV1, SparseMerkleBatchTransitionInputV1,
    SparseMerkleCellTransitionWitnessInputV1, SparseMerkleCellTransitionWitnessV1,
    SparseMerkleSiblingPathV1, ValueHashV2, SPARSE_MERKLE_BATCH_VERSION_V1,
    SPARSE_MERKLE_TREE_DEPTH_V1, SPARSE_MERKLE_WITNESS_VERSION_V1,
};

const FRONTIER_DOMAIN: &[u8] = b"zenodex.zrpf.test.sparse_merkle_frontier.v1";

pub fn bytes(seed: u8) -> [u8; 32] {
    [seed; 32]
}

pub fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new(bytes(seed)).unwrap()
}

pub fn action(seed: u8) -> EconomicActionIdV1 {
    EconomicActionIdV1::new(bytes(seed)).unwrap()
}

pub fn value(seed: u8) -> ValueHashV2 {
    ValueHashV2::new(bytes(seed))
}

fn key(index: usize) -> CommitmentV3 {
    let mut raw = [0_u8; 32];
    raw[..8].copy_from_slice(&(u64::try_from(index).unwrap() + 1).to_be_bytes());
    raw[31] = 0xa5;
    CommitmentV3::new(raw).unwrap()
}

fn path_bit(key: CommitmentV3, depth: usize) -> u8 {
    (key.as_bytes()[depth / 8] >> (7 - (depth % 8))) & 1
}

fn prefix_with_bit(mut prefix: [u8; 32], depth: usize, bit: u8) -> [u8; 32] {
    let mask = 1 << (7 - (depth % 8));
    if bit == 0 {
        prefix[depth / 8] &= !mask;
    } else {
        prefix[depth / 8] |= mask;
    }
    prefix
}

fn frontier(depth: usize, prefix: [u8; 32]) -> CommitmentV3 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(FRONTIER_DOMAIN.len()).unwrap().to_be_bytes());
    hasher.update(FRONTIER_DOMAIN);
    hasher.update(u16::try_from(depth).unwrap().to_be_bytes());
    hasher.update(prefix);
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

fn split_at_bit(entries: &[(CommitmentV3, ValueHashV2)], depth: usize) -> usize {
    entries
        .iter()
        .position(|(entry_key, _)| path_bit(*entry_key, depth) == 1)
        .unwrap_or(entries.len())
}

fn build_subtree(
    nodes: &mut BTreeMap<(usize, [u8; 32]), CommitmentV3>,
    depth: usize,
    prefix: [u8; 32],
    entries: &[(CommitmentV3, ValueHashV2)],
) -> CommitmentV3 {
    let root = if entries.is_empty() {
        frontier(depth, prefix)
    } else if depth == SPARSE_MERKLE_TREE_DEPTH_V1 {
        assert_eq!(entries.len(), 1);
        derive_sparse_merkle_leaf_commitment_v1(entries[0].0, entries[0].1).unwrap()
    } else {
        let split = split_at_bit(entries, depth);
        let left = build_subtree(
            nodes,
            depth + 1,
            prefix_with_bit(prefix, depth, 0),
            &entries[..split],
        );
        let right = build_subtree(
            nodes,
            depth + 1,
            prefix_with_bit(prefix, depth, 1),
            &entries[split..],
        );
        derive_sparse_merkle_internal_commitment_v1(depth, left, right).unwrap()
    };
    nodes.insert((depth, prefix), root);
    root
}

fn key_prefix(key: CommitmentV3, depth: usize) -> [u8; 32] {
    let mut prefix = *key.as_bytes();
    let full_bytes = depth / 8;
    let remaining_bits = depth % 8;
    if full_bytes < prefix.len() {
        if remaining_bits == 0 {
            prefix[full_bytes] = 0;
        } else {
            prefix[full_bytes] &= 0xff << (8 - remaining_bits);
        }
        prefix[full_bytes + 1..].fill(0);
    }
    prefix
}

fn initial_state(cell_count: usize) -> Vec<(CommitmentV3, ValueHashV2)> {
    (0..cell_count)
        .map(|index| (key(index), value(u8::try_from(index).unwrap() + 1)))
        .collect()
}

struct ReferenceTree {
    state: Vec<(CommitmentV3, ValueHashV2)>,
    nodes: BTreeMap<(usize, [u8; 32]), CommitmentV3>,
}

impl ReferenceTree {
    fn new(cell_count: usize) -> Self {
        let state = initial_state(cell_count);
        let mut nodes = BTreeMap::new();
        build_subtree(&mut nodes, 0, [0_u8; 32], &state);
        Self { state, nodes }
    }

    fn root(&self) -> CommitmentV3 {
        self.nodes[&(0, [0_u8; 32])]
    }

    fn value(&self, target_key: CommitmentV3) -> ValueHashV2 {
        self.state
            .iter()
            .find(|(entry_key, _)| *entry_key == target_key)
            .unwrap()
            .1
    }

    fn sibling_path(&self, target_key: CommitmentV3) -> SparseMerkleSiblingPathV1 {
        let mut siblings = [commitment(1); SPARSE_MERKLE_TREE_DEPTH_V1];
        for (depth, sibling) in siblings.iter_mut().enumerate() {
            let prefix = key_prefix(target_key, depth);
            let sibling_prefix = prefix_with_bit(prefix, depth, 1 - path_bit(target_key, depth));
            *sibling = self.nodes[&(depth + 1, sibling_prefix)];
        }
        SparseMerkleSiblingPathV1::new(siblings)
    }

    fn update(&mut self, target_key: CommitmentV3, post_value_hash: ValueHashV2) {
        let position = self
            .state
            .iter()
            .position(|(entry_key, _)| *entry_key == target_key)
            .unwrap();
        self.state[position].1 = post_value_hash;
        let leaf = derive_sparse_merkle_leaf_commitment_v1(target_key, post_value_hash).unwrap();
        self.nodes
            .insert((SPARSE_MERKLE_TREE_DEPTH_V1, *target_key.as_bytes()), leaf);
        for depth in (0..SPARSE_MERKLE_TREE_DEPTH_V1).rev() {
            let prefix = key_prefix(target_key, depth);
            let left = self.nodes[&(depth + 1, prefix_with_bit(prefix, depth, 0))];
            let right = self.nodes[&(depth + 1, prefix_with_bit(prefix, depth, 1))];
            let root = derive_sparse_merkle_internal_commitment_v1(depth, left, right).unwrap();
            self.nodes.insert((depth, prefix), root);
        }
    }
}

fn apply_step(
    tree: &mut ReferenceTree,
    key_index: usize,
    action_seed: u8,
    post_seed: u8,
) -> SparseMerkleBatchEntryV1 {
    let target_key = key(key_index);
    let pre_value_hash = tree.value(target_key);
    let post_value_hash = value(post_seed);
    assert_ne!(pre_value_hash, post_value_hash);
    let claimed_pre_root = tree.root();
    let sibling_commitments = tree.sibling_path(target_key);
    tree.update(target_key, post_value_hash);
    let claimed_post_root = tree.root();
    let economic_action_id = action(action_seed);
    let witness =
        SparseMerkleCellTransitionWitnessV1::new(SparseMerkleCellTransitionWitnessInputV1 {
            witness_version: SPARSE_MERKLE_WITNESS_VERSION_V1,
            economic_action_id,
            cell_key: target_key,
            pre_value_hash,
            post_value_hash,
            sibling_commitments,
            claimed_pre_root,
            claimed_post_root,
        })
        .unwrap();
    let cell_write = LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
        economic_action_id,
        cell_key: target_key,
        pre_value_hash,
        post_value_hash,
    })
    .unwrap();
    SparseMerkleBatchEntryV1::new(SparseMerkleBatchEntryInputV1 {
        cell_write,
        witness,
    })
    .unwrap()
}

pub fn batch_input_for_steps(steps: &[(usize, u8, u8)]) -> SparseMerkleBatchTransitionInputV1 {
    let cell_count = steps
        .iter()
        .map(|(key_index, _, _)| key_index + 1)
        .max()
        .unwrap_or(1);
    let mut tree = ReferenceTree::new(cell_count);
    let batch_pre_root = tree.root();
    let entries = steps
        .iter()
        .map(|(key_index, action_seed, post_seed)| {
            apply_step(&mut tree, *key_index, *action_seed, *post_seed)
        })
        .collect();
    SparseMerkleBatchTransitionInputV1 {
        batch_version: SPARSE_MERKLE_BATCH_VERSION_V1,
        entries,
        batch_pre_root,
        batch_post_root: tree.root(),
    }
}

pub fn canonical_batch_input(count: usize) -> SparseMerkleBatchTransitionInputV1 {
    let steps = (0..count)
        .map(|index| {
            (
                index,
                u8::try_from(index).unwrap() + 0x41,
                u8::try_from(index).unwrap() + 0x81,
            )
        })
        .collect::<Vec<_>>();
    batch_input_for_steps(&steps)
}
