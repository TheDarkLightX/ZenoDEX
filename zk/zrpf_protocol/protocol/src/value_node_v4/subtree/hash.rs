use sha2::{Digest, Sha256};

use crate::{CommitmentV3, PartitionV3};

use super::{SemanticSubtreeInputV2, SemanticSubtreeV2};
use crate::value_node_v4::{
    SemanticAssetFlowV2, SemanticAuthorityUseV2, SemanticValueLeafRecordV2, ValueNodeErrorV4,
};

const SEMANTIC_LEAF_RECORDS_ROOT_DOMAIN_V2: &[u8] =
    b"zenodex.zrpf.spot_semantic_leaf_records_root.v2";
const ORDERED_TRANSACTION_ROOTS_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.spot_ordered_transaction_roots_root.v1";
const STATE_CHAIN_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_state_chain_root.v1";
const ASSET_FLOWS_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_asset_flows_root.v1";
const AUTHORITY_USES_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_authority_uses_root.v1";
const VALUE_SUBTREE_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.spot_value_subtree_root.v2";

pub(super) struct DerivedSemanticRootsV2 {
    pub(super) semantic_leaf_records_root: CommitmentV3,
    pub(super) ordered_transaction_roots_root: CommitmentV3,
    pub(super) state_chain_root: CommitmentV3,
    pub(super) asset_flows_root: CommitmentV3,
    pub(super) authority_uses_root: CommitmentV3,
    pub(super) value_subtree_root: CommitmentV3,
}

struct ComponentRootsV2 {
    semantic_leaf_records_root: CommitmentV3,
    ordered_transaction_roots_root: CommitmentV3,
    state_chain_root: CommitmentV3,
    asset_flows_root: CommitmentV3,
    authority_uses_root: CommitmentV3,
}

struct SemanticRootMaterialV2<'a> {
    value_profile_id: CommitmentV3,
    accounting_domain_id: CommitmentV3,
    atoms_unit_id: CommitmentV3,
    state_root_scheme_id: CommitmentV3,
    scope_hash: CommitmentV3,
    lane_id_hash: CommitmentV3,
    partition: PartitionV3,
    raw_subtree_pre_state_root: CommitmentV3,
    raw_subtree_post_state_root: CommitmentV3,
    represented_row_count: u64,
    leaf_records: &'a [SemanticValueLeafRecordV2],
    authority_grants_root: CommitmentV3,
    asset_flows: &'a [SemanticAssetFlowV2],
    authority_uses: &'a [SemanticAuthorityUseV2],
}

pub(super) fn derive_roots_from_input(
    input: &SemanticSubtreeInputV2,
    leaf_count: u64,
) -> Result<DerivedSemanticRootsV2, ValueNodeErrorV4> {
    derive_roots(material_from_input(input), leaf_count)
}

pub(super) fn derive_roots_from_subtree(
    subtree: &SemanticSubtreeV2,
) -> Result<DerivedSemanticRootsV2, ValueNodeErrorV4> {
    derive_roots(material_from_subtree(subtree), subtree.leaf_count)
}

fn material_from_input(input: &SemanticSubtreeInputV2) -> SemanticRootMaterialV2<'_> {
    SemanticRootMaterialV2 {
        value_profile_id: input.value_profile_id,
        accounting_domain_id: input.accounting_domain_id,
        atoms_unit_id: input.atoms_unit_id,
        state_root_scheme_id: input.state_root_scheme_id,
        scope_hash: input.scope_hash,
        lane_id_hash: input.lane_id_hash,
        partition: input.partition,
        raw_subtree_pre_state_root: input.raw_subtree_pre_state_root,
        raw_subtree_post_state_root: input.raw_subtree_post_state_root,
        represented_row_count: input.represented_row_count,
        leaf_records: &input.leaf_records,
        authority_grants_root: input.authority_grants_root,
        asset_flows: &input.asset_flows,
        authority_uses: &input.authority_uses,
    }
}

fn material_from_subtree(subtree: &SemanticSubtreeV2) -> SemanticRootMaterialV2<'_> {
    SemanticRootMaterialV2 {
        value_profile_id: subtree.value_profile_id,
        accounting_domain_id: subtree.accounting_domain_id,
        atoms_unit_id: subtree.atoms_unit_id,
        state_root_scheme_id: subtree.state_root_scheme_id,
        scope_hash: subtree.scope_hash,
        lane_id_hash: subtree.lane_id_hash,
        partition: subtree.partition,
        raw_subtree_pre_state_root: subtree.raw_subtree_pre_state_root,
        raw_subtree_post_state_root: subtree.raw_subtree_post_state_root,
        represented_row_count: subtree.represented_row_count,
        leaf_records: &subtree.leaf_records,
        authority_grants_root: subtree.authority_grants_root,
        asset_flows: &subtree.asset_flows,
        authority_uses: &subtree.authority_uses,
    }
}

fn derive_roots(
    material: SemanticRootMaterialV2<'_>,
    leaf_count: u64,
) -> Result<DerivedSemanticRootsV2, ValueNodeErrorV4> {
    let components = ComponentRootsV2 {
        semantic_leaf_records_root: semantic_leaf_records_root(material.leaf_records)?,
        ordered_transaction_roots_root: ordered_transaction_roots_root(material.leaf_records)?,
        state_chain_root: state_chain_root(material.leaf_records)?,
        asset_flows_root: asset_flows_root(material.asset_flows)?,
        authority_uses_root: authority_uses_root(material.authority_uses)?,
    };
    let value_subtree_root = value_subtree_root(&material, leaf_count, &components)?;
    Ok(DerivedSemanticRootsV2 {
        semantic_leaf_records_root: components.semantic_leaf_records_root,
        ordered_transaction_roots_root: components.ordered_transaction_roots_root,
        state_chain_root: components.state_chain_root,
        asset_flows_root: components.asset_flows_root,
        authority_uses_root: components.authority_uses_root,
        value_subtree_root,
    })
}

fn semantic_leaf_records_root(
    records: &[SemanticValueLeafRecordV2],
) -> Result<CommitmentV3, ValueNodeErrorV4> {
    let mut hasher = domain_hasher(SEMANTIC_LEAF_RECORDS_ROOT_DOMAIN_V2)?;
    write_u32(
        &mut hasher,
        checked_len_u32(records.len(), "semantic_leaf_count")?,
    );
    for record in records {
        write_commitment(&mut hasher, record.semantic_leaf_hash);
    }
    commitment(hasher.finalize().into())
}

fn ordered_transaction_roots_root(
    records: &[SemanticValueLeafRecordV2],
) -> Result<CommitmentV3, ValueNodeErrorV4> {
    let mut hasher = domain_hasher(ORDERED_TRANSACTION_ROOTS_DOMAIN_V1)?;
    write_u32(
        &mut hasher,
        checked_len_u32(records.len(), "transaction_count")?,
    );
    for record in records {
        write_commitment(&mut hasher, record.transaction_root);
    }
    commitment(hasher.finalize().into())
}

fn state_chain_root(
    records: &[SemanticValueLeafRecordV2],
) -> Result<CommitmentV3, ValueNodeErrorV4> {
    let mut hasher = domain_hasher(STATE_CHAIN_ROOT_DOMAIN_V1)?;
    write_u32(
        &mut hasher,
        checked_len_u32(records.len(), "state_record_count")?,
    );
    for record in records {
        write_commitment(&mut hasher, record.source_claim_id);
        write_u64(&mut hasher, record.partition.start());
        write_commitment(&mut hasher, record.transaction_root);
        write_commitment(&mut hasher, record.raw_pre_state_root);
        write_commitment(&mut hasher, record.raw_post_state_root);
    }
    commitment(hasher.finalize().into())
}

fn asset_flows_root(flows: &[SemanticAssetFlowV2]) -> Result<CommitmentV3, ValueNodeErrorV4> {
    let mut hasher = domain_hasher(ASSET_FLOWS_ROOT_DOMAIN_V1)?;
    write_asset_flows(&mut hasher, flows)?;
    commitment(hasher.finalize().into())
}

fn authority_uses_root(uses: &[SemanticAuthorityUseV2]) -> Result<CommitmentV3, ValueNodeErrorV4> {
    let mut hasher = domain_hasher(AUTHORITY_USES_ROOT_DOMAIN_V1)?;
    write_authority_uses(&mut hasher, uses)?;
    commitment(hasher.finalize().into())
}

fn value_subtree_root(
    material: &SemanticRootMaterialV2<'_>,
    leaf_count: u64,
    roots: &ComponentRootsV2,
) -> Result<CommitmentV3, ValueNodeErrorV4> {
    let mut hasher = domain_hasher(VALUE_SUBTREE_ROOT_DOMAIN_V2)?;
    for value in [
        material.value_profile_id,
        material.accounting_domain_id,
        material.atoms_unit_id,
        material.state_root_scheme_id,
        material.scope_hash,
        material.lane_id_hash,
    ] {
        write_commitment(&mut hasher, value);
    }
    write_u64(&mut hasher, material.partition.start());
    write_u64(&mut hasher, material.partition.end_exclusive());
    write_commitment(&mut hasher, material.raw_subtree_pre_state_root);
    write_commitment(&mut hasher, material.raw_subtree_post_state_root);
    write_u64(&mut hasher, leaf_count);
    write_u64(&mut hasher, material.represented_row_count);
    for value in [
        roots.semantic_leaf_records_root,
        roots.ordered_transaction_roots_root,
        roots.state_chain_root,
        material.authority_grants_root,
        roots.asset_flows_root,
        roots.authority_uses_root,
    ] {
        write_commitment(&mut hasher, value);
    }
    commitment(hasher.finalize().into())
}

pub(super) fn write_leaf_records(
    hasher: &mut Sha256,
    records: &[SemanticValueLeafRecordV2],
) -> Result<(), ValueNodeErrorV4> {
    write_u32(hasher, checked_len_u32(records.len(), "leaf_record_count")?);
    for record in records {
        write_u64(hasher, record.partition.start());
        write_u64(hasher, record.partition.end_exclusive());
        for value in [
            record.semantic_leaf_hash,
            record.source_claim_id,
            record.semantic_source_id,
        ] {
            write_commitment(hasher, value);
        }
        hasher.update(record.task_id.as_bytes());
        for value in [
            record.pre_state_vector_root,
            record.post_state_vector_root,
            record.transaction_root,
            record.effect_root,
            record.asset_delta_root,
            record.raw_pre_state_root,
            record.raw_post_state_root,
        ] {
            write_commitment(hasher, value);
        }
    }
    Ok(())
}

pub(super) fn write_asset_flows(
    hasher: &mut Sha256,
    flows: &[SemanticAssetFlowV2],
) -> Result<(), ValueNodeErrorV4> {
    write_u32(hasher, checked_len_u32(flows.len(), "asset_flow_count")?);
    for flow in flows {
        hasher.update(flow.asset_id);
        write_u128(hasher, flow.outflow_atoms);
        write_u128(hasher, flow.inflow_atoms);
        write_u128(hasher, flow.issued_atoms);
        write_u128(hasher, flow.destroyed_atoms);
    }
    Ok(())
}

pub(super) fn write_authority_uses(
    hasher: &mut Sha256,
    uses: &[SemanticAuthorityUseV2],
) -> Result<(), ValueNodeErrorV4> {
    write_u32(hasher, checked_len_u32(uses.len(), "authority_use_count")?);
    for use_record in uses {
        write_commitment(hasher, use_record.source_claim_id);
        write_u64(hasher, use_record.leaf_ordinal);
        hasher.update(use_record.asset_id);
        write_u128(hasher, use_record.atoms);
        write_commitment(hasher, use_record.legacy_authority_root);
    }
    Ok(())
}

pub(super) fn require_root(
    actual: CommitmentV3,
    expected: CommitmentV3,
    field: &'static str,
) -> Result<(), ValueNodeErrorV4> {
    if actual != expected {
        return Err(ValueNodeErrorV4::CommitmentMismatch(field));
    }
    Ok(())
}

pub(in crate::value_node_v4) fn domain_hasher(domain: &[u8]) -> Result<Sha256, ValueNodeErrorV4> {
    let length = u16::try_from(domain.len())
        .map_err(|_| ValueNodeErrorV4::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

pub(in crate::value_node_v4) fn commitment(
    bytes: [u8; 32],
) -> Result<CommitmentV3, ValueNodeErrorV4> {
    CommitmentV3::new(bytes).map_err(ValueNodeErrorV4::Structural)
}

pub(in crate::value_node_v4) fn write_commitment(hasher: &mut Sha256, value: CommitmentV3) {
    hasher.update(value.as_bytes());
}

pub(in crate::value_node_v4) fn write_u16(hasher: &mut Sha256, value: u16) {
    hasher.update(value.to_be_bytes());
}

pub(in crate::value_node_v4) fn write_u32(hasher: &mut Sha256, value: u32) {
    hasher.update(value.to_be_bytes());
}

pub(super) fn write_u64(hasher: &mut Sha256, value: u64) {
    hasher.update(value.to_be_bytes());
}

fn write_u128(hasher: &mut Sha256, value: u128) {
    hasher.update(value.to_be_bytes());
}

pub(in crate::value_node_v4) fn checked_len_u32(
    length: usize,
    field: &'static str,
) -> Result<u32, ValueNodeErrorV4> {
    u32::try_from(length).map_err(|_| ValueNodeErrorV4::ArithmeticOverflow(field))
}

pub(super) fn checked_len_u64(length: usize, field: &'static str) -> Result<u64, ValueNodeErrorV4> {
    u64::try_from(length).map_err(|_| ValueNodeErrorV4::ArithmeticOverflow(field))
}
