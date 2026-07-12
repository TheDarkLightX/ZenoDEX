use alloc::collections::{BTreeMap, BTreeSet};

use crate::{CommitmentV3, PartitionV3};

use super::hash::checked_len_u64;
use super::{SemanticSubtreeInputV2, SemanticSubtreeV2};
use crate::value_node_v4::{
    SemanticAssetFlowV2, SemanticAuthorityUseV2, SemanticValueLeafRecordV2, ValueNodeErrorV4,
    MAX_SEMANTIC_ASSET_FLOWS_V2, MAX_SEMANTIC_AUTHORITY_USES_V2, MAX_SEMANTIC_REPRESENTED_ROWS_V2,
    MAX_SEMANTIC_VALUE_RECORDS_V2,
};

struct ValidationViewV2<'a> {
    partition: PartitionV3,
    raw_pre: CommitmentV3,
    raw_post: CommitmentV3,
    represented_row_count: u64,
    records: &'a [SemanticValueLeafRecordV2],
    flows: &'a [SemanticAssetFlowV2],
    uses: &'a [SemanticAuthorityUseV2],
}

pub(super) fn validate_input(input: &SemanticSubtreeInputV2) -> Result<(), ValueNodeErrorV4> {
    validate_view(ValidationViewV2 {
        partition: input.partition,
        raw_pre: input.raw_subtree_pre_state_root,
        raw_post: input.raw_subtree_post_state_root,
        represented_row_count: input.represented_row_count,
        records: &input.leaf_records,
        flows: &input.asset_flows,
        uses: &input.authority_uses,
    })
}

pub(super) fn validate_subtree(subtree: &SemanticSubtreeV2) -> Result<(), ValueNodeErrorV4> {
    validate_view(ValidationViewV2 {
        partition: subtree.partition,
        raw_pre: subtree.raw_subtree_pre_state_root,
        raw_post: subtree.raw_subtree_post_state_root,
        represented_row_count: subtree.represented_row_count,
        records: &subtree.leaf_records,
        flows: &subtree.asset_flows,
        uses: &subtree.authority_uses,
    })
}

fn validate_view(view: ValidationViewV2<'_>) -> Result<(), ValueNodeErrorV4> {
    validate_records(view.partition, view.raw_pre, view.raw_post, view.records)?;
    validate_flow_shape(view.represented_row_count, view.flows, view.uses)?;
    validate_issuance_uses(view.partition, view.records, view.flows, view.uses)
}

fn validate_records(
    partition: PartitionV3,
    raw_pre: CommitmentV3,
    raw_post: CommitmentV3,
    records: &[SemanticValueLeafRecordV2],
) -> Result<(), ValueNodeErrorV4> {
    validate_record_bounds(partition, records)?;
    let mut identities = IdentitySetsV2::default();
    for (ordinal, record) in records.iter().enumerate() {
        validate_record_at(partition, records, ordinal, record)?;
        identities.insert(record)?;
    }
    if records[0].raw_pre_state_root != raw_pre
        || records[records.len() - 1].raw_post_state_root != raw_post
    {
        return Err(ValueNodeErrorV4::SubtreeEndpointMismatch);
    }
    Ok(())
}

fn validate_record_bounds(
    partition: PartitionV3,
    records: &[SemanticValueLeafRecordV2],
) -> Result<(), ValueNodeErrorV4> {
    if records.is_empty() {
        return Err(ValueNodeErrorV4::EmptyLeafRecords);
    }
    if records.len() > MAX_SEMANTIC_VALUE_RECORDS_V2 {
        return Err(ValueNodeErrorV4::TooManyLeafRecords {
            actual: records.len(),
            maximum: MAX_SEMANTIC_VALUE_RECORDS_V2,
        });
    }
    let record_count = checked_len_u64(records.len(), "leaf_count")?;
    let partition_width = partition
        .end_exclusive()
        .checked_sub(partition.start())
        .ok_or(ValueNodeErrorV4::SubtreePartitionMismatch)?;
    if partition_width != record_count {
        return Err(ValueNodeErrorV4::SubtreePartitionMismatch);
    }
    Ok(())
}

fn validate_record_at(
    partition: PartitionV3,
    records: &[SemanticValueLeafRecordV2],
    ordinal: usize,
    record: &SemanticValueLeafRecordV2,
) -> Result<(), ValueNodeErrorV4> {
    record.validate(ordinal)?;
    let offset =
        u64::try_from(ordinal).map_err(|_| ValueNodeErrorV4::ArithmeticOverflow("leaf_ordinal"))?;
    let expected_start = partition
        .start()
        .checked_add(offset)
        .ok_or(ValueNodeErrorV4::ArithmeticOverflow("leaf_partition"))?;
    let expected_end = expected_start
        .checked_add(1)
        .ok_or(ValueNodeErrorV4::ArithmeticOverflow("leaf_partition"))?;
    if record.partition.start() != expected_start
        || record.partition.end_exclusive() != expected_end
    {
        return Err(ValueNodeErrorV4::NonCanonicalLeafOrder { ordinal });
    }
    if ordinal > 0 && records[ordinal - 1].raw_post_state_root != record.raw_pre_state_root {
        return Err(ValueNodeErrorV4::StateDiscontinuity { ordinal });
    }
    Ok(())
}

#[derive(Default)]
struct IdentitySetsV2 {
    source_claims: BTreeSet<CommitmentV3>,
    semantic_sources: BTreeSet<CommitmentV3>,
    tasks: BTreeSet<crate::TaskIdV3>,
    transactions: BTreeSet<CommitmentV3>,
}

impl IdentitySetsV2 {
    fn insert(&mut self, record: &SemanticValueLeafRecordV2) -> Result<(), ValueNodeErrorV4> {
        if !self.source_claims.insert(record.source_claim_id) {
            return Err(ValueNodeErrorV4::DuplicateSourceClaim);
        }
        if !self.semantic_sources.insert(record.semantic_source_id) {
            return Err(ValueNodeErrorV4::DuplicateSemanticSource);
        }
        if !self.tasks.insert(record.task_id) {
            return Err(ValueNodeErrorV4::DuplicateTask);
        }
        if !self.transactions.insert(record.transaction_root) {
            return Err(ValueNodeErrorV4::DuplicateTransactionRoot);
        }
        Ok(())
    }
}

fn validate_flow_shape(
    represented_row_count: u64,
    flows: &[SemanticAssetFlowV2],
    uses: &[SemanticAuthorityUseV2],
) -> Result<(), ValueNodeErrorV4> {
    validate_summary_bounds(represented_row_count, flows.len(), uses.len())?;
    for flow in flows {
        flow.validate()?;
    }
    if flows
        .windows(2)
        .any(|pair| pair[0].asset_id >= pair[1].asset_id)
    {
        return Err(ValueNodeErrorV4::NonCanonicalAssetFlowOrder);
    }
    for use_record in uses {
        use_record.validate()?;
    }
    if uses
        .windows(2)
        .any(|pair| authority_use_key(&pair[0]) >= authority_use_key(&pair[1]))
    {
        return Err(ValueNodeErrorV4::NonCanonicalAuthorityUseOrder);
    }
    Ok(())
}

fn validate_summary_bounds(
    represented_row_count: u64,
    flow_count: usize,
    use_count: usize,
) -> Result<(), ValueNodeErrorV4> {
    if represented_row_count > MAX_SEMANTIC_REPRESENTED_ROWS_V2 {
        return Err(ValueNodeErrorV4::RepresentedRowLimitExceeded {
            actual: represented_row_count,
            maximum: MAX_SEMANTIC_REPRESENTED_ROWS_V2,
        });
    }
    if flow_count > MAX_SEMANTIC_ASSET_FLOWS_V2 {
        return Err(ValueNodeErrorV4::TooManyAssetFlows {
            actual: flow_count,
            maximum: MAX_SEMANTIC_ASSET_FLOWS_V2,
        });
    }
    if use_count > MAX_SEMANTIC_AUTHORITY_USES_V2 {
        return Err(ValueNodeErrorV4::TooManyAuthorityUses {
            actual: use_count,
            maximum: MAX_SEMANTIC_AUTHORITY_USES_V2,
        });
    }
    let row_count = usize::try_from(represented_row_count)
        .map_err(|_| ValueNodeErrorV4::ArithmeticOverflow("represented_row_count"))?;
    if (row_count == 0 && (flow_count != 0 || use_count != 0))
        || (row_count > 0 && flow_count == 0)
        || flow_count > row_count
        || use_count > row_count
    {
        return Err(ValueNodeErrorV4::InvalidRepresentedRowShape);
    }
    Ok(())
}

fn validate_issuance_uses(
    partition: PartitionV3,
    records: &[SemanticValueLeafRecordV2],
    flows: &[SemanticAssetFlowV2],
    uses: &[SemanticAuthorityUseV2],
) -> Result<(), ValueNodeErrorV4> {
    let issued_by_asset = flows
        .iter()
        .map(|flow| (flow.asset_id, flow.issued_atoms))
        .collect::<BTreeMap<_, _>>();
    let mut used_by_asset = BTreeMap::<[u8; 32], u128>::new();
    for use_record in uses {
        validate_authority_source(partition, records, use_record)?;
        let prior = used_by_asset.entry(use_record.asset_id).or_insert(0);
        *prior = prior
            .checked_add(use_record.atoms)
            .ok_or(ValueNodeErrorV4::ArithmeticOverflow("authority_use_atoms"))?;
    }
    if issued_by_asset
        .iter()
        .any(|(asset_id, issued)| used_by_asset.get(asset_id).copied().unwrap_or(0) != *issued)
        || used_by_asset
            .keys()
            .any(|asset_id| !issued_by_asset.contains_key(asset_id))
    {
        return Err(ValueNodeErrorV4::IssuanceUseMismatch);
    }
    Ok(())
}

fn validate_authority_source(
    partition: PartitionV3,
    records: &[SemanticValueLeafRecordV2],
    use_record: &SemanticAuthorityUseV2,
) -> Result<(), ValueNodeErrorV4> {
    if use_record.leaf_ordinal < partition.start()
        || use_record.leaf_ordinal >= partition.end_exclusive()
    {
        return Err(ValueNodeErrorV4::AuthorityUseOutsidePartition);
    }
    let offset = use_record
        .leaf_ordinal
        .checked_sub(partition.start())
        .ok_or(ValueNodeErrorV4::AuthorityUseOutsidePartition)?;
    let index = usize::try_from(offset)
        .map_err(|_| ValueNodeErrorV4::ArithmeticOverflow("authority_leaf_ordinal"))?;
    if records[index].source_claim_id != use_record.source_claim_id {
        return Err(ValueNodeErrorV4::AuthorityUseSourceMismatch);
    }
    Ok(())
}

fn authority_use_key(use_record: &SemanticAuthorityUseV2) -> ([u8; 32], u64, [u8; 32]) {
    (
        use_record.asset_id,
        use_record.leaf_ordinal,
        use_record.source_claim_id.into_bytes(),
    )
}
