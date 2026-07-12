use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use super::{SemanticSubtreeInputV2, SemanticSubtreeV2};
use crate::value_node_v4::{
    SemanticAssetFlowInputV2, SemanticAssetFlowV2, SemanticAuthorityUseV2, ValueNodeErrorV4,
    MAX_SEMANTIC_ASSET_FLOWS_V2, MAX_SEMANTIC_AUTHORITY_USES_V2, MAX_SEMANTIC_REPRESENTED_ROWS_V2,
    MAX_SEMANTIC_VALUE_RECORDS_V2,
};
use crate::{CommitmentV3, PartitionV3, MAX_IMMEDIATE_CHILDREN_V3};

#[derive(Clone, Copy, Default)]
struct FlowTotalsV2 {
    outflow_atoms: u128,
    inflow_atoms: u128,
    issued_atoms: u128,
    destroyed_atoms: u128,
}

impl FlowTotalsV2 {
    fn add(&mut self, flow: SemanticAssetFlowV2) -> Result<(), ValueNodeErrorV4> {
        self.outflow_atoms =
            checked_add(self.outflow_atoms, flow.outflow_atoms(), "outflow_atoms")?;
        self.inflow_atoms = checked_add(self.inflow_atoms, flow.inflow_atoms(), "inflow_atoms")?;
        self.issued_atoms = checked_add(self.issued_atoms, flow.issued_atoms(), "issued_atoms")?;
        self.destroyed_atoms = checked_add(
            self.destroyed_atoms,
            flow.destroyed_atoms(),
            "destroyed_atoms",
        )?;
        Ok(())
    }
}

#[derive(Default)]
struct MergeStateV2 {
    leaf_records: Vec<crate::value_node_v4::SemanticValueLeafRecordV2>,
    authority_uses: Vec<SemanticAuthorityUseV2>,
    flows: BTreeMap<[u8; 32], FlowTotalsV2>,
    represented_row_count: u64,
    prior: Option<(u64, CommitmentV3)>,
}

impl MergeStateV2 {
    fn absorb(&mut self, child: &SemanticSubtreeV2, index: usize) -> Result<(), ValueNodeErrorV4> {
        require_order_and_continuity(self.prior, child, index)?;
        extend_bounded(
            &mut self.leaf_records,
            child.leaf_records(),
            MAX_SEMANTIC_VALUE_RECORDS_V2,
            "semantic_leaf_records",
        )?;
        extend_bounded(
            &mut self.authority_uses,
            child.authority_uses(),
            MAX_SEMANTIC_AUTHORITY_USES_V2,
            "semantic_authority_uses",
        )?;
        self.represented_row_count =
            checked_row_sum(self.represented_row_count, child.represented_row_count())?;
        merge_flows(&mut self.flows, child.asset_flows())?;
        self.prior = Some((
            child.partition().end_exclusive(),
            child.raw_subtree_post_state_root(),
        ));
        Ok(())
    }
}

/// Merge ordered, self-consistent child subtrees into one canonical summary.
///
/// Inputs are never silently reordered. Global identity uniqueness, state
/// continuity, issuance authority, and every derived root are rechecked by the
/// output constructor. This pure operation authenticates no receipt.
pub fn merge_semantic_subtrees_v2(
    children: &[SemanticSubtreeV2],
) -> Result<SemanticSubtreeV2, ValueNodeErrorV4> {
    validate_child_count(children.len())?;
    for child in children {
        child.validate()?;
    }
    let first = &children[0];
    let mut state = MergeStateV2::default();
    for (index, child) in children.iter().enumerate() {
        require_shared_metadata(first, child, index)?;
        state.absorb(child, index)?;
    }

    state.authority_uses.sort_by_key(authority_use_key);
    let asset_flows = canonical_flows(state.flows)?;
    let last = &children[children.len() - 1];
    SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: first.value_profile_id(),
        accounting_domain_id: first.accounting_domain_id(),
        atoms_unit_id: first.atoms_unit_id(),
        state_root_scheme_id: first.state_root_scheme_id(),
        scope_hash: first.scope_hash(),
        lane_id_hash: first.lane_id_hash(),
        partition: PartitionV3::new(first.partition().start(), last.partition().end_exclusive())?,
        raw_subtree_pre_state_root: first.raw_subtree_pre_state_root(),
        raw_subtree_post_state_root: last.raw_subtree_post_state_root(),
        represented_row_count: state.represented_row_count,
        leaf_records: state.leaf_records,
        authority_grants_root: first.authority_grants_root(),
        asset_flows,
        authority_uses: state.authority_uses,
    })
}

fn validate_child_count(count: usize) -> Result<(), ValueNodeErrorV4> {
    if count == 0 {
        return Err(ValueNodeErrorV4::EmptySemanticChildren);
    }
    if count > MAX_IMMEDIATE_CHILDREN_V3 {
        return Err(ValueNodeErrorV4::TooManySemanticChildren {
            actual: count,
            maximum: MAX_IMMEDIATE_CHILDREN_V3,
        });
    }
    Ok(())
}

fn require_shared_metadata(
    expected: &SemanticSubtreeV2,
    child: &SemanticSubtreeV2,
    index: usize,
) -> Result<(), ValueNodeErrorV4> {
    for (field, actual, required) in [
        (
            "value_profile_id",
            child.value_profile_id(),
            expected.value_profile_id(),
        ),
        (
            "accounting_domain_id",
            child.accounting_domain_id(),
            expected.accounting_domain_id(),
        ),
        (
            "atoms_unit_id",
            child.atoms_unit_id(),
            expected.atoms_unit_id(),
        ),
        (
            "state_root_scheme_id",
            child.state_root_scheme_id(),
            expected.state_root_scheme_id(),
        ),
        ("scope_hash", child.scope_hash(), expected.scope_hash()),
        (
            "lane_id_hash",
            child.lane_id_hash(),
            expected.lane_id_hash(),
        ),
        (
            "authority_grants_root",
            child.authority_grants_root(),
            expected.authority_grants_root(),
        ),
    ] {
        if actual != required {
            return Err(ValueNodeErrorV4::SemanticChildMetadataMismatch {
                child: index,
                field,
            });
        }
    }
    Ok(())
}

fn require_order_and_continuity(
    prior: Option<(u64, CommitmentV3)>,
    child: &SemanticSubtreeV2,
    index: usize,
) -> Result<(), ValueNodeErrorV4> {
    if let Some((expected_start, expected_pre)) = prior {
        if child.partition().start() != expected_start {
            return Err(ValueNodeErrorV4::NonCanonicalSemanticChildOrder { child: index });
        }
        if child.raw_subtree_pre_state_root() != expected_pre {
            return Err(ValueNodeErrorV4::SemanticChildStateDiscontinuity { child: index });
        }
    }
    Ok(())
}

fn extend_bounded<T: Clone>(
    output: &mut Vec<T>,
    values: &[T],
    maximum: usize,
    field: &'static str,
) -> Result<(), ValueNodeErrorV4> {
    let next = output
        .len()
        .checked_add(values.len())
        .ok_or(ValueNodeErrorV4::ArithmeticOverflow(field))?;
    if next > maximum {
        return Err(ValueNodeErrorV4::SemanticMergeLimitExceeded {
            field,
            actual: next,
            maximum,
        });
    }
    output.extend_from_slice(values);
    Ok(())
}

fn merge_flows(
    output: &mut BTreeMap<[u8; 32], FlowTotalsV2>,
    flows: &[SemanticAssetFlowV2],
) -> Result<(), ValueNodeErrorV4> {
    for flow in flows {
        let is_new = !output.contains_key(&flow.asset_id());
        if is_new && output.len() == MAX_SEMANTIC_ASSET_FLOWS_V2 {
            return Err(ValueNodeErrorV4::TooManyAssetFlows {
                actual: output.len() + 1,
                maximum: MAX_SEMANTIC_ASSET_FLOWS_V2,
            });
        }
        output.entry(flow.asset_id()).or_default().add(*flow)?;
    }
    Ok(())
}

fn checked_row_sum(left: u64, right: u64) -> Result<u64, ValueNodeErrorV4> {
    let total = left
        .checked_add(right)
        .ok_or(ValueNodeErrorV4::ArithmeticOverflow(
            "represented_row_count",
        ))?;
    if total > MAX_SEMANTIC_REPRESENTED_ROWS_V2 {
        return Err(ValueNodeErrorV4::RepresentedRowLimitExceeded {
            actual: total,
            maximum: MAX_SEMANTIC_REPRESENTED_ROWS_V2,
        });
    }
    Ok(total)
}

fn canonical_flows(
    flows: BTreeMap<[u8; 32], FlowTotalsV2>,
) -> Result<Vec<SemanticAssetFlowV2>, ValueNodeErrorV4> {
    flows
        .into_iter()
        .map(|(asset_id, totals)| {
            SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
                asset_id,
                outflow_atoms: totals.outflow_atoms,
                inflow_atoms: totals.inflow_atoms,
                issued_atoms: totals.issued_atoms,
                destroyed_atoms: totals.destroyed_atoms,
            })
        })
        .collect()
}

fn authority_use_key(use_record: &SemanticAuthorityUseV2) -> ([u8; 32], u64, [u8; 32]) {
    (
        use_record.asset_id(),
        use_record.leaf_ordinal(),
        use_record.source_claim_id().into_bytes(),
    )
}

fn checked_add(left: u128, right: u128, field: &'static str) -> Result<u128, ValueNodeErrorV4> {
    left.checked_add(right)
        .ok_or(ValueNodeErrorV4::ArithmeticOverflow(field))
}
