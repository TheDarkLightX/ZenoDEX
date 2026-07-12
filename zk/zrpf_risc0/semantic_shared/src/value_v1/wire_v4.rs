use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    CommitmentV3, PartitionV3, SemanticAssetFlowInputV2, SemanticAssetFlowV2,
    SemanticAuthorityUseInputV2, SemanticAuthorityUseV2, SemanticSubtreeInputV2, SemanticSubtreeV2,
    SemanticValueLeafRecordInputV2, SemanticValueLeafRecordV2,
};

use super::{
    ExpectedSpotSemanticValueMatchV1, SpotSemanticValueProjectionV1, SpotValueSubtreeSummaryV2,
};

mod error;
pub use error::{SpotValueWireErrorV4, SpotValueWireFieldV4};

#[derive(Clone, Debug, PartialEq, Eq)]
/// Exact pure V4 subtree plus a sealed expected Spot projection match.
///
/// This value carries no receipt, ledger, settlement, or release authority.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::SemanticSubtreeV2;
/// use zenodex_zrpf_risc0_semantic_shared::{
///     ExpectedSpotSemanticSubtreeMatchV4, ExpectedSpotSemanticValueMatchV1,
/// };
/// fn bypass(
///     subtree: SemanticSubtreeV2,
///     expected: ExpectedSpotSemanticValueMatchV1,
/// ) -> ExpectedSpotSemanticSubtreeMatchV4 {
///     (subtree, expected).into()
/// }
/// ```
pub struct ExpectedSpotSemanticSubtreeMatchV4 {
    semantic_subtree: SemanticSubtreeV2,
    expected_match: ExpectedSpotSemanticValueMatchV1,
}

impl ExpectedSpotSemanticSubtreeMatchV4 {
    pub const fn semantic_subtree(&self) -> &SemanticSubtreeV2 {
        &self.semantic_subtree
    }

    pub const fn expected_match(&self) -> &ExpectedSpotSemanticValueMatchV1 {
        &self.expected_match
    }

    pub const fn application_statement_hash(&self) -> CommitmentV3 {
        self.expected_match.expected_statement_hash()
    }

    pub const fn semantic_value_root(&self) -> CommitmentV3 {
        self.expected_match.projection().semantic_value_root()
    }
}

/// Translate one sealed Spot V1 summary into the exact generic V4 subtree.
///
/// The bridge independently derives every V4 component root and requires exact
/// equality with the V1 reference roots before returning.
pub fn semantic_subtree_v2_from_spot_summary(
    summary: &SpotValueSubtreeSummaryV2,
) -> Result<SemanticSubtreeV2, SpotValueWireErrorV4> {
    let partition = PartitionV3::new(summary.partition_start, summary.partition_end_exclusive)
        .map_err(SpotValueWireErrorV4::Structural)?;
    let leaf_records = derive_leaf_records(summary)?;
    let asset_flows = summary
        .asset_flows
        .iter()
        .map(semantic_asset_flow)
        .collect::<Result<Vec<_>, _>>()?;
    let authority_uses = summary
        .authority_uses
        .iter()
        .map(semantic_authority_use)
        .collect::<Result<Vec<_>, _>>()?;
    let subtree = SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: super::spot_represented_value_profile_id_v1()?,
        accounting_domain_id: super::spot_accounting_domain_id_v1()?,
        atoms_unit_id: super::spot_atoms_unit_id_v1()?,
        state_root_scheme_id: super::spot_state_root_scheme_id_v1()?,
        scope_hash: summary.scope_hash,
        lane_id_hash: summary.lane_id_hash,
        partition,
        raw_subtree_pre_state_root: commitment(summary.raw_subtree_pre_state_root)?,
        raw_subtree_post_state_root: commitment(summary.raw_subtree_post_state_root)?,
        represented_row_count: summary.represented_row_count,
        leaf_records,
        authority_grants_root: summary.authority_grants_root,
        asset_flows,
        authority_uses,
    })?;
    require_reference_roots(summary, &subtree)?;
    Ok(subtree)
}

/// Bind the exact V4 subtree to a projection already matched against the full
/// expected Spot application statement.
pub fn bind_expected_spot_semantic_subtree_v4(
    summary: &SpotValueSubtreeSummaryV2,
    expected_match: ExpectedSpotSemanticValueMatchV1,
) -> Result<ExpectedSpotSemanticSubtreeMatchV4, SpotValueWireErrorV4> {
    let semantic_subtree = semantic_subtree_v2_from_spot_summary(summary)?;
    require_projection_match(&semantic_subtree, expected_match.projection())?;
    Ok(ExpectedSpotSemanticSubtreeMatchV4 {
        semantic_subtree,
        expected_match,
    })
}

fn derive_leaf_records(
    summary: &SpotValueSubtreeSummaryV2,
) -> Result<Vec<SemanticValueLeafRecordV2>, SpotValueWireErrorV4> {
    if summary.leaves.len() != summary.openings.len() {
        return Err(SpotValueWireErrorV4::ReferenceMismatch(
            SpotValueWireFieldV4::LeafCount,
        ));
    }
    summary
        .leaves
        .iter()
        .zip(&summary.openings)
        .map(|(leaf, opening)| {
            let commitments = leaf.commitments().to_input();
            SemanticValueLeafRecordV2::new(SemanticValueLeafRecordInputV2 {
                partition: leaf.partition(),
                semantic_leaf_hash: leaf
                    .canonical_hash()
                    .map_err(SpotValueWireErrorV4::SemanticLeaf)?,
                source_claim_id: leaf.source_claim_id().into_commitment(),
                semantic_source_id: leaf.semantic_source_id().into_commitment(),
                task_id: leaf.task_id(),
                pre_state_vector_root: commitments.pre_state_vector_root,
                post_state_vector_root: commitments.post_state_vector_root,
                transaction_root: commitments.transaction_root,
                effect_root: commitments.effect_root,
                asset_delta_root: commitments.asset_delta_root,
                raw_pre_state_root: commitment(opening.raw_pre_state_root)?,
                raw_post_state_root: commitment(opening.raw_post_state_root)?,
            })
            .map_err(SpotValueWireErrorV4::ValueNode)
        })
        .collect()
}

fn semantic_asset_flow(
    flow: &super::SpotCanonicalAssetFlowV1,
) -> Result<SemanticAssetFlowV2, SpotValueWireErrorV4> {
    Ok(SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
        asset_id: flow.asset_id,
        outflow_atoms: flow.outflow_atoms,
        inflow_atoms: flow.inflow_atoms,
        issued_atoms: flow.issued_atoms,
        destroyed_atoms: flow.destroyed_atoms,
    })?)
}

fn semantic_authority_use(
    use_record: &super::SpotMintAuthorityUseV1,
) -> Result<SemanticAuthorityUseV2, SpotValueWireErrorV4> {
    Ok(SemanticAuthorityUseV2::new(SemanticAuthorityUseInputV2 {
        source_claim_id: commitment(use_record.source_claim_id)?,
        leaf_ordinal: use_record.leaf_ordinal,
        asset_id: use_record.asset_id,
        atoms: use_record.atoms,
        legacy_authority_root: commitment(use_record.legacy_authority_root)?,
    })?)
}

fn commitment(bytes: [u8; 32]) -> Result<CommitmentV3, SpotValueWireErrorV4> {
    CommitmentV3::new(bytes).map_err(SpotValueWireErrorV4::Structural)
}

fn require_reference_roots(
    summary: &SpotValueSubtreeSummaryV2,
    subtree: &SemanticSubtreeV2,
) -> Result<(), SpotValueWireErrorV4> {
    for (field, actual, expected) in [
        (
            SpotValueWireFieldV4::SemanticLeafRecordsRoot,
            subtree.semantic_leaf_records_root(),
            summary.semantic_leaf_records_root,
        ),
        (
            SpotValueWireFieldV4::OrderedTransactionRootsRoot,
            subtree.ordered_transaction_roots_root(),
            summary.ordered_transaction_roots_root,
        ),
        (
            SpotValueWireFieldV4::StateChainRoot,
            subtree.state_chain_root(),
            summary.state_chain_root,
        ),
        (
            SpotValueWireFieldV4::AssetFlowsRoot,
            subtree.asset_flows_root(),
            summary.asset_flows_root,
        ),
        (
            SpotValueWireFieldV4::AuthorityUsesRoot,
            subtree.authority_uses_root(),
            summary.authority_uses_root,
        ),
        (
            SpotValueWireFieldV4::ValueSubtreeRoot,
            subtree.value_subtree_root(),
            summary.subtree_root,
        ),
    ] {
        if actual != expected {
            return Err(SpotValueWireErrorV4::ReferenceMismatch(field));
        }
    }
    Ok(())
}

fn require_projection_match(
    subtree: &SemanticSubtreeV2,
    projection: &SpotSemanticValueProjectionV1,
) -> Result<(), SpotValueWireErrorV4> {
    require_projection_profile(subtree, projection)?;
    require_projection_shape(subtree, projection)?;
    require_projection_roots(subtree, projection)
}

fn require_projection_profile(
    subtree: &SemanticSubtreeV2,
    projection: &SpotSemanticValueProjectionV1,
) -> Result<(), SpotValueWireErrorV4> {
    let commitments = projection.commitments();
    for (field, actual, expected) in [
        (
            SpotValueWireFieldV4::ScopeHash,
            subtree.scope_hash(),
            projection.scope_hash(),
        ),
        (
            SpotValueWireFieldV4::LaneIdHash,
            subtree.lane_id_hash(),
            projection.lane_id_hash(),
        ),
        (
            SpotValueWireFieldV4::ValueProfileId,
            subtree.value_profile_id(),
            commitments.value_profile_id(),
        ),
        (
            SpotValueWireFieldV4::AccountingDomainId,
            subtree.accounting_domain_id(),
            commitments.accounting_domain_id(),
        ),
        (
            SpotValueWireFieldV4::AtomsUnitId,
            subtree.atoms_unit_id(),
            commitments.atoms_unit_id(),
        ),
        (
            SpotValueWireFieldV4::StateRootSchemeId,
            subtree.state_root_scheme_id(),
            commitments.state_root_scheme_id(),
        ),
    ] {
        require_projection_field(field, actual == expected)?;
    }
    Ok(())
}

fn require_projection_roots(
    subtree: &SemanticSubtreeV2,
    projection: &SpotSemanticValueProjectionV1,
) -> Result<(), SpotValueWireErrorV4> {
    let commitments = projection.commitments();
    for (field, actual, expected) in [
        (
            SpotValueWireFieldV4::SemanticLeafRecordsRoot,
            subtree.semantic_leaf_records_root(),
            commitments.semantic_leaf_records_root(),
        ),
        (
            SpotValueWireFieldV4::OrderedTransactionRootsRoot,
            subtree.ordered_transaction_roots_root(),
            commitments.ordered_transaction_roots_root(),
        ),
        (
            SpotValueWireFieldV4::StateChainRoot,
            subtree.state_chain_root(),
            commitments.state_chain_root(),
        ),
        (
            SpotValueWireFieldV4::AuthorityGrantsRoot,
            subtree.authority_grants_root(),
            commitments.authority_grants_root(),
        ),
        (
            SpotValueWireFieldV4::AssetFlowsRoot,
            subtree.asset_flows_root(),
            commitments.asset_flows_root(),
        ),
        (
            SpotValueWireFieldV4::AuthorityUsesRoot,
            subtree.authority_uses_root(),
            commitments.authority_uses_root(),
        ),
        (
            SpotValueWireFieldV4::ValueSubtreeRoot,
            subtree.value_subtree_root(),
            commitments.value_subtree_root(),
        ),
    ] {
        require_projection_field(field, actual == expected)?;
    }
    Ok(())
}

fn require_projection_shape(
    subtree: &SemanticSubtreeV2,
    projection: &SpotSemanticValueProjectionV1,
) -> Result<(), SpotValueWireErrorV4> {
    require_projection_field(
        SpotValueWireFieldV4::Partition,
        subtree.partition().start() == 0,
    )?;
    require_projection_field(
        SpotValueWireFieldV4::RawPreStateRoot,
        subtree.raw_subtree_pre_state_root().as_bytes() == &projection.raw_epoch_pre_state_root(),
    )?;
    require_projection_field(
        SpotValueWireFieldV4::RawPostStateRoot,
        subtree.raw_subtree_post_state_root().as_bytes() == &projection.raw_epoch_post_state_root(),
    )?;
    require_projection_field(
        SpotValueWireFieldV4::LeafCount,
        subtree.leaf_count() == projection.leaf_count(),
    )?;
    require_projection_field(
        SpotValueWireFieldV4::RepresentedRowCount,
        subtree.represented_row_count() == projection.represented_row_count(),
    )
}

fn require_projection_field(
    field: SpotValueWireFieldV4,
    matches: bool,
) -> Result<(), SpotValueWireErrorV4> {
    if matches {
        Ok(())
    } else {
        Err(SpotValueWireErrorV4::ExpectedProjectionMismatch(field))
    }
}
