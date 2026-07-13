use super::hash::*;
use super::*;

pub(super) fn validate_subtree_inputs(
    leaves: &[ProposedSemanticLeafV1],
    openings: &[SpotValueLeafOpeningV1],
    policy: &SpotRepresentedValuePolicyV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    if leaves.is_empty() {
        return Err(SpotSemanticValueErrorV1::EmptyLeaves);
    }
    if leaves.len() > MAX_SPOT_VALUE_SUBTREE_LEAVES_V2 {
        return Err(SpotSemanticValueErrorV1::TooManyLeaves {
            actual: leaves.len(),
            maximum: MAX_SPOT_VALUE_SUBTREE_LEAVES_V2,
        });
    }
    if leaves.len() != openings.len() {
        return Err(SpotSemanticValueErrorV1::OpeningCountMismatch);
    }
    let first = &leaves[0];
    if first.scope().epoch_start() != first.scope().epoch_end() {
        return Err(SpotSemanticValueErrorV1::EpochRangeUnsupported);
    }
    if first.scope().public_policy_hash().as_bytes() != &policy.public_policy_hash {
        return Err(SpotSemanticValueErrorV1::PublicPolicyMismatch);
    }
    validate_subtree_leaf_sequence(leaves)
}

fn validate_subtree_leaf_sequence(
    leaves: &[ProposedSemanticLeafV1],
) -> Result<(), SpotSemanticValueErrorV1> {
    let first = &leaves[0];
    let mut prior_end = first.partition().start();
    let mut source_claims = BTreeSet::new();
    let mut semantic_sources = BTreeSet::new();
    let mut tasks = BTreeSet::new();
    for (ordinal, leaf) in leaves.iter().enumerate() {
        leaf.canonical_hash()
            .map_err(SpotSemanticValueErrorV1::Protocol)?;
        let partition = leaf.partition();
        if partition.start() != prior_end
            || partition.end_exclusive() != partition.start().saturating_add(1)
        {
            return Err(SpotSemanticValueErrorV1::NonCanonicalSubtreeLeaves);
        }
        if leaf.scope() != first.scope() {
            return Err(SpotSemanticValueErrorV1::SubtreeScopeMismatch { ordinal });
        }
        if leaf.count_unit_id() != first.count_unit_id()
            || leaf.leaf_program_id() != first.leaf_program_id()
            || leaf.leaf_profile_id() != first.leaf_profile_id()
        {
            return Err(SpotSemanticValueErrorV1::NonCanonicalSubtreeLeaves);
        }
        if !source_claims.insert(*leaf.source_claim_id().as_bytes()) {
            return Err(SpotSemanticValueErrorV1::DuplicateSubtreeIdentity {
                field: "source claim",
            });
        }
        if !semantic_sources.insert(*leaf.semantic_source_id().as_bytes()) {
            return Err(SpotSemanticValueErrorV1::DuplicateSubtreeIdentity {
                field: "semantic source",
            });
        }
        if !tasks.insert(*leaf.task_id().as_bytes()) {
            return Err(SpotSemanticValueErrorV1::DuplicateSubtreeIdentity { field: "task" });
        }
        prior_end = partition.end_exclusive();
    }
    Ok(())
}

pub(super) fn bind_leaf(
    ordinal: usize,
    leaf: &ProposedSemanticLeafV1,
    opening: &SpotValueLeafOpeningV1,
    policy: &SpotRepresentedValuePolicyV1,
    state: &mut CompositionStateV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    validate_lane_and_state(ordinal, opening, state)?;
    let commitments = leaf.commitments().to_input();
    validate_state_commitments(
        ordinal,
        opening,
        commitments.pre_state_vector_root,
        commitments.post_state_vector_root,
    )?;
    let transaction_root = commitments.transaction_root.into_bytes();
    if !state.transaction_roots.insert(transaction_root) {
        return Err(SpotSemanticValueErrorV1::DuplicateTransactionRoot { ordinal });
    }
    validate_row_bound(ordinal, opening.asset_rows.len(), state.row_count)?;
    validate_asset_rows_root(ordinal, opening.asset_rows(), commitments.asset_delta_root)?;
    for (row_index, row) in opening.asset_rows().iter().enumerate() {
        accumulate_row(
            RowValidationContextV1 {
                ordinal,
                row_index,
                leaf,
                policy,
            },
            row,
            state,
        )?;
    }
    state.row_count = state
        .row_count
        .checked_add(opening.asset_rows.len())
        .ok_or(SpotSemanticValueErrorV1::ArithmeticOverflow("row_count"))?;
    state.state_records.push(StateRecordV1 {
        source_claim_id: *leaf.source_claim_id().as_bytes(),
        leaf_ordinal: leaf.partition().start(),
        transaction_root,
        raw_pre_state_root: opening.raw_pre_state_root,
        raw_post_state_root: opening.raw_post_state_root,
    });
    state.previous_post = Some(opening.raw_post_state_root);
    Ok(())
}

fn validate_lane_and_state(
    ordinal: usize,
    opening: &SpotValueLeafOpeningV1,
    state: &mut CompositionStateV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    if !valid_lane_id(&opening.lane_id) {
        return Err(SpotSemanticValueErrorV1::InvalidLaneId);
    }
    match &state.lane_id {
        Some(expected) if expected != &opening.lane_id => {
            return Err(SpotSemanticValueErrorV1::MixedLaneId { ordinal })
        }
        None => state.lane_id = Some(opening.lane_id.clone()),
        _ => {}
    }
    if opening.raw_pre_state_root == [0; 32] || opening.raw_post_state_root == [0; 32] {
        return Err(SpotSemanticValueErrorV1::ZeroStateRoot { ordinal });
    }
    if !opening.asset_rows.is_empty() && opening.raw_pre_state_root == opening.raw_post_state_root {
        return Err(SpotSemanticValueErrorV1::NonChangingValueState { ordinal });
    }
    if state
        .previous_post
        .is_some_and(|previous| previous != opening.raw_pre_state_root)
    {
        return Err(SpotSemanticValueErrorV1::StateDiscontinuity { ordinal });
    }
    Ok(())
}

fn validate_state_commitments(
    ordinal: usize,
    opening: &SpotValueLeafOpeningV1,
    expected_pre: CommitmentV3,
    expected_post: CommitmentV3,
) -> Result<(), SpotSemanticValueErrorV1> {
    let lane_pre = [(opening.lane_id.clone(), opening.raw_pre_state_root)];
    let actual_pre = recursive_lane_state_vector_root_v1(PRE_STATE_VECTOR_DOMAIN_V1, &lane_pre)
        .map_err(|_| SpotSemanticValueErrorV1::LegacyDerivation("pre_state_vector_root"))?;
    if expected_pre.as_bytes() != &actual_pre {
        return Err(SpotSemanticValueErrorV1::StateCommitmentMismatch {
            ordinal,
            side: "pre",
        });
    }
    let lane_post = [(opening.lane_id.clone(), opening.raw_post_state_root)];
    let actual_post = recursive_lane_state_vector_root_v1(POST_STATE_VECTOR_DOMAIN_V1, &lane_post)
        .map_err(|_| SpotSemanticValueErrorV1::LegacyDerivation("post_state_vector_root"))?;
    if expected_post.as_bytes() != &actual_post {
        return Err(SpotSemanticValueErrorV1::StateCommitmentMismatch {
            ordinal,
            side: "post",
        });
    }
    Ok(())
}

fn validate_row_bound(
    ordinal: usize,
    leaf_rows: usize,
    prior_rows: usize,
) -> Result<(), SpotSemanticValueErrorV1> {
    if leaf_rows > MAX_SPOT_ASSET_ROWS_PER_LEAF_V1 {
        return Err(SpotSemanticValueErrorV1::TooManyRows {
            ordinal,
            actual: leaf_rows,
            maximum: MAX_SPOT_ASSET_ROWS_PER_LEAF_V1,
        });
    }
    let total = prior_rows
        .checked_add(leaf_rows)
        .ok_or(SpotSemanticValueErrorV1::ArithmeticOverflow("row_count"))?;
    if total > MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2 {
        return Err(SpotSemanticValueErrorV1::TooManyRepresentedRows {
            actual: total,
            maximum: MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2,
        });
    }
    Ok(())
}

fn validate_asset_rows_root(
    ordinal: usize,
    rows: &[RecursiveAssetDeltaRowV1],
    expected: CommitmentV3,
) -> Result<(), SpotSemanticValueErrorV1> {
    let actual = recursive_asset_delta_root_v1(rows)
        .map_err(|_| SpotSemanticValueErrorV1::AssetRowsNotCanonical { ordinal })?;
    if expected.as_bytes() != &actual {
        return Err(SpotSemanticValueErrorV1::AssetRowsRootMismatch { ordinal });
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct RowValidationContextV1<'a> {
    ordinal: usize,
    row_index: usize,
    leaf: &'a ProposedSemanticLeafV1,
    policy: &'a SpotRepresentedValuePolicyV1,
}

fn accumulate_row(
    context: RowValidationContextV1<'_>,
    row: &RecursiveAssetDeltaRowV1,
    state: &mut CompositionStateV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    let asset_id = decode_canonical_asset_id(&row.asset_id).ok_or(
        SpotSemanticValueErrorV1::NonCanonicalAssetId {
            ordinal: context.ordinal,
            row: context.row_index,
        },
    )?;
    if row.debit_atoms == 0
        && row.credit_atoms == 0
        && row.authorized_mint_atoms == 0
        && row.authorized_burn_atoms == 0
    {
        return Err(SpotSemanticValueErrorV1::ZeroAssetRow {
            ordinal: context.ordinal,
            row: context.row_index,
        });
    }
    if row.authorized_mint_atoms != 0 && row.authorized_burn_atoms != 0 {
        return Err(SpotSemanticValueErrorV1::SupplyRowCombinesMintAndBurn {
            ordinal: context.ordinal,
            row: context.row_index,
        });
    }
    if row.authorized_burn_atoms != 0 {
        return Err(SpotSemanticValueErrorV1::BurnUnsupported {
            ordinal: context.ordinal,
            row: context.row_index,
        });
    }
    if row.authorized_mint_atoms == 0 {
        validate_ordinary_row(context, row)?;
    } else {
        validate_mint_row(context, asset_id, row, state)?;
    }
    accumulate_flow(asset_id, row, &mut state.flows)
}

fn validate_ordinary_row(
    context: RowValidationContextV1<'_>,
    row: &RecursiveAssetDeltaRowV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    if row.authority_root != [0; 32] {
        return Err(SpotSemanticValueErrorV1::OrdinaryRowHasAuthority {
            ordinal: context.ordinal,
            row: context.row_index,
        });
    }
    Ok(())
}

fn validate_mint_row(
    context: RowValidationContextV1<'_>,
    asset_id: [u8; 32],
    row: &RecursiveAssetDeltaRowV1,
    state: &mut CompositionStateV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    if row.debit_atoms != 0
        || row.credit_atoms != row.authorized_mint_atoms
        || row.authorized_burn_atoms != 0
    {
        return Err(SpotSemanticValueErrorV1::MintRowShapeInvalid {
            ordinal: context.ordinal,
            row: context.row_index,
        });
    }
    let grant =
        context
            .policy
            .grant(&asset_id)
            .ok_or(SpotSemanticValueErrorV1::MissingMintGrant {
                ordinal: context.ordinal,
                row: context.row_index,
            })?;
    if row.authority_root != grant.legacy_authority_root {
        return Err(SpotSemanticValueErrorV1::MintAuthorityMismatch {
            ordinal: context.ordinal,
            row: context.row_index,
        });
    }
    let used = state.grant_usage.entry(asset_id).or_insert(0);
    *used = used.checked_add(row.authorized_mint_atoms).ok_or(
        SpotSemanticValueErrorV1::ArithmeticOverflow("mint_grant_usage"),
    )?;
    if *used > grant.max_atoms_per_value_root {
        return Err(SpotSemanticValueErrorV1::MintCapExceeded {
            ordinal: context.ordinal,
            row: context.row_index,
        });
    }
    state.authority_uses.push(SpotMintAuthorityUseV1 {
        source_claim_id: *context.leaf.source_claim_id().as_bytes(),
        leaf_ordinal: context.leaf.partition().start(),
        asset_id,
        atoms: row.authorized_mint_atoms,
        legacy_authority_root: row.authority_root,
    });
    Ok(())
}

fn accumulate_flow(
    asset_id: [u8; 32],
    row: &RecursiveAssetDeltaRowV1,
    flows: &mut BTreeMap<[u8; 32], FlowAccumulatorV1>,
) -> Result<(), SpotSemanticValueErrorV1> {
    let flow = flows.entry(asset_id).or_default();
    flow.outflow_atoms = checked_add(flow.outflow_atoms, row.debit_atoms, "asset_outflow")?;
    flow.inflow_atoms = checked_add(flow.inflow_atoms, row.credit_atoms, "asset_inflow")?;
    flow.issued_atoms = checked_add(
        flow.issued_atoms,
        row.authorized_mint_atoms,
        "asset_issuance",
    )?;
    flow.destroyed_atoms = checked_add(
        flow.destroyed_atoms,
        row.authorized_burn_atoms,
        "asset_destruction",
    )?;
    Ok(())
}

pub(super) fn validate_closed_flows(
    flows: &[SpotCanonicalAssetFlowV1],
) -> Result<(), SpotSemanticValueErrorV1> {
    for flow in flows {
        let left = checked_add(flow.outflow_atoms, flow.issued_atoms, "balance_left")?;
        let right = checked_add(flow.inflow_atoms, flow.destroyed_atoms, "balance_right")?;
        if left != right {
            return Err(SpotSemanticValueErrorV1::AssetImbalance {
                asset_id: flow.asset_id,
            });
        }
    }
    Ok(())
}
