use sha2::Digest;
use zenodex_zrpf_protocol_v3::{CommitmentV3, NodeScopeV3};

use super::hash::{
    commitment, domain_hasher, spot_accounting_domain_id_v1, spot_atoms_unit_id_v1,
    spot_represented_value_profile_id_v1, spot_state_root_scheme_id_v1, write_bytes32, write_u64,
};
use super::{
    ExpectedSpotSemanticValueFieldV1, SpotSemanticValueErrorV1, SpotSemanticValueProjectionV1,
    MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2, MAX_SPOT_VALUE_LEAVES_V1,
};

const EXPECTED_SPOT_SEMANTIC_VALUE_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.spot_expected_semantic_value.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
/// Untrusted fields proposed as the complete expected Spot value statement.
pub struct ExpectedSpotSemanticValueInputV1 {
    pub scope: NodeScopeV3,
    pub lane_id_hash: CommitmentV3,
    pub value_profile_id: CommitmentV3,
    pub accounting_domain_id: CommitmentV3,
    pub atoms_unit_id: CommitmentV3,
    pub state_root_scheme_id: CommitmentV3,
    pub ordered_transaction_roots_root: CommitmentV3,
    pub state_chain_root: CommitmentV3,
    pub raw_pre_state_root: [u8; 32],
    pub raw_post_state_root: [u8; 32],
    pub leaf_count: u64,
    pub represented_row_count: u64,
    pub authority_grants_root: CommitmentV3,
    pub base_semantic_epoch_root: CommitmentV3,
    pub semantic_value_root: CommitmentV3,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Shape-checked expected statement; construction does not authenticate its provenance.
pub struct ExpectedSpotSemanticValueV1 {
    scope: NodeScopeV3,
    scope_hash: CommitmentV3,
    lane_id_hash: CommitmentV3,
    value_profile_id: CommitmentV3,
    accounting_domain_id: CommitmentV3,
    atoms_unit_id: CommitmentV3,
    state_root_scheme_id: CommitmentV3,
    ordered_transaction_roots_root: CommitmentV3,
    state_chain_root: CommitmentV3,
    raw_pre_state_root: [u8; 32],
    raw_post_state_root: [u8; 32],
    leaf_count: u64,
    represented_row_count: u64,
    authority_grants_root: CommitmentV3,
    base_semantic_epoch_root: CommitmentV3,
    semantic_value_root: CommitmentV3,
    statement_hash: CommitmentV3,
}

impl ExpectedSpotSemanticValueV1 {
    pub fn new(input: ExpectedSpotSemanticValueInputV1) -> Result<Self, SpotSemanticValueErrorV1> {
        validate_expected_input(&input)?;
        let scope_hash = input
            .scope
            .canonical_hash()
            .map_err(SpotSemanticValueErrorV1::Structural)?;
        let statement_hash = expected_statement_hash(&input, scope_hash)?;
        Ok(Self {
            scope: input.scope,
            scope_hash,
            lane_id_hash: input.lane_id_hash,
            value_profile_id: input.value_profile_id,
            accounting_domain_id: input.accounting_domain_id,
            atoms_unit_id: input.atoms_unit_id,
            state_root_scheme_id: input.state_root_scheme_id,
            ordered_transaction_roots_root: input.ordered_transaction_roots_root,
            state_chain_root: input.state_chain_root,
            raw_pre_state_root: input.raw_pre_state_root,
            raw_post_state_root: input.raw_post_state_root,
            leaf_count: input.leaf_count,
            represented_row_count: input.represented_row_count,
            authority_grants_root: input.authority_grants_root,
            base_semantic_epoch_root: input.base_semantic_epoch_root,
            semantic_value_root: input.semantic_value_root,
            statement_hash,
        })
    }

    pub const fn scope(&self) -> &NodeScopeV3 {
        &self.scope
    }

    pub const fn statement_hash(&self) -> CommitmentV3 {
        self.statement_hash
    }

    pub const fn semantic_value_root(&self) -> CommitmentV3 {
        self.semantic_value_root
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Exact projection/expectation match with no receipt, governance, or ledger authority.
///
/// Future receipt or ledger admission must not accept this pure match type
/// directly. It requires a separate post-receipt, authenticated-expectation
/// boundary.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_semantic_shared::{
///     ExpectedSpotSemanticValueMatchV1, SpotSemanticValueProjectionV1,
/// };
/// fn bypass(value: SpotSemanticValueProjectionV1) -> ExpectedSpotSemanticValueMatchV1 {
///     value.into()
/// }
/// ```
pub struct ExpectedSpotSemanticValueMatchV1 {
    projection: SpotSemanticValueProjectionV1,
    expected_statement_hash: CommitmentV3,
}

impl ExpectedSpotSemanticValueMatchV1 {
    pub const fn projection(&self) -> &SpotSemanticValueProjectionV1 {
        &self.projection
    }

    pub const fn expected_statement_hash(&self) -> CommitmentV3 {
        self.expected_statement_hash
    }
}

/// Consume a pure projection only after every shape-checked expected field
/// matches exactly.
pub fn match_expected_spot_semantic_value_v1(
    projection: SpotSemanticValueProjectionV1,
    expected: &ExpectedSpotSemanticValueV1,
) -> Result<ExpectedSpotSemanticValueMatchV1, SpotSemanticValueErrorV1> {
    match_scope_and_lane(&projection, expected)?;
    match_profile_commitments(&projection, expected)?;
    match_execution_commitments(&projection, expected)?;
    match_terminal_commitments(&projection, expected)?;
    Ok(ExpectedSpotSemanticValueMatchV1 {
        projection,
        expected_statement_hash: expected.statement_hash,
    })
}

fn match_scope_and_lane(
    projection: &SpotSemanticValueProjectionV1,
    expected: &ExpectedSpotSemanticValueV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    require_match(
        projection.scope_hash,
        expected.scope_hash,
        ExpectedSpotSemanticValueFieldV1::ScopeHash,
    )?;
    require_match(
        projection.lane_id_hash,
        expected.lane_id_hash,
        ExpectedSpotSemanticValueFieldV1::LaneIdHash,
    )
}

fn match_profile_commitments(
    projection: &SpotSemanticValueProjectionV1,
    expected: &ExpectedSpotSemanticValueV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    let commitments = &projection.commitments;
    require_match(
        commitments.value_profile_id,
        expected.value_profile_id,
        ExpectedSpotSemanticValueFieldV1::ValueProfileId,
    )?;
    require_match(
        commitments.accounting_domain_id,
        expected.accounting_domain_id,
        ExpectedSpotSemanticValueFieldV1::AccountingDomainId,
    )?;
    require_match(
        commitments.atoms_unit_id,
        expected.atoms_unit_id,
        ExpectedSpotSemanticValueFieldV1::AtomsUnitId,
    )?;
    require_match(
        commitments.state_root_scheme_id,
        expected.state_root_scheme_id,
        ExpectedSpotSemanticValueFieldV1::StateRootSchemeId,
    )
}

fn match_execution_commitments(
    projection: &SpotSemanticValueProjectionV1,
    expected: &ExpectedSpotSemanticValueV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    let commitments = &projection.commitments;
    require_match(
        commitments.ordered_transaction_roots_root,
        expected.ordered_transaction_roots_root,
        ExpectedSpotSemanticValueFieldV1::OrderedTransactionRootsRoot,
    )?;
    require_match(
        commitments.state_chain_root,
        expected.state_chain_root,
        ExpectedSpotSemanticValueFieldV1::StateChainRoot,
    )?;
    require_match(
        projection.raw_epoch_pre_state_root,
        expected.raw_pre_state_root,
        ExpectedSpotSemanticValueFieldV1::RawPreStateRoot,
    )?;
    require_match(
        projection.raw_epoch_post_state_root,
        expected.raw_post_state_root,
        ExpectedSpotSemanticValueFieldV1::RawPostStateRoot,
    )?;
    require_match(
        projection.leaf_count,
        expected.leaf_count,
        ExpectedSpotSemanticValueFieldV1::LeafCount,
    )?;
    require_match(
        projection.represented_row_count,
        expected.represented_row_count,
        ExpectedSpotSemanticValueFieldV1::RepresentedRowCount,
    )
}

fn match_terminal_commitments(
    projection: &SpotSemanticValueProjectionV1,
    expected: &ExpectedSpotSemanticValueV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    let commitments = &projection.commitments;
    require_match(
        commitments.authority_grants_root,
        expected.authority_grants_root,
        ExpectedSpotSemanticValueFieldV1::AuthorityGrantsRoot,
    )?;
    require_match(
        commitments.base_semantic_epoch_root,
        expected.base_semantic_epoch_root,
        ExpectedSpotSemanticValueFieldV1::BaseSemanticEpochRoot,
    )?;
    require_match(
        projection.semantic_value_root,
        expected.semantic_value_root,
        ExpectedSpotSemanticValueFieldV1::SemanticValueRoot,
    )
}

fn validate_expected_input(
    input: &ExpectedSpotSemanticValueInputV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    input
        .scope
        .validate()
        .map_err(SpotSemanticValueErrorV1::Structural)?;
    if input.scope.epoch_start() != input.scope.epoch_end() {
        return Err(SpotSemanticValueErrorV1::EpochRangeUnsupported);
    }
    validate_profile_id(
        input.value_profile_id,
        spot_represented_value_profile_id_v1()?,
        ExpectedSpotSemanticValueFieldV1::ValueProfileId,
    )?;
    validate_profile_id(
        input.accounting_domain_id,
        spot_accounting_domain_id_v1()?,
        ExpectedSpotSemanticValueFieldV1::AccountingDomainId,
    )?;
    validate_profile_id(
        input.atoms_unit_id,
        spot_atoms_unit_id_v1()?,
        ExpectedSpotSemanticValueFieldV1::AtomsUnitId,
    )?;
    validate_profile_id(
        input.state_root_scheme_id,
        spot_state_root_scheme_id_v1()?,
        ExpectedSpotSemanticValueFieldV1::StateRootSchemeId,
    )?;
    if input.raw_pre_state_root == [0; 32] {
        return Err(SpotSemanticValueErrorV1::ExpectedStatementShape(
            ExpectedSpotSemanticValueFieldV1::RawPreStateRoot,
        ));
    }
    if input.raw_post_state_root == [0; 32] {
        return Err(SpotSemanticValueErrorV1::ExpectedStatementShape(
            ExpectedSpotSemanticValueFieldV1::RawPostStateRoot,
        ));
    }
    let maximum_leaf_count = u64::try_from(MAX_SPOT_VALUE_LEAVES_V1)
        .map_err(|_| SpotSemanticValueErrorV1::ArithmeticOverflow("maximum_leaf_count"))?;
    if input.leaf_count == 0 || input.leaf_count > maximum_leaf_count {
        return Err(SpotSemanticValueErrorV1::ExpectedStatementShape(
            ExpectedSpotSemanticValueFieldV1::LeafCount,
        ));
    }
    let maximum_row_count = u64::try_from(MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2)
        .map_err(|_| SpotSemanticValueErrorV1::ArithmeticOverflow("maximum_row_count"))?;
    if input.represented_row_count == 0 || input.represented_row_count > maximum_row_count {
        return Err(SpotSemanticValueErrorV1::ExpectedStatementShape(
            ExpectedSpotSemanticValueFieldV1::RepresentedRowCount,
        ));
    }
    Ok(())
}

fn validate_profile_id(
    actual: CommitmentV3,
    expected: CommitmentV3,
    field: ExpectedSpotSemanticValueFieldV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    if actual != expected {
        return Err(SpotSemanticValueErrorV1::ExpectedProfileMismatch(field));
    }
    Ok(())
}

fn require_match<T: PartialEq>(
    actual: T,
    expected: T,
    field: ExpectedSpotSemanticValueFieldV1,
) -> Result<(), SpotSemanticValueErrorV1> {
    if actual != expected {
        return Err(SpotSemanticValueErrorV1::ExpectedProjectionMismatch(field));
    }
    Ok(())
}

fn expected_statement_hash(
    input: &ExpectedSpotSemanticValueInputV1,
    scope_hash: CommitmentV3,
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(EXPECTED_SPOT_SEMANTIC_VALUE_DOMAIN_V1)?;
    for value in [
        scope_hash,
        input.lane_id_hash,
        input.value_profile_id,
        input.accounting_domain_id,
        input.atoms_unit_id,
        input.state_root_scheme_id,
        input.ordered_transaction_roots_root,
        input.state_chain_root,
    ] {
        write_bytes32(&mut hasher, value.as_bytes());
    }
    write_bytes32(&mut hasher, &input.raw_pre_state_root);
    write_bytes32(&mut hasher, &input.raw_post_state_root);
    write_u64(&mut hasher, input.leaf_count);
    write_u64(&mut hasher, input.represented_row_count);
    for value in [
        input.authority_grants_root,
        input.base_semantic_epoch_root,
        input.semantic_value_root,
    ] {
        write_bytes32(&mut hasher, value.as_bytes());
    }
    commitment(hasher.finalize().into())
}
