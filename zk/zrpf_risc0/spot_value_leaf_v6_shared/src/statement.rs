use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    AuthorizationGrantIdV1, AuthorizationScopeIdV1, AuthorizationSubjectIdV1, CommitmentV3,
    ExpectedV1AdapterLeafIdentityV1, NodeJournalV3, NodeKindV3, ProfileIdV3, ProgramIdV3,
    ProposedSemanticLeafV1, SemanticSubtreeV2, V1AdapterSemanticLeafOpeningV1,
    ValueAggregateOperationalCommitmentsInputV5, ValueAggregateOperationalCommitmentsV5,
};
use zenodex_zrpf_risc0_shared::{profile_id_v3, program_id_from_risc0_words_v3};

use crate::{SourceOpenedSpotValueLeafErrorV6, PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID};

pub const SOURCE_OPENED_SPOT_VALUE_LEAF_STATEMENT_VERSION_V6: u16 = 6;
pub const MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_STATEMENT_BYTES_V6: usize = 64 * 1_024;

const PROFILE_NAME_V6: &str = "zrpf_source_opened_ordinary_spot_value_leaf_v6";
const MANIFEST_CLASS_V6: &[u8] = b"source_opened_ordinary_spot_value_leaf_v6_no_self_image";
const MANIFEST_CLASS_DOMAIN_V6: &[u8] =
    b"zenodex.zrpf.source_opened_spot_value_leaf_manifest_class.v6";
const PROGRAM_MANIFEST_DOMAIN_V6: &[u8] =
    b"zenodex.zrpf.source_opened_spot_value_leaf_program_manifest.v6";
const ACTION_NULLIFIER_ROOT_DOMAIN_V6: &[u8] =
    b"zenodex.zrpf.source_opened_spot_action_nullifier_root.v6";
const NO_DA_CERTIFICATE_DOMAIN_V6: &[u8] = b"zenodex.zrpf.source_opened_spot_no_da_certificate.v6";
const EMPTY_CARRY_ROOT_DOMAIN_V6: &[u8] = b"zenodex.zrpf.source_opened_spot_empty_carry_root.v6";
const SINGLETON_SCHEDULE_DOMAIN_V6: &[u8] =
    b"zenodex.zrpf.source_opened_spot_singleton_schedule.v6";
const SEMANTIC_LEAF_HASH_DOMAIN_V6: &[u8] = b"zenodex.zrpf.source_opened_spot_semantic_leaf.v6";
const STATEMENT_HASH_DOMAIN_V6: &[u8] = b"zenodex.zrpf.source_opened_spot_value_leaf_statement.v6";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceOpenedSpotValueLeafStatementV6 {
    statement_version: u16,
    structural_adapter_journal: NodeJournalV3,
    semantic_subtree: SemanticSubtreeV2,
    source_transaction_commitment: CommitmentV3,
    canonical_tx_commitment: CommitmentV3,
    action_nullifier_root: CommitmentV3,
    source_execution_order_commitment: CommitmentV3,
    singleton_schedule_commitment: CommitmentV3,
    carry_queue_pre_root: CommitmentV3,
    carry_queue_post_root: CommitmentV3,
    data_availability_payload_commitment: CommitmentV3,
    authorization_subject_id: AuthorizationSubjectIdV1,
    authorization_scope_id: AuthorizationScopeIdV1,
    authorization_nonce: u64,
    authorization_grant_id: AuthorizationGrantIdV1,
    proof_profile_id: ProfileIdV3,
    program_manifest_class_commitment: CommitmentV3,
    statement_hash: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceOpenedSpotValueLeafStatementWireV6 {
    statement_version: u16,
    structural_adapter_journal: NodeJournalV3,
    semantic_subtree: SemanticSubtreeV2,
    source_transaction_commitment: CommitmentV3,
    canonical_tx_commitment: CommitmentV3,
    action_nullifier_root: CommitmentV3,
    source_execution_order_commitment: CommitmentV3,
    singleton_schedule_commitment: CommitmentV3,
    carry_queue_pre_root: CommitmentV3,
    carry_queue_post_root: CommitmentV3,
    data_availability_payload_commitment: CommitmentV3,
    authorization_subject_id: AuthorizationSubjectIdV1,
    authorization_scope_id: AuthorizationScopeIdV1,
    authorization_nonce: u64,
    authorization_grant_id: AuthorizationGrantIdV1,
    proof_profile_id: ProfileIdV3,
    program_manifest_class_commitment: CommitmentV3,
    statement_hash: CommitmentV3,
}

pub(crate) struct SourceOpenedSpotValueLeafStatementInputV6 {
    pub(crate) structural_adapter_journal: NodeJournalV3,
    pub(crate) semantic_subtree: SemanticSubtreeV2,
    pub(crate) source_transaction_commitment: CommitmentV3,
    pub(crate) canonical_tx_commitment: CommitmentV3,
    pub(crate) source_execution_order_commitment: CommitmentV3,
    pub(crate) singleton_schedule_commitment: CommitmentV3,
    pub(crate) data_availability_payload_commitment: CommitmentV3,
    pub(crate) authorization_subject_id: AuthorizationSubjectIdV1,
    pub(crate) authorization_scope_id: AuthorizationScopeIdV1,
    pub(crate) authorization_nonce: u64,
    pub(crate) authorization_grant_id: AuthorizationGrantIdV1,
}

impl SourceOpenedSpotValueLeafStatementV6 {
    pub(crate) fn derive(
        input: SourceOpenedSpotValueLeafStatementInputV6,
    ) -> Result<Self, SourceOpenedSpotValueLeafErrorV6> {
        let record = input.semantic_subtree.leaf_records().first().ok_or(
            SourceOpenedSpotValueLeafErrorV6::StatementShape("missing semantic leaf record"),
        )?;
        let action_nullifier_root = action_nullifier_root_v6(record.transaction_root())?;
        let empty_carry_root = canonical_empty_carry_root_v6()?;
        let proof_profile_id = source_opened_spot_value_leaf_profile_id_v6()?;
        let program_manifest_class_commitment =
            source_opened_spot_value_leaf_manifest_class_commitment_v6()?;
        let mut statement = Self {
            statement_version: SOURCE_OPENED_SPOT_VALUE_LEAF_STATEMENT_VERSION_V6,
            structural_adapter_journal: input.structural_adapter_journal,
            semantic_subtree: input.semantic_subtree,
            source_transaction_commitment: input.source_transaction_commitment,
            canonical_tx_commitment: input.canonical_tx_commitment,
            action_nullifier_root,
            source_execution_order_commitment: input.source_execution_order_commitment,
            singleton_schedule_commitment: input.singleton_schedule_commitment,
            carry_queue_pre_root: empty_carry_root,
            carry_queue_post_root: empty_carry_root,
            data_availability_payload_commitment: input.data_availability_payload_commitment,
            authorization_subject_id: input.authorization_subject_id,
            authorization_scope_id: input.authorization_scope_id,
            authorization_nonce: input.authorization_nonce,
            authorization_grant_id: input.authorization_grant_id,
            proof_profile_id,
            program_manifest_class_commitment,
            statement_hash: CommitmentV3::new([1; 32])
                .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("seed"))?,
        };
        statement.statement_hash = derive_statement_hash_v6(&statement)?;
        statement.validate()?;
        Ok(statement)
    }

    pub fn validate(&self) -> Result<(), SourceOpenedSpotValueLeafErrorV6> {
        if self.statement_version != SOURCE_OPENED_SPOT_VALUE_LEAF_STATEMENT_VERSION_V6 {
            return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
                "statement version",
            ));
        }
        self.structural_adapter_journal
            .validate()
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementShape("adapter journal"))?;
        self.semantic_subtree
            .validate()
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementShape("semantic subtree"))?;
        validate_adapter_and_subtree_v6(self)?;
        validate_flow_shape_v6(&self.semantic_subtree)?;
        validate_derived_commitments_v6(self)?;
        Ok(())
    }

    pub const fn structural_adapter_journal(&self) -> &NodeJournalV3 {
        &self.structural_adapter_journal
    }

    pub const fn semantic_subtree(&self) -> &SemanticSubtreeV2 {
        &self.semantic_subtree
    }

    pub const fn source_transaction_commitment(&self) -> CommitmentV3 {
        self.source_transaction_commitment
    }

    pub const fn canonical_tx_commitment(&self) -> CommitmentV3 {
        self.canonical_tx_commitment
    }

    pub const fn action_nullifier_root(&self) -> CommitmentV3 {
        self.action_nullifier_root
    }

    pub const fn singleton_schedule_commitment(&self) -> CommitmentV3 {
        self.singleton_schedule_commitment
    }

    pub const fn carry_queue_pre_root(&self) -> CommitmentV3 {
        self.carry_queue_pre_root
    }

    pub const fn carry_queue_post_root(&self) -> CommitmentV3 {
        self.carry_queue_post_root
    }

    pub const fn data_availability_payload_commitment(&self) -> CommitmentV3 {
        self.data_availability_payload_commitment
    }

    pub const fn authorization_subject_id(&self) -> AuthorizationSubjectIdV1 {
        self.authorization_subject_id
    }

    pub const fn authorization_scope_id(&self) -> AuthorizationScopeIdV1 {
        self.authorization_scope_id
    }

    pub const fn authorization_nonce(&self) -> u64 {
        self.authorization_nonce
    }

    pub const fn authorization_grant_id(&self) -> AuthorizationGrantIdV1 {
        self.authorization_grant_id
    }

    pub const fn proof_profile_id(&self) -> ProfileIdV3 {
        self.proof_profile_id
    }

    pub const fn program_manifest_class_commitment(&self) -> CommitmentV3 {
        self.program_manifest_class_commitment
    }

    pub const fn statement_hash(&self) -> CommitmentV3 {
        self.statement_hash
    }

    /// Derive the exact operational commitments consumed by a parent V5 tree.
    ///
    /// The no-certificate root records that this leaf supplies a DA payload
    /// commitment only. A later settlement certificate must authenticate its
    /// own full-blob DA certificate independently.
    pub fn operational_commitments_v5(
        &self,
    ) -> Result<ValueAggregateOperationalCommitmentsV5, SourceOpenedSpotValueLeafErrorV6> {
        let structural = self.structural_adapter_journal.commitments().to_input();
        ValueAggregateOperationalCommitmentsV5::new(ValueAggregateOperationalCommitmentsInputV5 {
            data_availability_root: self.data_availability_payload_commitment,
            data_availability_certificate_root: no_da_certificate_root_v6()?,
            conflict_schedule_root: self.singleton_schedule_commitment,
            cross_lane_outbox_root: structural.cross_lane_outbox_root,
            cross_lane_inbox_root: structural.cross_lane_inbox_root,
            cross_lane_message_ids_root: structural.cross_lane_message_ids_root,
            carry_queue_pre_root: self.carry_queue_pre_root,
            carry_queue_post_root: self.carry_queue_post_root,
        })
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementShape("operational commitments"))
    }
}

impl<'de> Deserialize<'de> for SourceOpenedSpotValueLeafStatementV6 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = SourceOpenedSpotValueLeafStatementWireV6::deserialize(deserializer)?;
        let statement = Self {
            statement_version: wire.statement_version,
            structural_adapter_journal: wire.structural_adapter_journal,
            semantic_subtree: wire.semantic_subtree,
            source_transaction_commitment: wire.source_transaction_commitment,
            canonical_tx_commitment: wire.canonical_tx_commitment,
            action_nullifier_root: wire.action_nullifier_root,
            source_execution_order_commitment: wire.source_execution_order_commitment,
            singleton_schedule_commitment: wire.singleton_schedule_commitment,
            carry_queue_pre_root: wire.carry_queue_pre_root,
            carry_queue_post_root: wire.carry_queue_post_root,
            data_availability_payload_commitment: wire.data_availability_payload_commitment,
            authorization_subject_id: wire.authorization_subject_id,
            authorization_scope_id: wire.authorization_scope_id,
            authorization_nonce: wire.authorization_nonce,
            authorization_grant_id: wire.authorization_grant_id,
            proof_profile_id: wire.proof_profile_id,
            program_manifest_class_commitment: wire.program_manifest_class_commitment,
            statement_hash: wire.statement_hash,
        };
        statement.validate().map_err(de::Error::custom)?;
        Ok(statement)
    }
}

pub fn encode_source_opened_spot_value_leaf_statement_v6(
    statement: &SourceOpenedSpotValueLeafStatementV6,
) -> Result<Vec<u8>, SourceOpenedSpotValueLeafErrorV6> {
    statement.validate()?;
    let bytes = postcard::to_allocvec(statement)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementEncode)?;
    require_statement_size(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_source_opened_spot_value_leaf_statement_v6(
    bytes: &[u8],
) -> Result<SourceOpenedSpotValueLeafStatementV6, SourceOpenedSpotValueLeafErrorV6> {
    require_statement_size(bytes.len())?;
    let (statement, remainder) =
        postcard::take_from_bytes::<SourceOpenedSpotValueLeafStatementV6>(bytes)
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDecode)?;
    if !remainder.is_empty() {
        return Err(SourceOpenedSpotValueLeafErrorV6::NonCanonicalStatement);
    }
    if encode_source_opened_spot_value_leaf_statement_v6(&statement)?.as_slice() != bytes {
        return Err(SourceOpenedSpotValueLeafErrorV6::NonCanonicalStatement);
    }
    Ok(statement)
}

pub fn source_opened_spot_value_leaf_profile_id_v6(
) -> Result<ProfileIdV3, SourceOpenedSpotValueLeafErrorV6> {
    profile_id_v3(PROFILE_NAME_V6)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("profile"))
}

pub fn source_opened_spot_value_leaf_manifest_class_commitment_v6(
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    let adapter_program = program_id_from_risc0_words_v3(PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("adapter program"))?;
    let profile = source_opened_spot_value_leaf_profile_id_v6()?;
    hash_framed(
        MANIFEST_CLASS_DOMAIN_V6,
        &[
            profile.as_bytes(),
            adapter_program.as_bytes(),
            MANIFEST_CLASS_V6,
        ],
    )
}

/// Bind the parent-authenticated V6 runtime identity to the proof-neutral
/// statement profile, manifest class, and exact adapter-successor program.
///
/// The V6 guest cannot derive its own runtime identity. A receipt-verifying
/// parent or sealed host supplies `v6_program_id` only after authenticating the
/// V6 receipt under the corresponding image ID.
pub fn source_opened_spot_value_leaf_program_manifest_root_v6(
    v6_program_id: ProgramIdV3,
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    let adapter_program_id =
        program_id_from_risc0_words_v3(PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID).map_err(|_| {
            SourceOpenedSpotValueLeafErrorV6::StatementDerivation("adapter program")
        })?;
    let profile = source_opened_spot_value_leaf_profile_id_v6()?;
    let class = source_opened_spot_value_leaf_manifest_class_commitment_v6()?;
    hash_framed(
        PROGRAM_MANIFEST_DOMAIN_V6,
        &[
            v6_program_id.as_bytes(),
            adapter_program_id.as_bytes(),
            profile.as_bytes(),
            class.as_bytes(),
        ],
    )
}

pub(crate) fn action_nullifier_root_v6(
    action_nullifier: CommitmentV3,
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    hash_framed(
        ACTION_NULLIFIER_ROOT_DOMAIN_V6,
        &[&1_u16.to_be_bytes(), action_nullifier.as_bytes()],
    )
}

pub(crate) fn canonical_empty_carry_root_v6(
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    hash_framed(EMPTY_CARRY_ROOT_DOMAIN_V6, &[&0_u16.to_be_bytes()])
}

fn no_da_certificate_root_v6() -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    hash_framed(NO_DA_CERTIFICATE_DOMAIN_V6, &[&0_u16.to_be_bytes()])
}

pub(crate) fn singleton_schedule_commitment_v6(
    source_execution_order_commitment: CommitmentV3,
    canonical_tx_commitment: CommitmentV3,
    action_nullifier: CommitmentV3,
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    hash_framed(
        SINGLETON_SCHEDULE_DOMAIN_V6,
        &[
            &1_u16.to_be_bytes(),
            &0_u32.to_be_bytes(),
            source_execution_order_commitment.as_bytes(),
            canonical_tx_commitment.as_bytes(),
            action_nullifier.as_bytes(),
        ],
    )
}

pub(crate) fn semantic_leaf_hash_v6(
    adapter_journal_hash: CommitmentV3,
    source_transaction_commitment: CommitmentV3,
    canonical_tx_commitment: CommitmentV3,
    action_nullifier: CommitmentV3,
    asset_delta_root: CommitmentV3,
    singleton_schedule_commitment: CommitmentV3,
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    hash_framed(
        SEMANTIC_LEAF_HASH_DOMAIN_V6,
        &[
            adapter_journal_hash.as_bytes(),
            source_transaction_commitment.as_bytes(),
            canonical_tx_commitment.as_bytes(),
            action_nullifier.as_bytes(),
            asset_delta_root.as_bytes(),
            singleton_schedule_commitment.as_bytes(),
        ],
    )
}

fn validate_adapter_and_subtree_v6(
    statement: &SourceOpenedSpotValueLeafStatementV6,
) -> Result<(), SourceOpenedSpotValueLeafErrorV6> {
    let adapter = &statement.structural_adapter_journal;
    let subtree = &statement.semantic_subtree;
    if adapter.node_kind() != NodeKindV3::Leaf
        || adapter.leaf_count() != 1
        || adapter.operation_count() != 1
        || subtree.leaf_count() != 1
        || subtree.leaf_records().len() != 1
        || adapter.partition() != subtree.partition()
        || adapter
            .scope()
            .canonical_hash()
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementShape("adapter scope hash"))?
            != subtree.scope_hash()
    {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
            "adapter/subtree relation",
        ));
    }
    let expected_adapter = program_id_from_risc0_words_v3(PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementShape("adapter identity"))?;
    if adapter.actual_program_id() != expected_adapter {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
            "adapter program",
        ));
    }
    let record = &subtree.leaf_records()[0];
    let expected_identity = ExpectedV1AdapterLeafIdentityV1::new(expected_adapter)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementShape("adapter identity"))?;
    let semantic_leaf = ProposedSemanticLeafV1::bind_v1_adapter_journal(
        adapter,
        V1AdapterSemanticLeafOpeningV1::new(record.semantic_source_id()),
        &expected_identity,
    )
    .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementShape("semantic source opening"))?;
    let commitments = adapter.commitments().to_input();
    if record.partition() != adapter.partition()
        || record.task_id() != adapter.task_id()
        || record.source_claim_id() != semantic_leaf.source_claim_id().into_commitment()
        || record.semantic_source_id() != semantic_leaf.semantic_source_id().into_commitment()
        || record.pre_state_vector_root() != commitments.pre_state_vector_root
        || record.post_state_vector_root() != commitments.post_state_vector_root
        || statement.source_transaction_commitment != commitments.transaction_root
        || record.effect_root() != commitments.effect_root
    {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
            "semantic record/adapter relation",
        ));
    }
    let expected_leaf_hash = semantic_leaf_hash_v6(
        adapter.canonical_hash().map_err(|_| {
            SourceOpenedSpotValueLeafErrorV6::StatementShape("adapter journal hash")
        })?,
        statement.source_transaction_commitment,
        statement.canonical_tx_commitment,
        record.transaction_root(),
        record.asset_delta_root(),
        statement.singleton_schedule_commitment,
    )?;
    if record.semantic_leaf_hash() != expected_leaf_hash {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
            "semantic leaf hash",
        ));
    }
    Ok(())
}

fn validate_flow_shape_v6(
    subtree: &SemanticSubtreeV2,
) -> Result<(), SourceOpenedSpotValueLeafErrorV6> {
    if subtree.represented_row_count() != 2
        || subtree.asset_flows().len() != 2
        || !subtree.authority_uses().is_empty()
    {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
            "ordinary flow cardinality",
        ));
    }
    for flow in subtree.asset_flows() {
        if flow.outflow_atoms() == 0
            || flow.outflow_atoms() != flow.inflow_atoms()
            || flow.issued_atoms() != 0
            || flow.destroyed_atoms() != 0
        {
            return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
                "balanced ordinary flow",
            ));
        }
    }
    Ok(())
}

fn validate_derived_commitments_v6(
    statement: &SourceOpenedSpotValueLeafStatementV6,
) -> Result<(), SourceOpenedSpotValueLeafErrorV6> {
    let record = &statement.semantic_subtree.leaf_records()[0];
    if statement.action_nullifier_root != action_nullifier_root_v6(record.transaction_root())? {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
            "action nullifier root",
        ));
    }
    if statement.singleton_schedule_commitment
        != singleton_schedule_commitment_v6(
            statement.source_execution_order_commitment,
            statement.canonical_tx_commitment,
            record.transaction_root(),
        )?
    {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
            "singleton schedule",
        ));
    }
    let empty_carry = canonical_empty_carry_root_v6()?;
    if statement.carry_queue_pre_root != empty_carry
        || statement.carry_queue_post_root != empty_carry
    {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
            "canonical empty carry",
        ));
    }
    if statement.proof_profile_id != source_opened_spot_value_leaf_profile_id_v6()?
        || statement.program_manifest_class_commitment
            != source_opened_spot_value_leaf_manifest_class_commitment_v6()?
    {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
            "proof-neutral profile/manifest class",
        ));
    }
    if statement.statement_hash != derive_statement_hash_v6(statement)? {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementShape(
            "statement hash",
        ));
    }
    statement.operational_commitments_v5()?;
    Ok(())
}

fn derive_statement_hash_v6(
    statement: &SourceOpenedSpotValueLeafStatementV6,
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    let adapter_hash = statement
        .structural_adapter_journal
        .canonical_hash()
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("adapter hash"))?;
    let subtree_hash = statement
        .semantic_subtree
        .canonical_hash()
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("subtree hash"))?;
    hash_framed(
        STATEMENT_HASH_DOMAIN_V6,
        &[
            &statement.statement_version.to_be_bytes(),
            adapter_hash.as_bytes(),
            subtree_hash.as_bytes(),
            statement.source_transaction_commitment.as_bytes(),
            statement.canonical_tx_commitment.as_bytes(),
            statement.action_nullifier_root.as_bytes(),
            statement.source_execution_order_commitment.as_bytes(),
            statement.singleton_schedule_commitment.as_bytes(),
            statement.carry_queue_pre_root.as_bytes(),
            statement.carry_queue_post_root.as_bytes(),
            statement.data_availability_payload_commitment.as_bytes(),
            statement.authorization_subject_id.as_bytes(),
            statement.authorization_scope_id.as_bytes(),
            &statement.authorization_nonce.to_be_bytes(),
            statement.authorization_grant_id.as_bytes(),
            statement.proof_profile_id.as_bytes(),
            statement.program_manifest_class_commitment.as_bytes(),
        ],
    )
}

pub(crate) fn hash_framed(
    domain: &[u8],
    fields: &[&[u8]],
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    let mut hasher = Sha256::new();
    let domain_length = u16::try_from(domain.len())
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("domain length"))?;
    hasher.update(domain_length.to_be_bytes());
    hasher.update(domain);
    for field in fields {
        let length = u32::try_from(field.len())
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("field length"))?;
        hasher.update(length.to_be_bytes());
        hasher.update(field);
    }
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("commitment"))
}

fn require_statement_size(size: usize) -> Result<(), SourceOpenedSpotValueLeafErrorV6> {
    if size == 0 {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementDecode);
    }
    if size > MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_STATEMENT_BYTES_V6 {
        return Err(SourceOpenedSpotValueLeafErrorV6::StatementTooLarge {
            actual: size,
            maximum: MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_STATEMENT_BYTES_V6,
        });
    }
    Ok(())
}
