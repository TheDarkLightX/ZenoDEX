extern crate alloc;

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    execute_perps_np_transition_v1, execute_state_proof_input_v1, execute_zusd_transition_v1,
    PerpsNpActionV1, PerpsNpTransitionInputV1, PerpsNpTransitionJournalV1, StateProofInputV1,
    StateProofJournalV1, TransitionError, ZusdTransitionInputV1, ZusdTransitionJournalV1,
    NATIVE_ASSET,
};

pub const PROOF_TYPE_RECURSIVE: &str = "risc0.zenodex_recursive_epoch.v1";
pub const PROOF_TYPE_RECURSIVE_SUMMARY_LEAF: &str = "risc0.zenodex_recursive_summary_leaf.v1";
pub const PROOF_TYPE_RECURSIVE_SPOT_LEAF: &str = "risc0.zenodex_recursive_spot_leaf.v1";
pub const PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF: &str = "risc0.zenodex_recursive_perps_np_leaf.v1";
pub const PROOF_TYPE_RECURSIVE_ZUSD_LEAF: &str = "risc0.zenodex_recursive_zusd_leaf.v1";
pub const RECURSIVE_EFFECT_SUMMARY_VERSION_V1: u32 = 1;
pub const RECURSIVE_STATEMENT_VERSION_V1: u32 = 1;
pub const RECURSIVE_JOURNAL_VERSION_V1: u32 = 1;
pub const RECURSIVE_STRICT_CROSS_SHARD_MODE_V1: &str = "strict";
pub const RECURSIVE_DOMAIN_SEPARATOR_V1: &str = "zenodex.risc0.recursive_epoch.v1";
pub const RECURSIVE_AUTHORITY_EFFECT_MINT_V1: &str = "mint";
pub const RECURSIVE_AUTHORITY_EFFECT_BURN_V1: &str = "burn";
pub const RECURSIVE_EPOCH_PROFILE_V1: &str = "recursive_epoch_v1";
pub const RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1: &str = "recursive_summary_leaf_test_v1";
pub const RECURSIVE_SPOT_LEAF_PROFILE_V1: &str = "recursive_spot_leaf_v1";
pub const RECURSIVE_PERPS_NP_LEAF_PROFILE_V1: &str = "recursive_perps_np_leaf_v1";
pub const RECURSIVE_ZUSD_LEAF_PROFILE_V1: &str = "recursive_zusd_leaf_v1";
pub const RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES: u32 = 4096;
pub const RECURSIVE_SUMMARY_TEXT_MAX_BYTES: usize = 128;
pub const RECURSIVE_AGGREGATE_MAX_INPUT_BYTES: u32 = 4 * 1_048_576;
pub const RECURSIVE_SPOT_LEAF_MAX_INPUT_BYTES: u32 = 1_048_576;
pub const RECURSIVE_PERPS_NP_LEAF_MAX_INPUT_BYTES: u32 = 1_048_576;
pub const RECURSIVE_ZUSD_LEAF_MAX_INPUT_BYTES: u32 = 1_048_576;
pub const RECURSIVE_PERPS_NP_MIN_PARTICIPANTS: u32 = 4;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecursiveCompositionStatementV1 {
    pub domain_separator: String,
    pub schema_version: u32,
    pub chain_id: String,
    pub epoch_id: u64,
    pub proof_profile: String,
    pub verifier_set_root: [u8; 32],
    pub allowed_authority_roots_root: [u8; 32],
    pub public_policy_hash: [u8; 32],
    pub feature_suite_hash: [u8; 32],
    pub dependency_lock_hash: [u8; 32],
    pub toolchain_lock_hash: [u8; 32],
    pub expected_pre_state_root: [u8; 32],
    pub expected_post_state_root: [u8; 32],
    pub conflict_schedule_hash: [u8; 32],
    pub carry_queue_pre_root: [u8; 32],
    pub carry_queue_post_root: [u8; 32],
    pub data_availability_root: [u8; 32],
    pub expected_child_count: u32,
    pub max_children: u32,
    pub max_child_journal_bytes: u32,
    pub max_total_child_journal_bytes: u32,
    pub max_asset_delta_rows: u32,
    /// Maximum count in each outbox and inbox message partition.
    pub max_cross_shard_messages: u32,
    /// Maximum count in each accepted and rejected receipt-ID partition.
    pub max_receipt_ids: u32,
    pub cross_shard_mode: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecursiveChildDescriptorV1 {
    pub child_verification_claim_hash: [u8; 32],
    pub child_journal_hash: [u8; 32],
    pub child_effect_summary_hash: [u8; 32],
    pub child_statement_hash: [u8; 32],
    pub child_image_id: [u32; 8],
    pub child_verifier_id: [u8; 32],
    pub child_profile: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecursiveEffectSummaryV1 {
    pub summary_version: u32,
    pub lane_id: String,
    pub lane_kind: String,
    pub chain_id: String,
    pub epoch_id: u64,
    pub proof_profile: String,
    pub risc0_image_id: [u32; 8],
    pub statement_hash: [u8; 32],
    pub pre_state_root: [u8; 32],
    pub post_state_root: [u8; 32],
    pub tx_root: [u8; 32],
    pub evidence_root: [u8; 32],
    pub receipt_root: [u8; 32],
    pub accepted_receipts_root: [u8; 32],
    pub rejected_receipts_root: [u8; 32],
    pub asset_delta_root: [u8; 32],
    pub cross_shard_outbox_root: [u8; 32],
    pub cross_shard_inbox_root: [u8; 32],
    pub write_set_root: [u8; 32],
    pub public_policy_hash: [u8; 32],
    pub feature_suite_hash: [u8; 32],
    pub dependency_lock_hash: [u8; 32],
    pub toolchain_lock_hash: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct RecursiveAssetDeltaRowV1 {
    pub asset_id: String,
    pub debit_atoms: u128,
    pub credit_atoms: u128,
    pub authorized_mint_atoms: u128,
    pub authorized_burn_atoms: u128,
    pub authority_root: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct RecursiveCrossShardMessageV1 {
    pub message_id: [u8; 32],
    pub epoch_id: u64,
    pub source_shard_id: String,
    pub destination_shard_id: String,
    pub asset_id: String,
    pub amount_atoms: u128,
    pub sender_scope_hash: [u8; 32],
    pub recipient_scope_hash: [u8; 32],
    pub source_receipt_hash: [u8; 32],
    pub deadline_epoch: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecursiveChildEffectV1 {
    pub descriptor: RecursiveChildDescriptorV1,
    pub child_journal_bytes: Vec<u8>,
    pub summary: RecursiveEffectSummaryV1,
    pub asset_delta_rows: Vec<RecursiveAssetDeltaRowV1>,
    pub outbox_messages: Vec<RecursiveCrossShardMessageV1>,
    pub inbox_messages: Vec<RecursiveCrossShardMessageV1>,
    pub accepted_receipt_ids: Vec<[u8; 32]>,
    pub rejected_receipt_ids: Vec<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecursiveCompositionInputV1 {
    pub statement: RecursiveCompositionStatementV1,
    pub allowed_verifier_ids: Vec<[u8; 32]>,
    pub allowed_authority_roots: Vec<[u8; 32]>,
    pub children: Vec<RecursiveChildEffectV1>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SpotRecursiveLeafInputV1 {
    pub chain_id: String,
    pub epoch_id: u64,
    pub lane_id: String,
    pub risc0_image_id: [u32; 8],
    pub public_policy_hash: [u8; 32],
    pub feature_suite_hash: [u8; 32],
    pub dependency_lock_hash: [u8; 32],
    pub toolchain_lock_hash: [u8; 32],
    pub spot_input: StateProofInputV1,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ZusdRecursiveLeafInputV1 {
    pub chain_id: String,
    pub epoch_id: u64,
    pub lane_id: String,
    pub risc0_image_id: [u32; 8],
    pub public_policy_hash: [u8; 32],
    pub feature_suite_hash: [u8; 32],
    pub dependency_lock_hash: [u8; 32],
    pub toolchain_lock_hash: [u8; 32],
    pub zusd_input: ZusdTransitionInputV1,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PerpsNpRecursiveLeafInputV1 {
    pub chain_id: String,
    pub epoch_id: u64,
    pub lane_id: String,
    pub risc0_image_id: [u32; 8],
    pub public_policy_hash: [u8; 32],
    pub feature_suite_hash: [u8; 32],
    pub dependency_lock_hash: [u8; 32],
    pub toolchain_lock_hash: [u8; 32],
    pub perps_input: PerpsNpTransitionInputV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecursiveEpochJournalV1 {
    pub journal_version: u32,
    pub proof_type: String,
    pub domain_separator: String,
    pub chain_id: String,
    pub epoch_id: u64,
    pub proof_profile: String,
    pub statement_hash: [u8; 32],
    pub verifier_set_root: [u8; 32],
    pub allowed_authority_roots_root: [u8; 32],
    pub child_verification_claims_root: [u8; 32],
    pub child_journals_root: [u8; 32],
    pub child_effect_summaries_root: [u8; 32],
    pub child_count: u32,
    pub pre_state_root: [u8; 32],
    pub post_state_root: [u8; 32],
    pub tx_root: [u8; 32],
    pub evidence_root: [u8; 32],
    pub receipt_root: [u8; 32],
    pub accepted_receipts_root: [u8; 32],
    pub rejected_receipts_root: [u8; 32],
    pub aggregate_asset_delta_root: [u8; 32],
    pub cross_shard_outbox_root: [u8; 32],
    pub cross_shard_inbox_root: [u8; 32],
    pub cross_shard_message_ids_root: [u8; 32],
    pub carry_queue_pre_root: [u8; 32],
    pub carry_queue_post_root: [u8; 32],
    pub conflict_schedule_hash: [u8; 32],
    pub data_availability_root: [u8; 32],
    pub public_policy_hash: [u8; 32],
    pub feature_suite_hash: [u8; 32],
    pub dependency_lock_hash: [u8; 32],
    pub toolchain_lock_hash: [u8; 32],
}

pub fn compose_recursive_epoch_journal_v1(
    input: &RecursiveCompositionInputV1,
) -> Result<RecursiveEpochJournalV1, TransitionError> {
    validate_recursive_statement_v1(&input.statement)?;
    validate_sorted_unique_roots_v1(&input.allowed_verifier_ids, "verifier id")?;
    validate_sorted_unique_roots_v1(&input.allowed_authority_roots, "authority root")?;
    if recursive_root_list_root_v1(
        b"zenodex.risc0.recursive.verifier_set_root.v1",
        &input.allowed_verifier_ids,
    )? != input.statement.verifier_set_root
    {
        return Err(TransitionError::InvalidInput("verifier_set_root mismatch"));
    }
    if recursive_root_list_root_v1(
        b"zenodex.risc0.recursive.authority_set_root.v1",
        &input.allowed_authority_roots,
    )? != input.statement.allowed_authority_roots_root
    {
        return Err(TransitionError::InvalidInput(
            "allowed_authority_roots_root mismatch",
        ));
    }
    if input.children.is_empty() {
        return Err(TransitionError::InvalidInput("recursive child set empty"));
    }
    let child_count = checked_len_u32(input.children.len(), "child count too large")?;
    if child_count != input.statement.expected_child_count {
        return Err(TransitionError::InvalidInput(
            "recursive child count mismatch",
        ));
    }
    if child_count > input.statement.max_children {
        return Err(TransitionError::InvalidInput(
            "recursive child count exceeds max",
        ));
    }

    let statement_hash = recursive_statement_hash_v1(&input.statement);
    let allowed_verifiers: BTreeSet<[u8; 32]> =
        input.allowed_verifier_ids.iter().copied().collect();
    let allowed_authorities: BTreeSet<[u8; 32]> =
        input.allowed_authority_roots.iter().copied().collect();

    let mut previous_lane: Option<&str> = None;
    let mut child_verification_claim_hashes = Vec::new();
    let mut child_journal_hashes = Vec::new();
    let mut child_summary_hashes = Vec::new();
    let mut pre_lane_roots = Vec::new();
    let mut post_lane_roots = Vec::new();
    let mut tx_roots = Vec::new();
    let mut evidence_roots = Vec::new();
    let mut receipt_roots = Vec::new();
    let mut accepted_roots = Vec::new();
    let mut rejected_roots = Vec::new();
    let mut outbox_roots = Vec::new();
    let mut inbox_roots = Vec::new();
    let mut aggregate_delta_rows = Vec::new();
    let mut all_outbox = Vec::new();
    let mut all_inbox = Vec::new();
    let mut all_accepted_receipts = Vec::new();
    let mut all_rejected_receipts = Vec::new();
    let mut total_child_journal_bytes = 0usize;

    for child in &input.children {
        validate_child_effect_v1(child, &input.statement, &allowed_verifiers)?;
        validate_child_asset_authority_scopes_v1(child, &input.statement)?;
        total_child_journal_bytes = total_child_journal_bytes
            .checked_add(child.child_journal_bytes.len())
            .ok_or(TransitionError::Arithmetic(
                "recursive child journal byte count overflow",
            ))?;
        let max_total_child_journal_bytes =
            usize::try_from(input.statement.max_total_child_journal_bytes).map_err(|_| {
                TransitionError::Arithmetic("recursive max_total_child_journal_bytes overflow")
            })?;
        if total_child_journal_bytes > max_total_child_journal_bytes {
            return Err(TransitionError::InvalidInput(
                "recursive total child journal bytes exceeds max",
            ));
        }
        match previous_lane {
            Some(prev) if prev >= child.summary.lane_id.as_str() => {
                return Err(TransitionError::InvalidInput(
                    "recursive child lanes not sorted unique",
                ));
            }
            _ => previous_lane = Some(child.summary.lane_id.as_str()),
        }

        let summary_hash = recursive_effect_summary_hash_v1(&child.summary);
        let child_journal_hash = recursive_child_journal_hash_v1(&child.child_journal_bytes)?;
        if child_journal_hash != child.descriptor.child_journal_hash {
            return Err(TransitionError::InvalidInput("child journal hash mismatch"));
        }
        let child_verification_claim_hash = recursive_child_verification_claim_hash_v1(
            &child.descriptor.child_image_id,
            &child.child_journal_bytes,
        )?;
        if child_verification_claim_hash != child.descriptor.child_verification_claim_hash {
            return Err(TransitionError::InvalidInput(
                "child verification claim hash mismatch",
            ));
        }
        if summary_hash != child.descriptor.child_effect_summary_hash {
            return Err(TransitionError::InvalidInput(
                "child effect summary hash mismatch",
            ));
        }
        if child.descriptor.child_statement_hash != child.summary.statement_hash {
            return Err(TransitionError::InvalidInput(
                "child statement hash mismatch",
            ));
        }
        if child.descriptor.child_image_id != child.summary.risc0_image_id {
            return Err(TransitionError::InvalidInput("child image id mismatch"));
        }
        if child.descriptor.child_profile != child.summary.proof_profile {
            return Err(TransitionError::InvalidInput(
                "child proof profile mismatch",
            ));
        }
        if child.summary.asset_delta_root != recursive_asset_delta_root_v1(&child.asset_delta_rows)?
        {
            return Err(TransitionError::InvalidInput(
                "child asset_delta_root mismatch",
            ));
        }
        if child.summary.cross_shard_outbox_root
            != recursive_cross_shard_messages_root_v1(&child.outbox_messages)?
        {
            return Err(TransitionError::InvalidInput("child outbox root mismatch"));
        }
        if child.summary.cross_shard_inbox_root
            != recursive_cross_shard_messages_root_v1(&child.inbox_messages)?
        {
            return Err(TransitionError::InvalidInput("child inbox root mismatch"));
        }
        if child.summary.accepted_receipts_root
            != recursive_receipt_ids_root_v1(&child.accepted_receipt_ids)?
        {
            return Err(TransitionError::InvalidInput(
                "child accepted_receipts_root mismatch",
            ));
        }
        if child.summary.rejected_receipts_root
            != recursive_receipt_ids_root_v1(&child.rejected_receipt_ids)?
        {
            return Err(TransitionError::InvalidInput(
                "child rejected_receipts_root mismatch",
            ));
        }

        child_verification_claim_hashes.push(child_verification_claim_hash);
        child_journal_hashes.push(child_journal_hash);
        child_summary_hashes.push(summary_hash);
        pre_lane_roots.push((child.summary.lane_id.clone(), child.summary.pre_state_root));
        post_lane_roots.push((child.summary.lane_id.clone(), child.summary.post_state_root));
        tx_roots.push(child.summary.tx_root);
        evidence_roots.push(child.summary.evidence_root);
        receipt_roots.push(child.summary.receipt_root);
        accepted_roots.push(child.summary.accepted_receipts_root);
        rejected_roots.push(child.summary.rejected_receipts_root);
        outbox_roots.push(child.summary.cross_shard_outbox_root);
        inbox_roots.push(child.summary.cross_shard_inbox_root);
        extend_bounded(
            &mut aggregate_delta_rows,
            &child.asset_delta_rows,
            input.statement.max_asset_delta_rows,
            "asset delta row count exceeds max",
        )?;
        extend_bounded(
            &mut all_outbox,
            &child.outbox_messages,
            input.statement.max_cross_shard_messages,
            "cross-shard message count exceeds max",
        )?;
        extend_bounded(
            &mut all_inbox,
            &child.inbox_messages,
            input.statement.max_cross_shard_messages,
            "cross-shard message count exceeds max",
        )?;
        extend_bounded(
            &mut all_accepted_receipts,
            &child.accepted_receipt_ids,
            input.statement.max_receipt_ids,
            "receipt id count exceeds max",
        )?;
        extend_bounded(
            &mut all_rejected_receipts,
            &child.rejected_receipt_ids,
            input.statement.max_receipt_ids,
            "receipt id count exceeds max",
        )?;
    }

    // Lane order is canonical independently of receipt-id order. Preserve duplicates
    // while globally ordering the merged partitions so validation can reject them.
    all_accepted_receipts.sort_unstable();
    all_rejected_receipts.sort_unstable();

    let canonical_delta_rows =
        canonical_asset_delta_rows_v1(&aggregate_delta_rows, &allowed_authorities)?;
    let canonical_outbox = canonical_cross_shard_messages_v1(&all_outbox)?;
    let canonical_inbox = canonical_cross_shard_messages_v1(&all_inbox)?;
    validate_asset_conservation_v1(&canonical_delta_rows)?;
    validate_receipt_partition_v1(&all_accepted_receipts, &all_rejected_receipts)?;
    validate_cross_shard_strict_cancellation_v1(
        &canonical_outbox,
        &canonical_inbox,
        input.statement.epoch_id,
    )?;

    let pre_state_root = recursive_lane_state_vector_root_v1(
        b"zenodex.risc0.recursive.pre_state_vector_root.v1",
        &pre_lane_roots,
    )?;
    let post_state_root = recursive_lane_state_vector_root_v1(
        b"zenodex.risc0.recursive.post_state_vector_root.v1",
        &post_lane_roots,
    )?;
    if pre_state_root != input.statement.expected_pre_state_root {
        return Err(TransitionError::InvalidInput(
            "recursive pre_state_root mismatch",
        ));
    }
    if post_state_root != input.statement.expected_post_state_root {
        return Err(TransitionError::InvalidInput(
            "recursive post_state_root mismatch",
        ));
    }

    Ok(RecursiveEpochJournalV1 {
        journal_version: RECURSIVE_JOURNAL_VERSION_V1,
        proof_type: PROOF_TYPE_RECURSIVE.to_string(),
        domain_separator: input.statement.domain_separator.clone(),
        chain_id: input.statement.chain_id.clone(),
        epoch_id: input.statement.epoch_id,
        proof_profile: input.statement.proof_profile.clone(),
        statement_hash,
        verifier_set_root: input.statement.verifier_set_root,
        allowed_authority_roots_root: input.statement.allowed_authority_roots_root,
        child_verification_claims_root: recursive_child_verification_claims_root_v1(
            &child_verification_claim_hashes,
        )?,
        child_journals_root: recursive_root_list_root_v1(
            b"zenodex.risc0.recursive.child_journals_root.v1",
            &child_journal_hashes,
        )?,
        child_effect_summaries_root: recursive_root_list_root_v1(
            b"zenodex.risc0.recursive.child_effect_summaries_root.v1",
            &child_summary_hashes,
        )?,
        child_count,
        pre_state_root,
        post_state_root,
        tx_root: recursive_root_list_root_v1(b"zenodex.risc0.recursive.tx_root.v1", &tx_roots)?,
        evidence_root: recursive_root_list_root_v1(
            b"zenodex.risc0.recursive.evidence_root.v1",
            &evidence_roots,
        )?,
        receipt_root: recursive_root_list_root_v1(
            b"zenodex.risc0.recursive.receipt_root.v1",
            &receipt_roots,
        )?,
        accepted_receipts_root: recursive_receipt_ids_root_v1(&all_accepted_receipts)?,
        rejected_receipts_root: recursive_receipt_ids_root_v1(&all_rejected_receipts)?,
        aggregate_asset_delta_root: recursive_asset_delta_root_v1(&canonical_delta_rows)?,
        cross_shard_outbox_root: recursive_cross_shard_messages_root_v1(&canonical_outbox)?,
        cross_shard_inbox_root: recursive_cross_shard_messages_root_v1(&canonical_inbox)?,
        cross_shard_message_ids_root: recursive_cross_shard_message_ids_root_v1(&canonical_outbox)?,
        carry_queue_pre_root: input.statement.carry_queue_pre_root,
        carry_queue_post_root: input.statement.carry_queue_post_root,
        conflict_schedule_hash: input.statement.conflict_schedule_hash,
        data_availability_root: input.statement.data_availability_root,
        public_policy_hash: input.statement.public_policy_hash,
        feature_suite_hash: input.statement.feature_suite_hash,
        dependency_lock_hash: input.statement.dependency_lock_hash,
        toolchain_lock_hash: input.statement.toolchain_lock_hash,
    })
}

pub fn recursive_statement_hash_v1(statement: &RecursiveCompositionStatementV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.statement_hash.v1");
    write_str(&mut hasher, &statement.domain_separator);
    write_u32(&mut hasher, statement.schema_version);
    write_str(&mut hasher, &statement.chain_id);
    write_u64(&mut hasher, statement.epoch_id);
    write_str(&mut hasher, &statement.proof_profile);
    write_bytes32(&mut hasher, &statement.verifier_set_root);
    write_bytes32(&mut hasher, &statement.allowed_authority_roots_root);
    write_bytes32(&mut hasher, &statement.public_policy_hash);
    write_bytes32(&mut hasher, &statement.feature_suite_hash);
    write_bytes32(&mut hasher, &statement.dependency_lock_hash);
    write_bytes32(&mut hasher, &statement.toolchain_lock_hash);
    write_bytes32(&mut hasher, &statement.expected_pre_state_root);
    write_bytes32(&mut hasher, &statement.expected_post_state_root);
    write_bytes32(&mut hasher, &statement.conflict_schedule_hash);
    write_bytes32(&mut hasher, &statement.carry_queue_pre_root);
    write_bytes32(&mut hasher, &statement.carry_queue_post_root);
    write_bytes32(&mut hasher, &statement.data_availability_root);
    write_u32(&mut hasher, statement.expected_child_count);
    write_u32(&mut hasher, statement.max_children);
    write_u32(&mut hasher, statement.max_child_journal_bytes);
    write_u32(&mut hasher, statement.max_total_child_journal_bytes);
    write_u32(&mut hasher, statement.max_asset_delta_rows);
    write_u32(&mut hasher, statement.max_cross_shard_messages);
    write_u32(&mut hasher, statement.max_receipt_ids);
    write_str(&mut hasher, &statement.cross_shard_mode);
    hasher.finalize().into()
}

pub fn recursive_child_journal_hash_v1(journal_bytes: &[u8]) -> Result<[u8; 32], TransitionError> {
    if journal_bytes.is_empty() {
        return Err(TransitionError::InvalidInput("child journal bytes empty"));
    }
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.child_journal_hash.v1");
    write_u32(
        &mut hasher,
        checked_len_u32(journal_bytes.len(), "child journal bytes too large")?,
    );
    hasher.update(journal_bytes);
    Ok(hasher.finalize().into())
}

pub fn recursive_child_verification_claim_hash_v1(
    image_id: &[u32; 8],
    journal_bytes: &[u8],
) -> Result<[u8; 32], TransitionError> {
    if journal_bytes.is_empty() {
        return Err(TransitionError::InvalidInput("child journal bytes empty"));
    }
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.child_verification_claim_hash.v1");
    write_image_id(&mut hasher, image_id);
    write_u32(
        &mut hasher,
        checked_len_u32(journal_bytes.len(), "child journal bytes too large")?,
    );
    hasher.update(journal_bytes);
    Ok(hasher.finalize().into())
}

pub fn recursive_child_verifier_id_v1(
    image_id: &[u32; 8],
    profile: &str,
) -> Result<[u8; 32], TransitionError> {
    require_nonempty(profile, "child profile empty")?;
    if image_id.iter().all(|word| *word == 0) {
        return Err(TransitionError::InvalidInput("child image id zero"));
    }
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.child_verifier_id.v1");
    write_image_id(&mut hasher, image_id);
    write_str(&mut hasher, profile);
    Ok(hasher.finalize().into())
}

pub fn recursive_effect_summary_hash_v1(summary: &RecursiveEffectSummaryV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.effect_summary_hash.v1");
    write_u32(&mut hasher, summary.summary_version);
    write_str(&mut hasher, &summary.lane_id);
    write_str(&mut hasher, &summary.lane_kind);
    write_str(&mut hasher, &summary.chain_id);
    write_u64(&mut hasher, summary.epoch_id);
    write_str(&mut hasher, &summary.proof_profile);
    write_image_id(&mut hasher, &summary.risc0_image_id);
    write_bytes32(&mut hasher, &summary.statement_hash);
    write_bytes32(&mut hasher, &summary.pre_state_root);
    write_bytes32(&mut hasher, &summary.post_state_root);
    write_bytes32(&mut hasher, &summary.tx_root);
    write_bytes32(&mut hasher, &summary.evidence_root);
    write_bytes32(&mut hasher, &summary.receipt_root);
    write_bytes32(&mut hasher, &summary.accepted_receipts_root);
    write_bytes32(&mut hasher, &summary.rejected_receipts_root);
    write_bytes32(&mut hasher, &summary.asset_delta_root);
    write_bytes32(&mut hasher, &summary.cross_shard_outbox_root);
    write_bytes32(&mut hasher, &summary.cross_shard_inbox_root);
    write_bytes32(&mut hasher, &summary.write_set_root);
    write_bytes32(&mut hasher, &summary.public_policy_hash);
    write_bytes32(&mut hasher, &summary.feature_suite_hash);
    write_bytes32(&mut hasher, &summary.dependency_lock_hash);
    write_bytes32(&mut hasher, &summary.toolchain_lock_hash);
    hasher.finalize().into()
}

pub fn compose_spot_recursive_leaf_summary_v1(
    input: SpotRecursiveLeafInputV1,
) -> Result<RecursiveEffectSummaryV1, TransitionError> {
    require_nonempty_bounded(
        &input.chain_id,
        "spot leaf chain_id empty",
        "spot leaf chain_id too long",
    )?;
    require_nonempty_bounded(
        &input.lane_id,
        "spot leaf lane_id empty",
        "spot leaf lane_id too long",
    )?;
    require_nonzero_root(
        &input.public_policy_hash,
        "spot leaf public_policy_hash zero",
    )?;
    require_nonzero_root(
        &input.feature_suite_hash,
        "spot leaf feature_suite_hash zero",
    )?;
    require_nonzero_root(
        &input.dependency_lock_hash,
        "spot leaf dependency_lock_hash zero",
    )?;
    require_nonzero_root(
        &input.toolchain_lock_hash,
        "spot leaf toolchain_lock_hash zero",
    )?;
    if input.risc0_image_id.iter().all(|word| *word == 0) {
        return Err(TransitionError::InvalidInput("spot leaf image id zero"));
    }

    let asset_delta_rows =
        spot_recursive_leaf_asset_delta_rows_v1(&input.spot_input, input.public_policy_hash)?;
    let journal = execute_state_proof_input_v1(input.spot_input)?;
    if !journal.pre_app_hash_present {
        return Err(TransitionError::InvalidInput(
            "spot recursive leaf requires pre_app_hash",
        ));
    }
    if journal.state_hash != journal.post_app_hash {
        return Err(TransitionError::InvalidInput(
            "spot recursive leaf state_hash must equal post_app_hash",
        ));
    }

    let empty_messages = Vec::new();
    let empty_receipt_ids = Vec::new();
    let summary = RecursiveEffectSummaryV1 {
        summary_version: RECURSIVE_EFFECT_SUMMARY_VERSION_V1,
        lane_id: input.lane_id,
        lane_kind: "spot".to_string(),
        chain_id: input.chain_id,
        epoch_id: input.epoch_id,
        proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1.to_string(),
        risc0_image_id: input.risc0_image_id,
        statement_hash: spot_recursive_leaf_statement_hash_v1(
            &journal,
            input.public_policy_hash,
            input.feature_suite_hash,
            input.dependency_lock_hash,
            input.toolchain_lock_hash,
        ),
        pre_state_root: journal.pre_app_hash,
        post_state_root: journal.post_app_hash,
        tx_root: journal.txs_commitment,
        evidence_root: spot_recursive_leaf_evidence_root_v1(&journal),
        receipt_root: journal.accepted_receipts_root,
        accepted_receipts_root: recursive_receipt_ids_root_v1(&empty_receipt_ids)?,
        rejected_receipts_root: recursive_receipt_ids_root_v1(&empty_receipt_ids)?,
        asset_delta_root: recursive_asset_delta_root_v1(&asset_delta_rows)?,
        cross_shard_outbox_root: recursive_cross_shard_messages_root_v1(&empty_messages)?,
        cross_shard_inbox_root: recursive_cross_shard_messages_root_v1(&empty_messages)?,
        write_set_root: spot_recursive_leaf_write_set_root_v1(&journal),
        public_policy_hash: input.public_policy_hash,
        feature_suite_hash: input.feature_suite_hash,
        dependency_lock_hash: input.dependency_lock_hash,
        toolchain_lock_hash: input.toolchain_lock_hash,
    };
    validate_recursive_effect_summary_shape_v1(&summary)?;
    Ok(summary)
}

pub fn compose_zusd_recursive_leaf_summary_v1(
    input: ZusdRecursiveLeafInputV1,
) -> Result<RecursiveEffectSummaryV1, TransitionError> {
    require_nonempty_bounded(
        &input.chain_id,
        "zUSD leaf chain_id empty",
        "zUSD leaf chain_id too long",
    )?;
    require_nonempty_bounded(
        &input.lane_id,
        "zUSD leaf lane_id empty",
        "zUSD leaf lane_id too long",
    )?;
    require_nonzero_root(
        &input.public_policy_hash,
        "zUSD leaf public_policy_hash zero",
    )?;
    require_nonzero_root(
        &input.feature_suite_hash,
        "zUSD leaf feature_suite_hash zero",
    )?;
    require_nonzero_root(
        &input.dependency_lock_hash,
        "zUSD leaf dependency_lock_hash zero",
    )?;
    require_nonzero_root(
        &input.toolchain_lock_hash,
        "zUSD leaf toolchain_lock_hash zero",
    )?;
    if input.risc0_image_id.iter().all(|word| *word == 0) {
        return Err(TransitionError::InvalidInput("zUSD leaf image id zero"));
    }

    let journal = execute_zusd_transition_v1(input.zusd_input)?;
    if !journal.pre_app_hash_present {
        return Err(TransitionError::InvalidInput(
            "zUSD recursive leaf requires pre_app_hash",
        ));
    }
    if journal.state_hash != journal.post_app_hash {
        return Err(TransitionError::InvalidInput(
            "zUSD recursive leaf state_hash must equal post_app_hash",
        ));
    }
    if journal.chain_id.as_str() != input.chain_id.as_str() {
        return Err(TransitionError::InvalidInput(
            "zUSD recursive leaf chain_id mismatch",
        ));
    }
    if journal.risc0_image_id != input.risc0_image_id {
        return Err(TransitionError::InvalidInput(
            "zUSD recursive leaf image id mismatch",
        ));
    }

    let asset_delta_rows =
        zusd_recursive_leaf_asset_delta_rows_v1(&journal, input.public_policy_hash)?;
    let empty_messages = Vec::new();
    let empty_receipt_ids = Vec::new();
    let summary = RecursiveEffectSummaryV1 {
        summary_version: RECURSIVE_EFFECT_SUMMARY_VERSION_V1,
        lane_id: input.lane_id,
        lane_kind: "zusd".to_string(),
        chain_id: input.chain_id,
        epoch_id: input.epoch_id,
        proof_profile: RECURSIVE_ZUSD_LEAF_PROFILE_V1.to_string(),
        risc0_image_id: input.risc0_image_id,
        statement_hash: zusd_recursive_leaf_statement_hash_v1(
            &journal,
            input.public_policy_hash,
            input.feature_suite_hash,
            input.dependency_lock_hash,
            input.toolchain_lock_hash,
        ),
        pre_state_root: journal.pre_app_hash,
        post_state_root: journal.post_app_hash,
        tx_root: journal.operation_hash,
        evidence_root: zusd_recursive_leaf_evidence_root_v1(&journal),
        receipt_root: journal.zusd_balance_root_hash,
        accepted_receipts_root: recursive_receipt_ids_root_v1(&empty_receipt_ids)?,
        rejected_receipts_root: recursive_receipt_ids_root_v1(&empty_receipt_ids)?,
        asset_delta_root: recursive_asset_delta_root_v1(&asset_delta_rows)?,
        cross_shard_outbox_root: recursive_cross_shard_messages_root_v1(&empty_messages)?,
        cross_shard_inbox_root: recursive_cross_shard_messages_root_v1(&empty_messages)?,
        write_set_root: zusd_recursive_leaf_write_set_root_v1(&journal),
        public_policy_hash: input.public_policy_hash,
        feature_suite_hash: input.feature_suite_hash,
        dependency_lock_hash: input.dependency_lock_hash,
        toolchain_lock_hash: input.toolchain_lock_hash,
    };
    validate_recursive_effect_summary_shape_v1(&summary)?;
    Ok(summary)
}

pub fn zusd_recursive_leaf_asset_delta_rows_v1(
    journal: &ZusdTransitionJournalV1,
    public_policy_hash: [u8; 32],
) -> Result<Vec<RecursiveAssetDeltaRowV1>, TransitionError> {
    require_nonzero_root(&public_policy_hash, "zUSD public_policy_hash zero")?;
    if journal.minted_zusd_e8 == 0 {
        return Err(TransitionError::InvalidInput(
            "zUSD recursive leaf operation unsupported: mint amount zero",
        ));
    }
    let authority_root = recursive_authority_scope_root_v1(
        public_policy_hash,
        "zusd",
        "zUSD",
        RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
    )?;
    Ok(Vec::from([RecursiveAssetDeltaRowV1 {
        asset_id: "zUSD".to_string(),
        debit_atoms: 0,
        credit_atoms: journal.minted_zusd_e8,
        authorized_mint_atoms: journal.minted_zusd_e8,
        authorized_burn_atoms: 0,
        authority_root,
    }]))
}

pub fn spot_recursive_leaf_asset_delta_rows_v1(
    input: &StateProofInputV1,
    public_policy_hash: [u8; 32],
) -> Result<Vec<RecursiveAssetDeltaRowV1>, TransitionError> {
    let mut rows = Vec::new();
    for tx in &input.txs {
        if !tx.app_ops.has_faucet && !tx.app_ops.faucet_mint.is_empty() {
            return Err(TransitionError::InvalidInput(
                "spot recursive leaf faucet mint flag mismatch",
            ));
        }
        if !tx.app_ops.has_faucet {
            continue;
        }
        for mint in &tx.app_ops.faucet_mint {
            if mint.pubkey.is_empty() || mint.asset.is_empty() {
                return Err(TransitionError::InvalidInput(
                    "faucet mint pubkey/asset empty",
                ));
            }
            if mint.asset == NATIVE_ASSET {
                return Err(TransitionError::InvalidInput(
                    "faucet cannot mint native asset",
                ));
            }
            if mint.amount == 0 {
                return Err(TransitionError::InvalidInput(
                    "faucet mint amount must be positive",
                ));
            }
            require_nonzero_root(&public_policy_hash, "spot public_policy_hash zero")?;
            let authority_root = recursive_authority_scope_root_v1(
                public_policy_hash,
                "spot",
                &mint.asset,
                RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
            )?;
            rows.push(RecursiveAssetDeltaRowV1 {
                asset_id: mint.asset.clone(),
                debit_atoms: 0,
                credit_atoms: mint.amount,
                authorized_mint_atoms: mint.amount,
                authorized_burn_atoms: 0,
                authority_root,
            });
        }
    }

    let mut pre_native_balances = BTreeMap::new();
    for entry in &input.pre_state.balances {
        if entry.asset != NATIVE_ASSET || entry.amount == 0 {
            continue;
        }
        if pre_native_balances
            .insert(entry.pubkey.clone(), entry.amount)
            .is_some()
        {
            return Err(TransitionError::InvalidInput(
                "spot recursive native pre balance duplicate",
            ));
        }
    }

    let mut post_native_balances = BTreeMap::new();
    for entry in &input.chain_balances_post {
        if entry.amount == 0 {
            post_native_balances.remove(&entry.pubkey);
        } else {
            post_native_balances.insert(entry.pubkey.clone(), entry.amount);
        }
    }

    let mut native_pubkeys = BTreeSet::new();
    native_pubkeys.extend(pre_native_balances.keys().cloned());
    native_pubkeys.extend(post_native_balances.keys().cloned());
    for pubkey in native_pubkeys {
        let pre_amount = pre_native_balances.get(&pubkey).copied().unwrap_or(0);
        let post_amount = post_native_balances.get(&pubkey).copied().unwrap_or(0);
        match post_amount.cmp(&pre_amount) {
            core::cmp::Ordering::Greater => rows.push(RecursiveAssetDeltaRowV1 {
                asset_id: NATIVE_ASSET.to_string(),
                debit_atoms: 0,
                credit_atoms: post_amount - pre_amount,
                authorized_mint_atoms: 0,
                authorized_burn_atoms: 0,
                authority_root: [0u8; 32],
            }),
            core::cmp::Ordering::Less => rows.push(RecursiveAssetDeltaRowV1 {
                asset_id: NATIVE_ASSET.to_string(),
                debit_atoms: pre_amount - post_amount,
                credit_atoms: 0,
                authorized_mint_atoms: 0,
                authorized_burn_atoms: 0,
                authority_root: [0u8; 32],
            }),
            core::cmp::Ordering::Equal => {}
        }
    }

    let allowed_authorities: BTreeSet<[u8; 32]> = rows
        .iter()
        .map(|row| row.authority_root)
        .filter(|root| *root != [0u8; 32])
        .collect();
    canonical_asset_delta_rows_v1(&rows, &allowed_authorities)
}

pub fn perps_np_recursive_leaf_asset_delta_rows_v1(
    input: &PerpsNpTransitionInputV1,
) -> Result<Vec<RecursiveAssetDeltaRowV1>, TransitionError> {
    let mut rows = Vec::new();
    for action in &input.actions {
        match action {
            PerpsNpActionV1::InitMarket {
                collateral_asset,
                insurance_seed_e8,
                ..
            } => {
                if *insurance_seed_e8 < 0 {
                    return Err(TransitionError::InvalidInput("insurance seed negative"));
                }
                if *insurance_seed_e8 > 0 {
                    let amount =
                        i128_to_u128_v1(*insurance_seed_e8, "insurance seed amount invalid")?;
                    rows.push(ordinary_asset_delta_row_v1(
                        collateral_asset,
                        amount,
                        amount,
                    ));
                }
            }
            PerpsNpActionV1::DepositCollateral {
                asset, amount_e8, ..
            } => {
                let amount = positive_i128_to_u128_v1(*amount_e8, "deposit must be positive")?;
                rows.push(ordinary_asset_delta_row_v1(asset, amount, amount));
            }
            PerpsNpActionV1::WithdrawCollateral {
                asset, amount_e8, ..
            } => {
                let amount = positive_i128_to_u128_v1(*amount_e8, "withdraw must be positive")?;
                rows.push(ordinary_asset_delta_row_v1(asset, amount, amount));
            }
            PerpsNpActionV1::SubmitIntent { .. } | PerpsNpActionV1::RunEpoch { .. } => {}
        }
    }
    canonical_asset_delta_rows_v1(&rows, &BTreeSet::new())
}

fn ordinary_asset_delta_row_v1(
    asset_id: &str,
    debit_atoms: u128,
    credit_atoms: u128,
) -> RecursiveAssetDeltaRowV1 {
    RecursiveAssetDeltaRowV1 {
        asset_id: asset_id.to_string(),
        debit_atoms,
        credit_atoms,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_root: [0u8; 32],
    }
}

fn positive_i128_to_u128_v1(value: i128, err: &'static str) -> Result<u128, TransitionError> {
    if value <= 0 {
        return Err(TransitionError::InvalidInput(err));
    }
    i128_to_u128_v1(value, err)
}

fn i128_to_u128_v1(value: i128, err: &'static str) -> Result<u128, TransitionError> {
    u128::try_from(value).map_err(|_| TransitionError::InvalidInput(err))
}

pub fn compose_perps_np_recursive_leaf_summary_v1(
    input: PerpsNpRecursiveLeafInputV1,
) -> Result<RecursiveEffectSummaryV1, TransitionError> {
    require_nonempty_bounded(
        &input.chain_id,
        "perps NP leaf chain_id empty",
        "perps NP leaf chain_id too long",
    )?;
    require_nonempty_bounded(
        &input.lane_id,
        "perps NP leaf lane_id empty",
        "perps NP leaf lane_id too long",
    )?;
    require_nonzero_root(
        &input.public_policy_hash,
        "perps NP leaf public_policy_hash zero",
    )?;
    require_nonzero_root(
        &input.feature_suite_hash,
        "perps NP leaf feature_suite_hash zero",
    )?;
    require_nonzero_root(
        &input.dependency_lock_hash,
        "perps NP leaf dependency_lock_hash zero",
    )?;
    require_nonzero_root(
        &input.toolchain_lock_hash,
        "perps NP leaf toolchain_lock_hash zero",
    )?;
    if input.risc0_image_id.iter().all(|word| *word == 0) {
        return Err(TransitionError::InvalidInput("perps NP leaf image id zero"));
    }
    let has_run_epoch = input
        .perps_input
        .actions
        .iter()
        .any(|action| matches!(action, PerpsNpActionV1::RunEpoch { .. }));

    let asset_delta_rows = perps_np_recursive_leaf_asset_delta_rows_v1(&input.perps_input)?;
    let journal = execute_perps_np_transition_v1(input.perps_input)?;
    if !journal.pre_app_hash_present {
        return Err(TransitionError::InvalidInput(
            "perps NP recursive leaf requires pre_app_hash",
        ));
    }
    if journal.state_hash != journal.post_app_hash {
        return Err(TransitionError::InvalidInput(
            "perps NP recursive leaf state_hash must equal post_app_hash",
        ));
    }
    if journal.chain_id.as_str() != input.chain_id.as_str() {
        return Err(TransitionError::InvalidInput(
            "perps NP recursive leaf chain_id mismatch",
        ));
    }
    if journal.risc0_image_id != input.risc0_image_id {
        return Err(TransitionError::InvalidInput(
            "perps NP recursive leaf image id mismatch",
        ));
    }
    if has_run_epoch && journal.participant_count < RECURSIVE_PERPS_NP_MIN_PARTICIPANTS {
        return Err(TransitionError::InvalidInput(
            "perps NP recursive leaf participant floor",
        ));
    }
    if journal.net_position_base != 0 {
        return Err(TransitionError::InvalidInput(
            "perps NP recursive leaf net position nonzero",
        ));
    }

    let empty_messages = Vec::new();
    let empty_receipt_ids = Vec::new();
    let summary = RecursiveEffectSummaryV1 {
        summary_version: RECURSIVE_EFFECT_SUMMARY_VERSION_V1,
        lane_id: input.lane_id,
        lane_kind: "perps_np".to_string(),
        chain_id: input.chain_id,
        epoch_id: input.epoch_id,
        proof_profile: RECURSIVE_PERPS_NP_LEAF_PROFILE_V1.to_string(),
        risc0_image_id: input.risc0_image_id,
        statement_hash: perps_np_recursive_leaf_statement_hash_v1(
            &journal,
            input.public_policy_hash,
            input.feature_suite_hash,
            input.dependency_lock_hash,
            input.toolchain_lock_hash,
        ),
        pre_state_root: journal.pre_app_hash,
        post_state_root: journal.post_app_hash,
        tx_root: journal.operation_hash,
        evidence_root: perps_np_recursive_leaf_evidence_root_v1(&journal),
        receipt_root: journal.receipt_root,
        accepted_receipts_root: recursive_receipt_ids_root_v1(&empty_receipt_ids)?,
        rejected_receipts_root: recursive_receipt_ids_root_v1(&empty_receipt_ids)?,
        asset_delta_root: recursive_asset_delta_root_v1(&asset_delta_rows)?,
        cross_shard_outbox_root: recursive_cross_shard_messages_root_v1(&empty_messages)?,
        cross_shard_inbox_root: recursive_cross_shard_messages_root_v1(&empty_messages)?,
        write_set_root: perps_np_recursive_leaf_write_set_root_v1(&journal),
        public_policy_hash: input.public_policy_hash,
        feature_suite_hash: input.feature_suite_hash,
        dependency_lock_hash: input.dependency_lock_hash,
        toolchain_lock_hash: input.toolchain_lock_hash,
    };
    validate_recursive_effect_summary_shape_v1(&summary)?;
    Ok(summary)
}

pub fn spot_recursive_leaf_statement_hash_v1(
    journal: &StateProofJournalV1,
    public_policy_hash: [u8; 32],
    feature_suite_hash: [u8; 32],
    dependency_lock_hash: [u8; 32],
    toolchain_lock_hash: [u8; 32],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.spot_leaf.statement.v1");
    write_u32(&mut hasher, journal.journal_version);
    write_bytes32(&mut hasher, &journal.state_hash);
    write_bytes32(&mut hasher, &journal.txs_commitment);
    write_bytes32(&mut hasher, &journal.ingress_commitment);
    write_bytes32(&mut hasher, &journal.pre_nonce_root);
    write_bytes32(&mut hasher, &journal.post_nonce_root);
    write_bytes32(&mut hasher, &journal.accepted_receipts_root);
    hasher.update([journal.pre_app_hash_present as u8]);
    write_bytes32(&mut hasher, &journal.pre_app_hash);
    write_bytes32(&mut hasher, &journal.post_app_hash);
    write_u32(&mut hasher, journal.protocol_fee_share_bps);
    match &journal.protocol_fee_recipient_pubkey {
        Some(value) => {
            hasher.update([1u8]);
            write_str(&mut hasher, value);
        }
        None => hasher.update([0u8]),
    }
    write_bytes32(&mut hasher, &journal.tx_execution_order_commitment);
    write_bytes32(&mut hasher, &public_policy_hash);
    write_bytes32(&mut hasher, &feature_suite_hash);
    write_bytes32(&mut hasher, &dependency_lock_hash);
    write_bytes32(&mut hasher, &toolchain_lock_hash);
    hasher.finalize().into()
}

pub fn zusd_recursive_leaf_statement_hash_v1(
    journal: &ZusdTransitionJournalV1,
    public_policy_hash: [u8; 32],
    feature_suite_hash: [u8; 32],
    dependency_lock_hash: [u8; 32],
    toolchain_lock_hash: [u8; 32],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.zusd_leaf.statement.v1");
    write_u32(&mut hasher, journal.journal_version);
    write_str(&mut hasher, &journal.proof_type);
    write_bytes32(&mut hasher, &journal.state_hash);
    write_str(&mut hasher, &journal.chain_id);
    hasher.update([journal.pre_app_hash_present as u8]);
    write_bytes32(&mut hasher, &journal.pre_app_hash);
    write_bytes32(&mut hasher, &journal.post_app_hash);
    write_bytes32(&mut hasher, &journal.operation_hash);
    write_bytes32(&mut hasher, &journal.state_delta_hash);
    write_bytes32(&mut hasher, &journal.oracle_binding_hash);
    write_bytes32(&mut hasher, &journal.zusd_balance_root_hash);
    write_bytes32(&mut hasher, &journal.zusd_vault_root_hash);
    write_bytes32(&mut hasher, &journal.participant_set_hash);
    write_image_id(&mut hasher, &journal.risc0_image_id);
    write_u128(&mut hasher, journal.minted_zusd_e8);
    write_u128(&mut hasher, journal.collateral_value_e8);
    write_u32(&mut hasher, journal.mcr_bps);
    write_bytes32(&mut hasher, &public_policy_hash);
    write_bytes32(&mut hasher, &feature_suite_hash);
    write_bytes32(&mut hasher, &dependency_lock_hash);
    write_bytes32(&mut hasher, &toolchain_lock_hash);
    hasher.finalize().into()
}

pub fn perps_np_recursive_leaf_statement_hash_v1(
    journal: &PerpsNpTransitionJournalV1,
    public_policy_hash: [u8; 32],
    feature_suite_hash: [u8; 32],
    dependency_lock_hash: [u8; 32],
    toolchain_lock_hash: [u8; 32],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.perps_np_leaf.statement.v1");
    write_u32(&mut hasher, journal.journal_version);
    write_str(&mut hasher, &journal.proof_type);
    write_bytes32(&mut hasher, &journal.state_hash);
    write_str(&mut hasher, &journal.chain_id);
    hasher.update([journal.pre_app_hash_present as u8]);
    write_bytes32(&mut hasher, &journal.pre_app_hash);
    write_bytes32(&mut hasher, &journal.post_app_hash);
    write_bytes32(&mut hasher, &journal.operation_hash);
    write_bytes32(&mut hasher, &journal.state_delta_hash);
    write_bytes32(&mut hasher, &journal.oracle_binding_hash);
    write_bytes32(&mut hasher, &journal.collateral_binding_hash);
    write_bytes32(&mut hasher, &journal.participant_set_hash);
    write_bytes32(&mut hasher, &journal.receipt_root);
    write_image_id(&mut hasher, &journal.risc0_image_id);
    write_u32(&mut hasher, journal.participant_count);
    write_i128(&mut hasher, journal.net_position_base);
    write_i128(&mut hasher, journal.total_collateral_e8);
    write_i128(&mut hasher, journal.funding_residual_e8);
    write_i128(&mut hasher, journal.matched_base_volume);
    write_bytes32(&mut hasher, &public_policy_hash);
    write_bytes32(&mut hasher, &feature_suite_hash);
    write_bytes32(&mut hasher, &dependency_lock_hash);
    write_bytes32(&mut hasher, &toolchain_lock_hash);
    hasher.finalize().into()
}

pub fn spot_recursive_leaf_evidence_root_v1(journal: &StateProofJournalV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.spot_leaf.evidence_root.v1");
    write_bytes32(&mut hasher, &journal.ingress_commitment);
    write_bytes32(&mut hasher, &journal.tx_execution_order_commitment);
    write_bytes32(&mut hasher, &journal.route_price_intervals_root);
    write_bytes32(&mut hasher, &journal.route_price_interval_authority_root);
    write_bytes32(
        &mut hasher,
        &journal.route_price_interval_authority_policy_root,
    );
    match journal.route_price_interval_max_width_bps {
        Some(value) => {
            hasher.update([1u8]);
            write_u64(&mut hasher, value);
        }
        None => hasher.update([0u8]),
    }
    write_u32(
        &mut hasher,
        journal.shared_pool_frontier_signature_certificate_count,
    );
    write_bytes32(
        &mut hasher,
        &journal.shared_pool_frontier_signature_certificates_root,
    );
    hasher.finalize().into()
}

pub fn perps_np_recursive_leaf_evidence_root_v1(journal: &PerpsNpTransitionJournalV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.perps_np_leaf.evidence_root.v1");
    write_bytes32(&mut hasher, &journal.oracle_binding_hash);
    write_bytes32(&mut hasher, &journal.collateral_binding_hash);
    write_bytes32(&mut hasher, &journal.participant_set_hash);
    write_bytes32(&mut hasher, &journal.receipt_root);
    write_u32(&mut hasher, journal.participant_count);
    write_i128(&mut hasher, journal.net_position_base);
    write_i128(&mut hasher, journal.total_collateral_e8);
    write_i128(&mut hasher, journal.funding_residual_e8);
    write_i128(&mut hasher, journal.matched_base_volume);
    hasher.finalize().into()
}

pub fn zusd_recursive_leaf_evidence_root_v1(journal: &ZusdTransitionJournalV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.zusd_leaf.evidence_root.v1");
    write_bytes32(&mut hasher, &journal.oracle_binding_hash);
    write_bytes32(&mut hasher, &journal.zusd_balance_root_hash);
    write_bytes32(&mut hasher, &journal.zusd_vault_root_hash);
    write_bytes32(&mut hasher, &journal.participant_set_hash);
    write_u128(&mut hasher, journal.minted_zusd_e8);
    write_u128(&mut hasher, journal.collateral_value_e8);
    write_u32(&mut hasher, journal.mcr_bps);
    hasher.finalize().into()
}

pub fn spot_recursive_leaf_write_set_root_v1(journal: &StateProofJournalV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.spot_leaf.write_set_root.v1");
    write_bytes32(&mut hasher, &journal.pre_nonce_root);
    write_bytes32(&mut hasher, &journal.post_nonce_root);
    write_bytes32(&mut hasher, &journal.pre_app_hash);
    write_bytes32(&mut hasher, &journal.post_app_hash);
    hasher.finalize().into()
}

pub fn perps_np_recursive_leaf_write_set_root_v1(journal: &PerpsNpTransitionJournalV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.perps_np_leaf.write_set_root.v1");
    write_bytes32(&mut hasher, &journal.pre_app_hash);
    write_bytes32(&mut hasher, &journal.post_app_hash);
    write_bytes32(&mut hasher, &journal.state_delta_hash);
    write_bytes32(&mut hasher, &journal.participant_set_hash);
    write_bytes32(&mut hasher, &journal.receipt_root);
    hasher.finalize().into()
}

pub fn zusd_recursive_leaf_write_set_root_v1(journal: &ZusdTransitionJournalV1) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.zusd_leaf.write_set_root.v1");
    write_bytes32(&mut hasher, &journal.pre_app_hash);
    write_bytes32(&mut hasher, &journal.post_app_hash);
    write_bytes32(&mut hasher, &journal.state_delta_hash);
    write_bytes32(&mut hasher, &journal.zusd_balance_root_hash);
    write_bytes32(&mut hasher, &journal.zusd_vault_root_hash);
    hasher.finalize().into()
}

pub fn validate_recursive_effect_summary_shape_v1(
    summary: &RecursiveEffectSummaryV1,
) -> Result<(), TransitionError> {
    if summary.summary_version != RECURSIVE_EFFECT_SUMMARY_VERSION_V1 {
        return Err(TransitionError::InvalidInput("summary_version mismatch"));
    }
    require_nonempty_bounded(
        &summary.lane_id,
        "summary lane_id empty",
        "summary lane_id too long",
    )?;
    require_nonempty_bounded(
        &summary.lane_kind,
        "summary lane_kind empty",
        "summary lane_kind too long",
    )?;
    require_nonempty_bounded(
        &summary.chain_id,
        "summary chain_id empty",
        "summary chain_id too long",
    )?;
    require_nonempty_bounded(
        &summary.proof_profile,
        "summary proof_profile empty",
        "summary proof_profile too long",
    )?;
    if summary.risc0_image_id.iter().all(|word| *word == 0) {
        return Err(TransitionError::InvalidInput("summary image id zero"));
    }
    require_nonzero_root(&summary.statement_hash, "summary statement_hash zero")?;
    require_nonzero_root(&summary.pre_state_root, "summary pre_state_root zero")?;
    require_nonzero_root(&summary.post_state_root, "summary post_state_root zero")?;
    require_nonzero_root(&summary.tx_root, "summary tx_root zero")?;
    require_nonzero_root(&summary.evidence_root, "summary evidence_root zero")?;
    require_nonzero_root(&summary.receipt_root, "summary receipt_root zero")?;
    require_nonzero_root(&summary.write_set_root, "summary write_set_root zero")?;
    require_nonzero_root(
        &summary.public_policy_hash,
        "summary public_policy_hash zero",
    )?;
    require_nonzero_root(
        &summary.feature_suite_hash,
        "summary feature_suite_hash zero",
    )?;
    require_nonzero_root(
        &summary.dependency_lock_hash,
        "summary dependency_lock_hash zero",
    )?;
    require_nonzero_root(
        &summary.toolchain_lock_hash,
        "summary toolchain_lock_hash zero",
    )?;
    Ok(())
}

pub fn recursive_verifier_set_root_v1(ids: &[[u8; 32]]) -> Result<[u8; 32], TransitionError> {
    validate_sorted_unique_roots_v1(ids, "verifier id")?;
    recursive_root_list_root_v1(b"zenodex.risc0.recursive.verifier_set_root.v1", ids)
}

pub fn recursive_child_verification_claims_root_v1(
    ids: &[[u8; 32]],
) -> Result<[u8; 32], TransitionError> {
    recursive_root_list_root_v1(
        b"zenodex.risc0.recursive.child_verification_claims_root.v1",
        ids,
    )
}

pub fn recursive_authority_set_root_v1(ids: &[[u8; 32]]) -> Result<[u8; 32], TransitionError> {
    validate_sorted_unique_roots_v1(ids, "authority root")?;
    recursive_root_list_root_v1(b"zenodex.risc0.recursive.authority_set_root.v1", ids)
}

pub fn recursive_vector_root_v1(
    domain: &'static [u8],
    roots: &[[u8; 32]],
) -> Result<[u8; 32], TransitionError> {
    recursive_root_list_root_v1(domain, roots)
}

pub fn recursive_lane_state_vector_root_v1(
    domain: &'static [u8],
    lane_roots: &[(String, [u8; 32])],
) -> Result<[u8; 32], TransitionError> {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    write_u32(
        &mut hasher,
        checked_len_u32(lane_roots.len(), "recursive lane state vector too large")?,
    );
    let mut previous_lane: Option<&str> = None;
    for (lane_id, root) in lane_roots {
        require_nonempty_bounded(
            lane_id,
            "recursive lane state id empty",
            "recursive lane state id too long",
        )?;
        if previous_lane.is_some_and(|previous| previous >= lane_id.as_str()) {
            return Err(TransitionError::InvalidInput(
                "recursive lane state ids not sorted unique",
            ));
        }
        write_str(&mut hasher, lane_id);
        write_bytes32(&mut hasher, root);
        previous_lane = Some(lane_id);
    }
    Ok(hasher.finalize().into())
}

pub fn recursive_asset_delta_root_v1(
    rows: &[RecursiveAssetDeltaRowV1],
) -> Result<[u8; 32], TransitionError> {
    validate_sorted_unique_asset_rows_v1(rows)?;
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.asset_delta_root.v1");
    write_u32(
        &mut hasher,
        checked_len_u32(rows.len(), "recursive asset delta row count too large")?,
    );
    for row in rows {
        write_str(&mut hasher, &row.asset_id);
        write_u128(&mut hasher, row.debit_atoms);
        write_u128(&mut hasher, row.credit_atoms);
        write_u128(&mut hasher, row.authorized_mint_atoms);
        write_u128(&mut hasher, row.authorized_burn_atoms);
        write_bytes32(&mut hasher, &row.authority_root);
    }
    Ok(hasher.finalize().into())
}

pub fn recursive_cross_shard_messages_root_v1(
    rows: &[RecursiveCrossShardMessageV1],
) -> Result<[u8; 32], TransitionError> {
    validate_sorted_unique_messages_v1(rows)?;
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.cross_shard_messages_root.v1");
    write_u32(
        &mut hasher,
        checked_len_u32(rows.len(), "recursive cross-shard message count too large")?,
    );
    for row in rows {
        write_cross_shard_message(&mut hasher, row);
    }
    Ok(hasher.finalize().into())
}

pub fn recursive_message_ids_root_v1(ids: &[[u8; 32]]) -> Result<[u8; 32], TransitionError> {
    validate_sorted_unique_roots_v1(ids, "message id")?;
    recursive_root_list_root_v1(b"zenodex.risc0.recursive.message_ids_root.v1", ids)
}

pub fn recursive_epoch_journal_bytes_hash_v1(
    journal_bytes: &[u8],
) -> Result<[u8; 32], TransitionError> {
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.epoch_journal_bytes_hash.v1");
    write_u32(
        &mut hasher,
        checked_len_u32(
            journal_bytes.len(),
            "recursive epoch journal byte count too large",
        )?,
    );
    hasher.update(journal_bytes);
    Ok(hasher.finalize().into())
}

pub fn recursive_cross_shard_message_ids_root_v1(
    rows: &[RecursiveCrossShardMessageV1],
) -> Result<[u8; 32], TransitionError> {
    validate_sorted_unique_messages_v1(rows)?;
    let ids: Vec<[u8; 32]> = rows.iter().map(|row| row.message_id).collect();
    recursive_message_ids_root_v1(&ids)
}

pub fn recursive_cross_shard_message_id_v1(
    row: &RecursiveCrossShardMessageV1,
) -> Result<[u8; 32], TransitionError> {
    validate_cross_shard_message_fields_v1(row)?;
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.cross_shard_message_id.v1");
    write_u64(&mut hasher, row.epoch_id);
    write_str(&mut hasher, &row.source_shard_id);
    write_str(&mut hasher, &row.destination_shard_id);
    write_str(&mut hasher, &row.asset_id);
    write_u128(&mut hasher, row.amount_atoms);
    write_bytes32(&mut hasher, &row.sender_scope_hash);
    write_bytes32(&mut hasher, &row.recipient_scope_hash);
    write_bytes32(&mut hasher, &row.source_receipt_hash);
    write_u64(&mut hasher, row.deadline_epoch);
    Ok(hasher.finalize().into())
}

pub fn recursive_authority_scope_root_v1(
    public_policy_hash: [u8; 32],
    lane_kind: &str,
    asset_id: &str,
    effect_kind: &str,
) -> Result<[u8; 32], TransitionError> {
    require_nonzero_root(&public_policy_hash, "authority public_policy_hash zero")?;
    require_nonempty_bounded(
        lane_kind,
        "authority lane_kind empty",
        "authority lane_kind too long",
    )?;
    require_nonempty_bounded(
        asset_id,
        "authority asset_id empty",
        "authority asset_id too long",
    )?;
    if effect_kind != RECURSIVE_AUTHORITY_EFFECT_MINT_V1
        && effect_kind != RECURSIVE_AUTHORITY_EFFECT_BURN_V1
    {
        return Err(TransitionError::Unsupported(
            "authority effect_kind unsupported",
        ));
    }
    let mut hasher = Sha256::new();
    hasher.update(b"zenodex.risc0.recursive.authority_scope.v1");
    write_bytes32(&mut hasher, &public_policy_hash);
    write_str(&mut hasher, lane_kind);
    write_str(&mut hasher, asset_id);
    write_str(&mut hasher, effect_kind);
    Ok(hasher.finalize().into())
}

pub fn recursive_receipt_ids_root_v1(ids: &[[u8; 32]]) -> Result<[u8; 32], TransitionError> {
    validate_sorted_unique_roots_v1(ids, "receipt id")?;
    recursive_root_list_root_v1(b"zenodex.risc0.recursive.receipt_ids_root.v1", ids)
}

fn validate_recursive_statement_v1(
    statement: &RecursiveCompositionStatementV1,
) -> Result<(), TransitionError> {
    if statement.domain_separator != RECURSIVE_DOMAIN_SEPARATOR_V1 {
        return Err(TransitionError::InvalidInput(
            "recursive domain_separator mismatch",
        ));
    }
    if statement.schema_version != RECURSIVE_STATEMENT_VERSION_V1 {
        return Err(TransitionError::InvalidInput(
            "recursive schema_version mismatch",
        ));
    }
    require_nonempty(&statement.chain_id, "recursive chain_id empty")?;
    if statement.proof_profile != RECURSIVE_EPOCH_PROFILE_V1 {
        return Err(TransitionError::Unsupported(
            "recursive proof_profile unsupported",
        ));
    }
    if statement.cross_shard_mode != RECURSIVE_STRICT_CROSS_SHARD_MODE_V1 {
        return Err(TransitionError::Unsupported(
            "recursive cross_shard_mode unsupported",
        ));
    }
    require_nonzero_root(&statement.verifier_set_root, "verifier_set_root zero")?;
    require_nonzero_root(
        &statement.allowed_authority_roots_root,
        "allowed_authority_roots_root zero",
    )?;
    require_nonzero_root(
        &statement.public_policy_hash,
        "recursive public_policy_hash zero",
    )?;
    require_nonzero_root(
        &statement.feature_suite_hash,
        "recursive feature_suite_hash zero",
    )?;
    require_nonzero_root(
        &statement.dependency_lock_hash,
        "recursive dependency_lock_hash zero",
    )?;
    require_nonzero_root(
        &statement.toolchain_lock_hash,
        "recursive toolchain_lock_hash zero",
    )?;
    require_nonzero_root(
        &statement.expected_pre_state_root,
        "recursive expected_pre_state_root zero",
    )?;
    require_nonzero_root(
        &statement.expected_post_state_root,
        "recursive expected_post_state_root zero",
    )?;
    require_nonzero_root(
        &statement.conflict_schedule_hash,
        "recursive conflict_schedule_hash zero",
    )?;
    require_nonzero_root(
        &statement.data_availability_root,
        "recursive data_availability_root zero",
    )?;
    if statement.expected_child_count == 0 {
        return Err(TransitionError::InvalidInput(
            "recursive expected_child_count zero",
        ));
    }
    if statement.max_children == 0 || statement.expected_child_count > statement.max_children {
        return Err(TransitionError::InvalidInput(
            "recursive max_children invalid",
        ));
    }
    if statement.max_child_journal_bytes == 0
        || statement.max_total_child_journal_bytes == 0
        || statement.max_child_journal_bytes > statement.max_total_child_journal_bytes
    {
        return Err(TransitionError::InvalidInput(
            "recursive child journal byte bounds invalid",
        ));
    }
    if statement.max_asset_delta_rows == 0
        || statement.max_cross_shard_messages == 0
        || statement.max_receipt_ids == 0
    {
        return Err(TransitionError::InvalidInput("recursive max rows invalid"));
    }
    if statement.carry_queue_pre_root != statement.carry_queue_post_root {
        return Err(TransitionError::Unsupported(
            "recursive carry mode unsupported",
        ));
    }
    Ok(())
}

fn validate_child_effect_v1(
    child: &RecursiveChildEffectV1,
    statement: &RecursiveCompositionStatementV1,
    allowed_verifiers: &BTreeSet<[u8; 32]>,
) -> Result<(), TransitionError> {
    require_nonzero_root(
        &child.descriptor.child_verification_claim_hash,
        "child verification claim hash zero",
    )?;
    require_nonzero_root(
        &child.descriptor.child_journal_hash,
        "child journal hash zero",
    )?;
    require_nonzero_root(
        &child.descriptor.child_effect_summary_hash,
        "child effect summary hash zero",
    )?;
    require_nonzero_root(
        &child.descriptor.child_statement_hash,
        "child statement hash zero",
    )?;
    require_nonzero_root(
        &child.descriptor.child_verifier_id,
        "child verifier id zero",
    )?;
    if child
        .descriptor
        .child_image_id
        .iter()
        .all(|word| *word == 0)
    {
        return Err(TransitionError::InvalidInput("child image id zero"));
    }
    require_nonempty(&child.descriptor.child_profile, "child profile empty")?;
    let expected_verifier_id = recursive_child_verifier_id_v1(
        &child.descriptor.child_image_id,
        &child.descriptor.child_profile,
    )?;
    if child.descriptor.child_verifier_id != expected_verifier_id {
        return Err(TransitionError::InvalidInput(
            "child verifier id image binding mismatch",
        ));
    }
    if !allowed_verifiers.contains(&expected_verifier_id) {
        return Err(TransitionError::InvalidInput(
            "child verifier id not allowed",
        ));
    }
    let child_journal_len = checked_len_u32(
        child.child_journal_bytes.len(),
        "child journal bytes length too large",
    )?;
    if child_journal_len == 0 {
        return Err(TransitionError::InvalidInput("child journal bytes empty"));
    }
    if child_journal_len > statement.max_child_journal_bytes {
        return Err(TransitionError::InvalidInput(
            "child journal bytes exceeds max",
        ));
    }

    let summary = &child.summary;
    if child.descriptor.child_profile == RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1
        || summary.proof_profile == RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1
    {
        return Err(TransitionError::InvalidInput(
            "recursive summary leaf profile not admissible",
        ));
    }
    if summary.summary_version != RECURSIVE_EFFECT_SUMMARY_VERSION_V1 {
        return Err(TransitionError::InvalidInput(
            "child summary_version mismatch",
        ));
    }
    require_nonempty(&summary.lane_id, "child lane_id empty")?;
    require_nonempty(&summary.lane_kind, "child lane_kind empty")?;
    if summary.chain_id != statement.chain_id {
        return Err(TransitionError::InvalidInput("child chain_id mismatch"));
    }
    if summary.epoch_id != statement.epoch_id {
        return Err(TransitionError::InvalidInput("child epoch_id mismatch"));
    }
    if summary.public_policy_hash != statement.public_policy_hash {
        return Err(TransitionError::InvalidInput("child policy hash mismatch"));
    }
    if summary.feature_suite_hash != statement.feature_suite_hash {
        return Err(TransitionError::InvalidInput("child feature hash mismatch"));
    }
    if summary.dependency_lock_hash != statement.dependency_lock_hash {
        return Err(TransitionError::InvalidInput(
            "child dependency hash mismatch",
        ));
    }
    if summary.toolchain_lock_hash != statement.toolchain_lock_hash {
        return Err(TransitionError::InvalidInput(
            "child toolchain hash mismatch",
        ));
    }
    require_nonzero_root(&summary.pre_state_root, "child pre_state_root zero")?;
    require_nonzero_root(&summary.post_state_root, "child post_state_root zero")?;
    require_nonzero_root(&summary.tx_root, "child tx_root zero")?;
    require_nonzero_root(&summary.evidence_root, "child evidence_root zero")?;
    require_nonzero_root(&summary.receipt_root, "child receipt_root zero")?;
    require_nonzero_root(&summary.write_set_root, "child write_set_root zero")?;
    for message in &child.outbox_messages {
        if message.source_shard_id != summary.lane_id {
            return Err(TransitionError::InvalidInput(
                "cross-shard outbox source lane mismatch",
            ));
        }
    }
    for message in &child.inbox_messages {
        if message.destination_shard_id != summary.lane_id {
            return Err(TransitionError::InvalidInput(
                "cross-shard inbox destination lane mismatch",
            ));
        }
    }
    Ok(())
}

fn validate_child_asset_authority_scopes_v1(
    child: &RecursiveChildEffectV1,
    statement: &RecursiveCompositionStatementV1,
) -> Result<(), TransitionError> {
    for row in &child.asset_delta_rows {
        let effect_kind = match (
            row.authorized_mint_atoms != 0,
            row.authorized_burn_atoms != 0,
        ) {
            (false, false) => continue,
            (true, false) => RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
            (false, true) => RECURSIVE_AUTHORITY_EFFECT_BURN_V1,
            (true, true) => {
                return Err(TransitionError::InvalidInput(
                    "asset row combines authorized mint and burn",
                ))
            }
        };
        let expected = recursive_authority_scope_root_v1(
            statement.public_policy_hash,
            &child.summary.lane_kind,
            &row.asset_id,
            effect_kind,
        )?;
        if row.authority_root != expected {
            return Err(TransitionError::InvalidInput(
                "asset authority scope mismatch",
            ));
        }
    }
    Ok(())
}

fn canonical_asset_delta_rows_v1(
    rows: &[RecursiveAssetDeltaRowV1],
    allowed_authorities: &BTreeSet<[u8; 32]>,
) -> Result<Vec<RecursiveAssetDeltaRowV1>, TransitionError> {
    let mut totals: BTreeMap<String, RecursiveAssetDeltaRowV1> = BTreeMap::new();
    for row in rows {
        require_nonempty(&row.asset_id, "asset_id empty")?;
        let has_authorized_effect =
            row.authorized_mint_atoms != 0 || row.authorized_burn_atoms != 0;
        if has_authorized_effect {
            require_nonzero_root(&row.authority_root, "asset authority root zero")?;
            if !allowed_authorities.contains(&row.authority_root) {
                return Err(TransitionError::InvalidInput(
                    "asset authority root not allowed",
                ));
            }
        } else if row.authority_root != [0u8; 32] {
            return Err(TransitionError::InvalidInput(
                "asset authority root unexpected",
            ));
        }

        let entry = totals
            .entry(row.asset_id.clone())
            .or_insert(RecursiveAssetDeltaRowV1 {
                asset_id: row.asset_id.clone(),
                debit_atoms: 0,
                credit_atoms: 0,
                authorized_mint_atoms: 0,
                authorized_burn_atoms: 0,
                authority_root: [0u8; 32],
            });
        if row.authority_root != [0u8; 32] {
            if entry.authority_root == [0u8; 32] {
                entry.authority_root = row.authority_root;
            } else if entry.authority_root != row.authority_root {
                return Err(TransitionError::InvalidInput(
                    "asset authority root conflict",
                ));
            }
        }
        entry.debit_atoms = entry
            .debit_atoms
            .checked_add(row.debit_atoms)
            .ok_or(TransitionError::Arithmetic("asset debit total overflow"))?;
        entry.credit_atoms = entry
            .credit_atoms
            .checked_add(row.credit_atoms)
            .ok_or(TransitionError::Arithmetic("asset credit total overflow"))?;
        entry.authorized_mint_atoms = entry
            .authorized_mint_atoms
            .checked_add(row.authorized_mint_atoms)
            .ok_or(TransitionError::Arithmetic("asset mint total overflow"))?;
        entry.authorized_burn_atoms = entry
            .authorized_burn_atoms
            .checked_add(row.authorized_burn_atoms)
            .ok_or(TransitionError::Arithmetic("asset burn total overflow"))?;
    }
    Ok(totals.into_values().collect())
}

fn validate_asset_conservation_v1(
    rows: &[RecursiveAssetDeltaRowV1],
) -> Result<(), TransitionError> {
    for row in rows {
        let debit_side = row
            .debit_atoms
            .checked_add(row.authorized_mint_atoms)
            .ok_or(TransitionError::Arithmetic("asset debit total overflow"))?;
        let credit_side = row
            .credit_atoms
            .checked_add(row.authorized_burn_atoms)
            .ok_or(TransitionError::Arithmetic("asset credit total overflow"))?;
        if debit_side != credit_side {
            return Err(TransitionError::InvalidInput(
                "aggregate asset delta unbalanced",
            ));
        }
    }
    Ok(())
}

fn validate_receipt_partition_v1(
    accepted: &[[u8; 32]],
    rejected: &[[u8; 32]],
) -> Result<(), TransitionError> {
    validate_sorted_unique_roots_v1(accepted, "accepted receipt id")?;
    validate_sorted_unique_roots_v1(rejected, "rejected receipt id")?;
    let accepted_set: BTreeSet<[u8; 32]> = accepted.iter().copied().collect();
    for id in rejected {
        if accepted_set.contains(id) {
            return Err(TransitionError::InvalidInput(
                "receipt id appears in accepted and rejected",
            ));
        }
    }
    Ok(())
}

fn validate_cross_shard_strict_cancellation_v1(
    outbox: &[RecursiveCrossShardMessageV1],
    inbox: &[RecursiveCrossShardMessageV1],
    expected_epoch_id: u64,
) -> Result<(), TransitionError> {
    validate_sorted_unique_messages_v1(outbox)?;
    validate_sorted_unique_messages_v1(inbox)?;
    validate_cross_shard_message_epochs_v1(outbox, expected_epoch_id)?;
    validate_cross_shard_message_epochs_v1(inbox, expected_epoch_id)?;
    if outbox.len() != inbox.len() {
        return Err(TransitionError::InvalidInput(
            "cross-shard message count mismatch",
        ));
    }
    for (left, right) in outbox.iter().zip(inbox.iter()) {
        if left != right {
            return Err(TransitionError::InvalidInput(
                "cross-shard message mismatch",
            ));
        }
    }
    Ok(())
}

fn canonical_cross_shard_messages_v1(
    rows: &[RecursiveCrossShardMessageV1],
) -> Result<Vec<RecursiveCrossShardMessageV1>, TransitionError> {
    let mut canonical = rows.to_vec();
    canonical.sort_by_key(|row| row.message_id);
    for pair in canonical.windows(2) {
        if pair[0].message_id == pair[1].message_id {
            return Err(TransitionError::InvalidInput(
                "cross-shard message id duplicate",
            ));
        }
    }
    validate_sorted_unique_messages_v1(&canonical)?;
    Ok(canonical)
}

fn validate_sorted_unique_asset_rows_v1(
    rows: &[RecursiveAssetDeltaRowV1],
) -> Result<(), TransitionError> {
    let mut prev: Option<&str> = None;
    for row in rows {
        require_nonempty(&row.asset_id, "asset_id empty")?;
        match prev {
            Some(prev_asset) if prev_asset >= row.asset_id.as_str() => {
                return Err(TransitionError::InvalidInput(
                    "asset delta rows not sorted unique",
                ));
            }
            _ => prev = Some(row.asset_id.as_str()),
        }
    }
    Ok(())
}

fn validate_sorted_unique_messages_v1(
    rows: &[RecursiveCrossShardMessageV1],
) -> Result<(), TransitionError> {
    let mut prev: Option<[u8; 32]> = None;
    for row in rows {
        require_nonzero_root(&row.message_id, "message_id zero")?;
        if row.message_id != recursive_cross_shard_message_id_v1(row)? {
            return Err(TransitionError::InvalidInput("message_id mismatch"));
        }
        match prev {
            Some(prev_id) if prev_id >= row.message_id => {
                return Err(TransitionError::InvalidInput(
                    "cross-shard messages not sorted unique",
                ));
            }
            _ => prev = Some(row.message_id),
        }
    }
    Ok(())
}

fn validate_cross_shard_message_fields_v1(
    row: &RecursiveCrossShardMessageV1,
) -> Result<(), TransitionError> {
    require_nonempty_bounded(
        &row.source_shard_id,
        "message source_shard_id empty",
        "message source_shard_id too long",
    )?;
    require_nonempty_bounded(
        &row.destination_shard_id,
        "message destination_shard_id empty",
        "message destination_shard_id too long",
    )?;
    require_nonempty_bounded(
        &row.asset_id,
        "message asset_id empty",
        "message asset_id too long",
    )?;
    if row.source_shard_id == row.destination_shard_id {
        return Err(TransitionError::InvalidInput(
            "message source and destination identical",
        ));
    }
    require_nonzero_root(&row.sender_scope_hash, "message sender_scope_hash zero")?;
    require_nonzero_root(
        &row.recipient_scope_hash,
        "message recipient_scope_hash zero",
    )?;
    require_nonzero_root(&row.source_receipt_hash, "message source_receipt_hash zero")?;
    if row.amount_atoms == 0 {
        return Err(TransitionError::InvalidInput("message amount zero"));
    }
    if row.deadline_epoch < row.epoch_id {
        return Err(TransitionError::InvalidInput(
            "message deadline before source epoch",
        ));
    }
    Ok(())
}

fn validate_cross_shard_message_epochs_v1(
    rows: &[RecursiveCrossShardMessageV1],
    expected_epoch_id: u64,
) -> Result<(), TransitionError> {
    for row in rows {
        if row.epoch_id != expected_epoch_id {
            return Err(TransitionError::InvalidInput("message epoch_id mismatch"));
        }
    }
    Ok(())
}

fn validate_sorted_unique_roots_v1(
    ids: &[[u8; 32]],
    kind: &'static str,
) -> Result<(), TransitionError> {
    let mut prev: Option<[u8; 32]> = None;
    for id in ids {
        if id.iter().all(|b| *b == 0) {
            return match kind {
                "verifier id" => Err(TransitionError::InvalidInput("verifier id zero")),
                "authority root" => Err(TransitionError::InvalidInput("authority root zero")),
                "receipt id" => Err(TransitionError::InvalidInput("receipt id zero")),
                "accepted receipt id" => {
                    Err(TransitionError::InvalidInput("accepted receipt id zero"))
                }
                "rejected receipt id" => {
                    Err(TransitionError::InvalidInput("rejected receipt id zero"))
                }
                _ => Err(TransitionError::InvalidInput("root id zero")),
            };
        }
        match prev {
            Some(prev_id) if prev_id >= *id => {
                return match kind {
                    "verifier id" => Err(TransitionError::InvalidInput(
                        "verifier ids not sorted unique",
                    )),
                    "authority root" => Err(TransitionError::InvalidInput(
                        "authority roots not sorted unique",
                    )),
                    "receipt id" => Err(TransitionError::InvalidInput(
                        "receipt ids not sorted unique",
                    )),
                    "accepted receipt id" => Err(TransitionError::InvalidInput(
                        "accepted receipt ids not sorted unique",
                    )),
                    "rejected receipt id" => Err(TransitionError::InvalidInput(
                        "rejected receipt ids not sorted unique",
                    )),
                    _ => Err(TransitionError::InvalidInput("roots not sorted unique")),
                };
            }
            _ => prev = Some(*id),
        }
    }
    Ok(())
}

fn extend_bounded<T: Clone>(
    dst: &mut Vec<T>,
    src: &[T],
    max: u32,
    err: &'static str,
) -> Result<(), TransitionError> {
    let next_len = dst
        .len()
        .checked_add(src.len())
        .ok_or(TransitionError::Arithmetic("recursive row count overflow"))?;
    let max_usize = usize::try_from(max).map_err(|_| TransitionError::Arithmetic(err))?;
    if next_len > max_usize {
        return Err(TransitionError::InvalidInput(err));
    }
    dst.extend_from_slice(src);
    Ok(())
}

fn recursive_root_list_root_v1(
    domain: &'static [u8],
    roots: &[[u8; 32]],
) -> Result<[u8; 32], TransitionError> {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    write_u32(
        &mut hasher,
        checked_len_u32(roots.len(), "recursive root vector too large")?,
    );
    for root in roots {
        write_bytes32(&mut hasher, root);
    }
    Ok(hasher.finalize().into())
}

fn require_nonempty(value: &str, msg: &'static str) -> Result<(), TransitionError> {
    if value.is_empty() {
        Err(TransitionError::InvalidInput(msg))
    } else {
        Ok(())
    }
}

fn require_nonempty_bounded(
    value: &str,
    empty_msg: &'static str,
    too_long_msg: &'static str,
) -> Result<(), TransitionError> {
    require_nonempty(value, empty_msg)?;
    if value.len() > RECURSIVE_SUMMARY_TEXT_MAX_BYTES {
        Err(TransitionError::InvalidInput(too_long_msg))
    } else {
        Ok(())
    }
}

fn require_nonzero_root(root: &[u8; 32], msg: &'static str) -> Result<(), TransitionError> {
    if root.iter().all(|b| *b == 0) {
        Err(TransitionError::InvalidInput(msg))
    } else {
        Ok(())
    }
}

fn checked_len_u32(len: usize, msg: &'static str) -> Result<u32, TransitionError> {
    u32::try_from(len).map_err(|_| TransitionError::Arithmetic(msg))
}

fn write_u32(hasher: &mut Sha256, n: u32) {
    hasher.update(n.to_be_bytes());
}

fn write_u64(hasher: &mut Sha256, n: u64) {
    hasher.update(n.to_be_bytes());
}

fn write_u128(hasher: &mut Sha256, n: u128) {
    hasher.update(n.to_be_bytes());
}

fn write_i128(hasher: &mut Sha256, n: i128) {
    hasher.update(n.to_be_bytes());
}

fn write_str(hasher: &mut Sha256, value: &str) {
    let bytes = value.as_bytes();
    let len = u32::try_from(bytes.len()).expect("recursive hash string length exceeds u32");
    write_u32(hasher, len);
    hasher.update(bytes);
}

fn write_bytes32(hasher: &mut Sha256, value: &[u8; 32]) {
    hasher.update(value);
}

fn write_image_id(hasher: &mut Sha256, image_id: &[u32; 8]) {
    for word in image_id {
        write_u32(hasher, *word);
    }
}

fn write_cross_shard_message(hasher: &mut Sha256, row: &RecursiveCrossShardMessageV1) {
    write_bytes32(hasher, &row.message_id);
    write_u64(hasher, row.epoch_id);
    write_str(hasher, &row.source_shard_id);
    write_str(hasher, &row.destination_shard_id);
    write_str(hasher, &row.asset_id);
    write_u128(hasher, row.amount_atoms);
    write_bytes32(hasher, &row.sender_scope_hash);
    write_bytes32(hasher, &row.recipient_scope_hash);
    write_bytes32(hasher, &row.source_receipt_hash);
    write_u64(hasher, row.deadline_epoch);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        accepted_receipts_root_v1, execute_perps_np_transition_v1, execute_zusd_transition_v1,
        sha256_canonical_perps_np_snapshot_v1, sha256_canonical_zusd_snapshot_v1,
        zusd_balance_root_hash_v1, ChainBalanceV1, DexBalanceEntryV1, DexStateV1, FaucetMintV1,
        OracleBindingV1, PerpsAccountV1, PerpsMarketParamsV1, PerpsNpActionV1, PerpsNpSnapshotV1,
        PerpsNpTransitionInputV1, StateProofInputV1, TauTxAppOpsV1, TauTxV1, TxIngressFactV1,
        ZusdBalanceEntryV1, ZusdOperationV1, ZusdSnapshotV1, ZusdTransitionInputV1,
        ZusdVaultEntryV1,
    };
    use alloc::string::ToString;

    fn h(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    fn image(byte: u32) -> [u32; 8] {
        [byte; 8]
    }

    fn spot_leaf_input() -> SpotRecursiveLeafInputV1 {
        let snapshot = DexStateV1::empty().to_snapshot();
        let app_hash = DexStateV1::from_snapshot(snapshot.clone())
            .unwrap()
            .canonical_app_hash_sha256();
        SpotRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "spot-lane-a".to_string(),
            risc0_image_id: image(41),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
            spot_input: StateProofInputV1 {
                state_hash: app_hash,
                block_timestamp: 1,
                pre_app_hash_present: true,
                pre_app_hash: app_hash,
                pre_state: snapshot,
                txs: Vec::new(),
                pre_nonces: Vec::new(),
                tx_ingress: Vec::new(),
                chain_balances_post: Vec::new(),
                expected_post_app_hash: app_hash,
                protocol_fee_share_bps: 0,
                protocol_fee_recipient_pubkey: None,
                tx_execution_order: Vec::new(),
                route_price_intervals: Vec::new(),
                route_price_interval_authority: None,
                route_price_interval_authority_policy: None,
                route_price_interval_max_width_bps: None,
                shared_pool_frontier_signature_certificates: Vec::new(),
            },
        }
    }

    #[test]
    fn zusd_recursive_leaf_rejects_inner_image_id_mismatch() {
        let mut input = zusd_leaf_input();
        input.zusd_input.risc0_image_id = image(43);
        assert!(matches!(
            compose_zusd_recursive_leaf_summary_v1(input),
            Err(TransitionError::InvalidInput(
                "zUSD recursive leaf image id mismatch"
            ))
        ));
    }

    #[test]
    fn perps_np_recursive_leaf_rejects_inner_image_id_mismatch() {
        let mut input = perps_leaf_input();
        input.perps_input.risc0_image_id = image(45);
        assert!(matches!(
            compose_perps_np_recursive_leaf_summary_v1(input),
            Err(TransitionError::InvalidInput(
                "perps NP recursive leaf image id mismatch"
            ))
        ));
    }

    fn oracle(price_e8: i128) -> OracleBindingV1 {
        OracleBindingV1 {
            oracle_bridge_id: "oracle-bridge-a".to_string(),
            oracle_bridge_hash: "1111111111111111111111111111111111111111111111111111111111111111"
                .to_string(),
            price_e8,
            price_timestamp: 10,
            max_staleness_seconds: 10,
            observed_at: 12,
            pre_price_batch_commitment:
                "2222222222222222222222222222222222222222222222222222222222222222".to_string(),
        }
    }

    fn zusd_leaf_input() -> ZusdRecursiveLeafInputV1 {
        let e8 = 100_000_000u128;
        let pre_state = ZusdSnapshotV1::empty();
        let pre_app_hash = sha256_canonical_zusd_snapshot_v1(&pre_state);
        let operation = ZusdOperationV1::DepositMint {
            pubkey: "wallet-a".to_string(),
            collateral_asset: "tAGRS".to_string(),
            deposit_amount_e8: 2_000 * e8,
            mint_amount_e8: 1_000 * e8,
            oracle: oracle(e8 as i128),
            mcr_bps: 11_000,
            nonce: 1,
        };
        let post_state = ZusdSnapshotV1 {
            version: 1,
            vaults: alloc::vec![ZusdVaultEntryV1 {
                pubkey: "wallet-a".to_string(),
                collateral_asset: "tAGRS".to_string(),
                collateral_amount_e8: 2_000 * e8,
                debt_zusd_e8: 1_000 * e8,
                nonce: 1,
            }],
            balances: alloc::vec![ZusdBalanceEntryV1 {
                pubkey: "wallet-a".to_string(),
                amount_e8: 1_000 * e8,
            }],
            total_debt_zusd_e8: 1_000 * e8,
        };
        let post_app_hash = sha256_canonical_zusd_snapshot_v1(&post_state);
        ZusdRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "zusd-lane-a".to_string(),
            risc0_image_id: image(42),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
            zusd_input: ZusdTransitionInputV1 {
                state_hash: post_app_hash,
                chain_id: "tau-test".to_string(),
                pre_app_hash_present: true,
                pre_app_hash,
                pre_state,
                operation,
                expected_post_app_hash: post_app_hash,
                risc0_image_id: image(42),
            },
        }
    }

    fn perps_snapshot(now_epoch: u64) -> PerpsNpSnapshotV1 {
        let e8 = 100_000_000i128;
        PerpsNpSnapshotV1 {
            version: 1,
            market_id: "BTC-PERP".to_string(),
            collateral_asset: "zUSD".to_string(),
            index_price_e8: 100 * e8,
            params: PerpsMarketParamsV1::default(),
            accounts: ["wallet-a", "wallet-b", "wallet-c", "wallet-d"]
                .iter()
                .map(|wallet| PerpsAccountV1 {
                    pubkey: (*wallet).to_string(),
                    position_base: 0,
                    entry_price_e8: 0,
                    collateral_e8: 2_000 * e8,
                    funding_paid_cum_e8: 0,
                    nonce: 1,
                })
                .collect(),
            pending_intents: Vec::new(),
            now_epoch,
            fee_pool_e8: 0,
            insurance_e8: 1_000_000_000,
            insurance_ext_e8: 1_000_000_000,
            claims_paid_e8: 0,
            net_deposited_e8: 4 * 2_000 * e8,
        }
    }

    fn perps_leaf_input() -> PerpsNpRecursiveLeafInputV1 {
        let e8 = 100_000_000i128;
        let pre_state = perps_snapshot(0);
        let post_state = perps_snapshot(1);
        let pre_app_hash = sha256_canonical_perps_np_snapshot_v1(&pre_state);
        let post_app_hash = sha256_canonical_perps_np_snapshot_v1(&post_state);
        PerpsNpRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "perps-np-lane-a".to_string(),
            risc0_image_id: image(44),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
            perps_input: PerpsNpTransitionInputV1 {
                state_hash: post_app_hash,
                chain_id: "tau-test".to_string(),
                pre_app_hash_present: true,
                pre_app_hash,
                pre_state,
                actions: alloc::vec![PerpsNpActionV1::RunEpoch {
                    oracle: oracle(100 * e8),
                    clearing_price_e8: 100 * e8,
                    funding_rate_bps: 0,
                    intents: Vec::new(),
                }],
                expected_post_app_hash: post_app_hash,
                risc0_image_id: image(44),
            },
        }
    }

    fn asset_row(asset_id: &str, debit: u128, credit: u128) -> RecursiveAssetDeltaRowV1 {
        RecursiveAssetDeltaRowV1 {
            asset_id: asset_id.to_string(),
            debit_atoms: debit,
            credit_atoms: credit,
            authorized_mint_atoms: 0,
            authorized_burn_atoms: 0,
            authority_root: [0u8; 32],
        }
    }

    fn authorized_asset_row(
        asset_id: &str,
        debit: u128,
        credit: u128,
        authorized_mint: u128,
        authorized_burn: u128,
    ) -> RecursiveAssetDeltaRowV1 {
        let effect_kind = if authorized_mint != 0 && authorized_burn == 0 {
            RECURSIVE_AUTHORITY_EFFECT_MINT_V1
        } else {
            RECURSIVE_AUTHORITY_EFFECT_BURN_V1
        };
        let authority_root =
            recursive_authority_scope_root_v1(h(10), "spot", asset_id, effect_kind).unwrap();
        RecursiveAssetDeltaRowV1 {
            asset_id: asset_id.to_string(),
            debit_atoms: debit,
            credit_atoms: credit,
            authorized_mint_atoms: authorized_mint,
            authorized_burn_atoms: authorized_burn,
            authority_root,
        }
    }

    fn message(byte: u8) -> RecursiveCrossShardMessageV1 {
        routed_message(byte, "lane-a", "lane-b")
    }

    fn routed_message(
        byte: u8,
        source_lane: &str,
        destination_lane: &str,
    ) -> RecursiveCrossShardMessageV1 {
        let mut message = RecursiveCrossShardMessageV1 {
            message_id: [0u8; 32],
            epoch_id: 7,
            source_shard_id: source_lane.to_string(),
            destination_shard_id: destination_lane.to_string(),
            asset_id: "ASSET0".to_string(),
            amount_atoms: 5,
            sender_scope_hash: h(91),
            recipient_scope_hash: h(92),
            source_receipt_hash: h(byte),
            deadline_epoch: 9,
        };
        message.message_id = recursive_cross_shard_message_id_v1(&message).unwrap();
        message
    }

    fn child(
        lane: &str,
        receipt_byte: u8,
        journal_byte: u8,
        rows: Vec<RecursiveAssetDeltaRowV1>,
        outbox: Vec<RecursiveCrossShardMessageV1>,
        inbox: Vec<RecursiveCrossShardMessageV1>,
        accepted: Vec<[u8; 32]>,
    ) -> RecursiveChildEffectV1 {
        let asset_delta_root = recursive_asset_delta_root_v1(&rows).unwrap();
        let outbox_root = recursive_cross_shard_messages_root_v1(&outbox).unwrap();
        let inbox_root = recursive_cross_shard_messages_root_v1(&inbox).unwrap();
        let accepted_root = recursive_receipt_ids_root_v1(&accepted).unwrap();
        let rejected: Vec<[u8; 32]> = Vec::new();
        let rejected_root = recursive_receipt_ids_root_v1(&rejected).unwrap();
        let summary = RecursiveEffectSummaryV1 {
            summary_version: RECURSIVE_EFFECT_SUMMARY_VERSION_V1,
            lane_id: lane.to_string(),
            lane_kind: "spot".to_string(),
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            proof_profile: "recursive_block_v1".to_string(),
            risc0_image_id: image(receipt_byte as u32),
            statement_hash: h(receipt_byte + 30),
            pre_state_root: h(receipt_byte + 40),
            post_state_root: h(receipt_byte + 50),
            tx_root: h(receipt_byte + 60),
            evidence_root: h(receipt_byte + 70),
            receipt_root: h(receipt_byte + 80),
            accepted_receipts_root: accepted_root,
            rejected_receipts_root: rejected_root,
            asset_delta_root,
            cross_shard_outbox_root: outbox_root,
            cross_shard_inbox_root: inbox_root,
            write_set_root: h(receipt_byte + 90),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
        };
        let summary_hash = recursive_effect_summary_hash_v1(&summary);
        let child_journal_bytes = alloc::vec![journal_byte, receipt_byte];
        let child_journal_hash = recursive_child_journal_hash_v1(&child_journal_bytes).unwrap();
        let child_verification_claim_hash = recursive_child_verification_claim_hash_v1(
            &summary.risc0_image_id,
            &child_journal_bytes,
        )
        .unwrap();
        let child_verifier_id =
            recursive_child_verifier_id_v1(&summary.risc0_image_id, &summary.proof_profile)
                .unwrap();
        RecursiveChildEffectV1 {
            descriptor: RecursiveChildDescriptorV1 {
                child_verification_claim_hash,
                child_journal_hash,
                child_effect_summary_hash: summary_hash,
                child_statement_hash: summary.statement_hash,
                child_image_id: summary.risc0_image_id,
                child_verifier_id,
                child_profile: summary.proof_profile.clone(),
            },
            child_journal_bytes,
            summary,
            asset_delta_rows: rows,
            outbox_messages: outbox,
            inbox_messages: inbox,
            accepted_receipt_ids: accepted,
            rejected_receipt_ids: rejected,
        }
    }

    fn valid_input() -> RecursiveCompositionInputV1 {
        let authority_roots = alloc::vec![h(6)];
        let left = child(
            "lane-a",
            21,
            31,
            alloc::vec![asset_row("ASSET0", 10, 0), asset_row("ASSET1", 0, 5)],
            alloc::vec![message(44)],
            Vec::new(),
            alloc::vec![h(81)],
        );
        let right = child(
            "lane-b",
            22,
            32,
            alloc::vec![asset_row("ASSET0", 0, 10), asset_row("ASSET1", 5, 0)],
            Vec::new(),
            alloc::vec![message(44)],
            alloc::vec![h(82)],
        );
        let mut verifier_ids = alloc::vec![
            left.descriptor.child_verifier_id,
            right.descriptor.child_verifier_id,
        ];
        verifier_ids.sort();
        let pre_state_root = recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.pre_state_vector_root.v1",
            &[
                (left.summary.lane_id.clone(), left.summary.pre_state_root),
                (right.summary.lane_id.clone(), right.summary.pre_state_root),
            ],
        )
        .unwrap();
        let post_state_root = recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.post_state_vector_root.v1",
            &[
                (left.summary.lane_id.clone(), left.summary.post_state_root),
                (right.summary.lane_id.clone(), right.summary.post_state_root),
            ],
        )
        .unwrap();
        RecursiveCompositionInputV1 {
            statement: RecursiveCompositionStatementV1 {
                domain_separator: RECURSIVE_DOMAIN_SEPARATOR_V1.to_string(),
                schema_version: RECURSIVE_STATEMENT_VERSION_V1,
                chain_id: "tau-test".to_string(),
                epoch_id: 7,
                proof_profile: RECURSIVE_EPOCH_PROFILE_V1.to_string(),
                verifier_set_root: recursive_verifier_set_root_v1(&verifier_ids).unwrap(),
                allowed_authority_roots_root: recursive_authority_set_root_v1(&authority_roots)
                    .unwrap(),
                public_policy_hash: h(10),
                feature_suite_hash: h(11),
                dependency_lock_hash: h(12),
                toolchain_lock_hash: h(13),
                expected_pre_state_root: pre_state_root,
                expected_post_state_root: post_state_root,
                conflict_schedule_hash: h(14),
                carry_queue_pre_root: h(15),
                carry_queue_post_root: h(15),
                data_availability_root: h(16),
                expected_child_count: 2,
                max_children: 8,
                max_child_journal_bytes: 64,
                max_total_child_journal_bytes: 128,
                max_asset_delta_rows: 16,
                max_cross_shard_messages: 16,
                max_receipt_ids: 16,
                cross_shard_mode: RECURSIVE_STRICT_CROSS_SHARD_MODE_V1.to_string(),
            },
            allowed_verifier_ids: verifier_ids,
            allowed_authority_roots: authority_roots,
            children: alloc::vec![left, right],
        }
    }

    fn refresh_child_effect_hashes(child: &mut RecursiveChildEffectV1) {
        child.summary.asset_delta_root =
            recursive_asset_delta_root_v1(&child.asset_delta_rows).expect("test asset rows hash");
        child.summary.cross_shard_outbox_root =
            recursive_cross_shard_messages_root_v1(&child.outbox_messages)
                .expect("test outbox rows hash");
        child.summary.cross_shard_inbox_root =
            recursive_cross_shard_messages_root_v1(&child.inbox_messages)
                .expect("test inbox rows hash");
        child.summary.accepted_receipts_root =
            recursive_receipt_ids_root_v1(&child.accepted_receipt_ids)
                .expect("test accepted receipt root");
        child.summary.rejected_receipts_root =
            recursive_receipt_ids_root_v1(&child.rejected_receipt_ids)
                .expect("test rejected receipt root");
        child.descriptor.child_effect_summary_hash =
            recursive_effect_summary_hash_v1(&child.summary);
    }

    fn single_child_input_with_rows(
        rows: Vec<RecursiveAssetDeltaRowV1>,
    ) -> RecursiveCompositionInputV1 {
        let mut input = valid_input();
        input.children.truncate(1);
        input.children[0].asset_delta_rows = rows;
        input.children[0].outbox_messages = Vec::new();
        input.children[0].inbox_messages = Vec::new();
        refresh_child_effect_hashes(&mut input.children[0]);
        input.allowed_verifier_ids = alloc::vec![input.children[0].descriptor.child_verifier_id];
        input.statement.verifier_set_root =
            recursive_verifier_set_root_v1(&input.allowed_verifier_ids).unwrap();
        input.statement.expected_child_count = 1;
        input.statement.expected_pre_state_root = recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.pre_state_vector_root.v1",
            &[(
                (input.children[0].summary.lane_id.clone()),
                input.children[0].summary.pre_state_root,
            )],
        )
        .unwrap();
        input.statement.expected_post_state_root = recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.post_state_vector_root.v1",
            &[(
                (input.children[0].summary.lane_id.clone()),
                input.children[0].summary.post_state_root,
            )],
        )
        .unwrap();
        let mut authority_roots: Vec<[u8; 32]> = input.children[0]
            .asset_delta_rows
            .iter()
            .map(|row| row.authority_root)
            .filter(|root| *root != [0u8; 32])
            .collect();
        authority_roots.sort();
        authority_roots.dedup();
        if !authority_roots.is_empty() {
            input.allowed_authority_roots = authority_roots;
            input.statement.allowed_authority_roots_root =
                recursive_authority_set_root_v1(&input.allowed_authority_roots).unwrap();
        }
        input
    }

    #[test]
    fn recursive_composition_accepts_balanced_strict_children() {
        let input = valid_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        assert_eq!(journal.child_count, 2);
        assert_eq!(journal.proof_type, PROOF_TYPE_RECURSIVE);
        assert_eq!(journal.chain_id, "tau-test");
        assert_eq!(journal.proof_profile, RECURSIVE_EPOCH_PROFILE_V1);
        assert_ne!(journal.child_verification_claims_root, [0u8; 32]);
        assert_ne!(journal.child_journals_root, [0u8; 32]);
        assert_eq!(
            journal.pre_state_root,
            input.statement.expected_pre_state_root
        );
        assert_eq!(
            journal.post_state_root,
            input.statement.expected_post_state_root
        );
        assert_eq!(journal.verifier_set_root, input.statement.verifier_set_root);
    }

    #[test]
    fn recursive_prop_composition_is_deterministic() {
        let input = valid_input();
        let first = compose_recursive_epoch_journal_v1(&input).unwrap();
        let second = compose_recursive_epoch_journal_v1(&input).unwrap();

        assert_eq!(first, second);
    }

    #[test]
    fn recursive_composition_accepts_authorized_mint_credit() {
        let input =
            single_child_input_with_rows(alloc::vec![
                authorized_asset_row("zUSD", 0, 100, 100, 0,)
            ]);
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        assert_eq!(journal.child_count, 1);
    }

    #[test]
    fn recursive_composition_rejects_wrong_aggregate_profile() {
        let mut input = valid_input();
        input.statement.proof_profile = "recursive_block_v1".to_string();

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::Unsupported(
                "recursive proof_profile unsupported"
            ))
        ));
    }

    #[test]
    fn recursive_composition_accepts_authorized_burn_debit() {
        let input =
            single_child_input_with_rows(alloc::vec![
                authorized_asset_row("zUSD", 100, 0, 0, 100,)
            ]);
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        assert_eq!(journal.child_count, 1);
    }

    #[test]
    fn recursive_composition_rejects_inverted_authorized_burn_credit() {
        let input =
            single_child_input_with_rows(alloc::vec![
                authorized_asset_row("zUSD", 0, 100, 0, 100,)
            ]);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "aggregate asset delta unbalanced"
            ))
        ));
    }

    #[test]
    fn recursive_composition_accepts_heterogeneous_child_profiles() {
        let authority_roots = alloc::vec![h(6)];
        let mut left = child(
            "lane-a",
            21,
            31,
            alloc::vec![asset_row("ASSET0", 10, 0)],
            Vec::new(),
            Vec::new(),
            alloc::vec![h(81)],
        );
        left.summary.proof_profile = RECURSIVE_SPOT_LEAF_PROFILE_V1.to_string();
        left.descriptor.child_profile = left.summary.proof_profile.clone();
        left.descriptor.child_verifier_id = recursive_child_verifier_id_v1(
            &left.summary.risc0_image_id,
            &left.summary.proof_profile,
        )
        .unwrap();
        left.descriptor.child_effect_summary_hash = recursive_effect_summary_hash_v1(&left.summary);

        let mut right = child(
            "lane-b",
            22,
            32,
            alloc::vec![asset_row("ASSET0", 0, 10)],
            Vec::new(),
            Vec::new(),
            alloc::vec![h(82)],
        );
        right.summary.proof_profile = RECURSIVE_ZUSD_LEAF_PROFILE_V1.to_string();
        right.descriptor.child_profile = right.summary.proof_profile.clone();
        right.descriptor.child_verifier_id = recursive_child_verifier_id_v1(
            &right.summary.risc0_image_id,
            &right.summary.proof_profile,
        )
        .unwrap();
        right.descriptor.child_effect_summary_hash =
            recursive_effect_summary_hash_v1(&right.summary);

        let mut verifier_ids = alloc::vec![
            left.descriptor.child_verifier_id,
            right.descriptor.child_verifier_id,
        ];
        verifier_ids.sort();
        let pre_state_root = recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.pre_state_vector_root.v1",
            &[
                (left.summary.lane_id.clone(), left.summary.pre_state_root),
                (right.summary.lane_id.clone(), right.summary.pre_state_root),
            ],
        )
        .unwrap();
        let post_state_root = recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.post_state_vector_root.v1",
            &[
                (left.summary.lane_id.clone(), left.summary.post_state_root),
                (right.summary.lane_id.clone(), right.summary.post_state_root),
            ],
        )
        .unwrap();
        let input = RecursiveCompositionInputV1 {
            statement: RecursiveCompositionStatementV1 {
                domain_separator: RECURSIVE_DOMAIN_SEPARATOR_V1.to_string(),
                schema_version: RECURSIVE_STATEMENT_VERSION_V1,
                chain_id: "tau-test".to_string(),
                epoch_id: 7,
                proof_profile: RECURSIVE_EPOCH_PROFILE_V1.to_string(),
                verifier_set_root: recursive_verifier_set_root_v1(&verifier_ids).unwrap(),
                allowed_authority_roots_root: recursive_authority_set_root_v1(&authority_roots)
                    .unwrap(),
                public_policy_hash: h(10),
                feature_suite_hash: h(11),
                dependency_lock_hash: h(12),
                toolchain_lock_hash: h(13),
                expected_pre_state_root: pre_state_root,
                expected_post_state_root: post_state_root,
                conflict_schedule_hash: h(14),
                carry_queue_pre_root: h(15),
                carry_queue_post_root: h(15),
                data_availability_root: h(16),
                expected_child_count: 2,
                max_children: 8,
                max_child_journal_bytes: 64,
                max_total_child_journal_bytes: 128,
                max_asset_delta_rows: 16,
                max_cross_shard_messages: 16,
                max_receipt_ids: 16,
                cross_shard_mode: RECURSIVE_STRICT_CROSS_SHARD_MODE_V1.to_string(),
            },
            allowed_verifier_ids: verifier_ids,
            allowed_authority_roots: authority_roots,
            children: alloc::vec![left, right],
        };
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        assert_eq!(journal.proof_profile, RECURSIVE_EPOCH_PROFILE_V1);
        assert_eq!(journal.child_count, 2);
    }

    #[test]
    fn recursive_composition_rejects_unbalanced_asset_delta() {
        let mut input = valid_input();
        input.children[1].asset_delta_rows[0].credit_atoms = 9;
        input.children[1].summary.asset_delta_root =
            recursive_asset_delta_root_v1(&input.children[1].asset_delta_rows).unwrap();
        input.children[1].descriptor.child_effect_summary_hash =
            recursive_effect_summary_hash_v1(&input.children[1].summary);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "aggregate asset delta unbalanced"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_child_summary_hash_mismatch() {
        let mut input = valid_input();
        input.children[0].descriptor.child_effect_summary_hash = h(99);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "child effect summary hash mismatch"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_child_journal_hash_mismatch() {
        let mut input = valid_input();
        input.children[0].descriptor.child_journal_hash = h(99);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput("child journal hash mismatch"))
        ));
    }

    #[test]
    fn recursive_effect_summary_shape_rejects_zero_image_id() {
        let input = valid_input();
        let mut summary = input.children[0].summary.clone();
        summary.risc0_image_id = [0u32; 8];
        assert!(matches!(
            validate_recursive_effect_summary_shape_v1(&summary),
            Err(TransitionError::InvalidInput("summary image id zero"))
        ));
    }

    #[test]
    fn recursive_effect_summary_shape_rejects_oversized_text() {
        let input = valid_input();
        let mut summary = input.children[0].summary.clone();
        summary.lane_id = "x".repeat(RECURSIVE_SUMMARY_TEXT_MAX_BYTES + 1);
        assert!(matches!(
            validate_recursive_effect_summary_shape_v1(&summary),
            Err(TransitionError::InvalidInput("summary lane_id too long"))
        ));
    }

    #[test]
    fn spot_recursive_leaf_derives_summary_from_checked_transition() {
        let input = spot_leaf_input();
        let expected_receipt_root =
            accepted_receipts_root_v1(&input.spot_input.txs, &input.spot_input.tx_ingress).unwrap();
        let app_hash = input.spot_input.expected_post_app_hash;
        let summary = compose_spot_recursive_leaf_summary_v1(input).unwrap();
        assert_eq!(summary.lane_kind, "spot");
        assert_eq!(summary.proof_profile, RECURSIVE_SPOT_LEAF_PROFILE_V1);
        assert_eq!(summary.pre_state_root, app_hash);
        assert_eq!(summary.post_state_root, app_hash);
        assert_eq!(summary.receipt_root, expected_receipt_root);
        assert_eq!(
            summary.accepted_receipts_root,
            recursive_receipt_ids_root_v1(&[]).unwrap()
        );
        assert_eq!(
            summary.asset_delta_root,
            recursive_asset_delta_root_v1(&[]).unwrap()
        );
    }

    #[test]
    fn spot_recursive_leaf_rejects_missing_pre_app_hash() {
        let mut input = spot_leaf_input();
        input.spot_input.pre_app_hash_present = false;
        input.spot_input.pre_app_hash = [0u8; 32];
        assert!(matches!(
            compose_spot_recursive_leaf_summary_v1(input),
            Err(TransitionError::InvalidInput(
                "spot recursive leaf requires pre_app_hash"
            ))
        ));
    }

    #[test]
    fn spot_recursive_leaf_rejects_state_hash_post_root_drift() {
        let mut input = spot_leaf_input();
        input.spot_input.state_hash = h(200);
        assert!(matches!(
            compose_spot_recursive_leaf_summary_v1(input),
            Err(TransitionError::InvalidInput(
                "spot recursive leaf state_hash must equal post_app_hash"
            ))
        ));
    }

    #[test]
    fn spot_recursive_leaf_derives_faucet_asset_rows() {
        let mut input = spot_leaf_input();
        let public_policy_hash = input.public_policy_hash;
        input.spot_input.txs = alloc::vec![TauTxV1 {
            sender_pubkey: "wallet-a".to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: true,
                faucet_mint: alloc::vec![FaucetMintV1 {
                    pubkey: "wallet-a".to_string(),
                    asset: "TEST".to_string(),
                    amount: 7,
                }],
                has_intents: false,
                intents: Vec::new(),
            },
        }];
        input.spot_input.tx_ingress = alloc::vec![TxIngressFactV1 {
            sender_pubkey: "wallet-a".to_string(),
            nonce: 0,
        }];
        let mut post_state = DexStateV1::empty();
        post_state.add_balance("wallet-a", "TEST", 7).unwrap();
        input.spot_input.expected_post_app_hash = post_state.canonical_app_hash_sha256();
        input.spot_input.state_hash = input.spot_input.expected_post_app_hash;

        let rows =
            spot_recursive_leaf_asset_delta_rows_v1(&input.spot_input, public_policy_hash).unwrap();
        let summary = compose_spot_recursive_leaf_summary_v1(input).unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].asset_id, "TEST");
        assert_eq!(rows[0].credit_atoms, 7);
        assert_eq!(rows[0].authorized_mint_atoms, 7);
        assert_eq!(
            rows[0].authority_root,
            recursive_authority_scope_root_v1(
                public_policy_hash,
                "spot",
                "TEST",
                RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
            )
            .unwrap()
        );
        assert_eq!(
            summary.asset_delta_root,
            recursive_asset_delta_root_v1(&rows).unwrap()
        );
    }

    #[test]
    fn spot_recursive_leaf_rejects_faucet_mint_flag_mismatch() {
        let mut input = spot_leaf_input();
        input.spot_input.txs = alloc::vec![TauTxV1 {
            sender_pubkey: "wallet-a".to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: alloc::vec![FaucetMintV1 {
                    pubkey: "wallet-a".to_string(),
                    asset: "TEST".to_string(),
                    amount: 7,
                }],
                has_intents: false,
                intents: Vec::new(),
            },
        }];
        assert!(matches!(
            spot_recursive_leaf_asset_delta_rows_v1(&input.spot_input, input.public_policy_hash),
            Err(TransitionError::InvalidInput(
                "spot recursive leaf faucet mint flag mismatch"
            ))
        ));
    }

    #[test]
    fn spot_recursive_leaf_derives_native_balance_sync_rows() {
        let mut input = spot_leaf_input();
        input.spot_input.pre_state.balances = alloc::vec![DexBalanceEntryV1 {
            pubkey: "wallet-a".to_string(),
            asset: NATIVE_ASSET.to_string(),
            amount: 10,
        }];
        input.spot_input.chain_balances_post = alloc::vec![
            ChainBalanceV1 {
                pubkey: "wallet-a".to_string(),
                amount: 4,
            },
            ChainBalanceV1 {
                pubkey: "wallet-b".to_string(),
                amount: 11,
            }
        ];
        let pre_state = DexStateV1::from_snapshot(input.spot_input.pre_state.clone()).unwrap();
        let pre_hash = pre_state.canonical_app_hash_sha256();
        let mut post_state = pre_state;
        post_state.sync_native_balances_post(&input.spot_input.chain_balances_post);
        let post_hash = post_state.canonical_app_hash_sha256();
        input.spot_input.pre_app_hash = pre_hash;
        input.spot_input.expected_post_app_hash = post_hash;
        input.spot_input.state_hash = post_hash;

        let rows =
            spot_recursive_leaf_asset_delta_rows_v1(&input.spot_input, input.public_policy_hash)
                .unwrap();
        let summary = compose_spot_recursive_leaf_summary_v1(input).unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].asset_id, NATIVE_ASSET);
        assert_eq!(rows[0].debit_atoms, 6);
        assert_eq!(rows[0].credit_atoms, 11);
        assert_eq!(rows[0].authority_root, [0u8; 32]);
        assert_eq!(
            summary.asset_delta_root,
            recursive_asset_delta_root_v1(&rows).unwrap()
        );
    }

    #[test]
    fn zusd_recursive_leaf_derives_summary_from_checked_transition() {
        let input = zusd_leaf_input();
        let public_policy_hash = input.public_policy_hash;
        let journal = execute_zusd_transition_v1(input.zusd_input.clone()).unwrap();
        let asset_delta_rows =
            zusd_recursive_leaf_asset_delta_rows_v1(&journal, public_policy_hash).unwrap();
        let expected_balance_root = zusd_balance_root_hash_v1(&ZusdSnapshotV1 {
            version: 1,
            vaults: alloc::vec![ZusdVaultEntryV1 {
                pubkey: "wallet-a".to_string(),
                collateral_asset: "tAGRS".to_string(),
                collateral_amount_e8: 200_000_000_000,
                debt_zusd_e8: 100_000_000_000,
                nonce: 1,
            }],
            balances: alloc::vec![ZusdBalanceEntryV1 {
                pubkey: "wallet-a".to_string(),
                amount_e8: 100_000_000_000,
            }],
            total_debt_zusd_e8: 100_000_000_000,
        });
        let summary = compose_zusd_recursive_leaf_summary_v1(input).unwrap();
        assert_eq!(summary.lane_kind, "zusd");
        assert_eq!(summary.proof_profile, RECURSIVE_ZUSD_LEAF_PROFILE_V1);
        assert_eq!(summary.pre_state_root, journal.pre_app_hash);
        assert_eq!(summary.post_state_root, journal.post_app_hash);
        assert_eq!(summary.tx_root, journal.operation_hash);
        assert_eq!(summary.receipt_root, expected_balance_root);
        assert_eq!(
            summary.asset_delta_root,
            recursive_asset_delta_root_v1(&asset_delta_rows).unwrap()
        );
        assert_eq!(asset_delta_rows.len(), 1);
        assert_eq!(asset_delta_rows[0].asset_id, "zUSD");
        assert_eq!(asset_delta_rows[0].credit_atoms, journal.minted_zusd_e8);
        assert_eq!(
            asset_delta_rows[0].authorized_mint_atoms,
            journal.minted_zusd_e8
        );
        assert_eq!(
            asset_delta_rows[0].authority_root,
            recursive_authority_scope_root_v1(
                public_policy_hash,
                "zusd",
                "zUSD",
                RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
            )
            .unwrap()
        );
    }

    #[test]
    fn zusd_recursive_leaf_asset_delta_row_rejects_zero_authority_root() {
        let input = zusd_leaf_input();
        let journal = execute_zusd_transition_v1(input.zusd_input.clone()).unwrap();
        assert!(matches!(
            zusd_recursive_leaf_asset_delta_rows_v1(&journal, [0u8; 32]),
            Err(TransitionError::InvalidInput(
                "zUSD public_policy_hash zero"
            ))
        ));
    }

    #[test]
    fn zusd_recursive_leaf_asset_delta_row_rejects_zero_minted_amount() {
        let input = zusd_leaf_input();
        let mut journal = execute_zusd_transition_v1(input.zusd_input.clone()).unwrap();
        journal.minted_zusd_e8 = 0;
        assert!(matches!(
            zusd_recursive_leaf_asset_delta_rows_v1(&journal, input.public_policy_hash),
            Err(TransitionError::InvalidInput(
                "zUSD recursive leaf operation unsupported: mint amount zero"
            ))
        ));
    }

    #[test]
    fn zusd_recursive_leaf_rejects_chain_id_relabel() {
        let mut input = zusd_leaf_input();
        input.chain_id = "tau-other".to_string();
        assert!(matches!(
            compose_zusd_recursive_leaf_summary_v1(input),
            Err(TransitionError::InvalidInput(
                "zUSD recursive leaf chain_id mismatch"
            ))
        ));
    }

    #[test]
    fn zusd_recursive_leaf_rejects_missing_pre_app_hash() {
        let mut input = zusd_leaf_input();
        input.zusd_input.pre_app_hash_present = false;
        input.zusd_input.pre_app_hash = [0u8; 32];
        assert!(matches!(
            compose_zusd_recursive_leaf_summary_v1(input),
            Err(TransitionError::InvalidInput(
                "zUSD recursive leaf requires pre_app_hash"
            ))
        ));
    }

    #[test]
    fn zusd_recursive_leaf_rejects_state_hash_post_root_drift() {
        let mut input = zusd_leaf_input();
        input.zusd_input.state_hash = h(201);
        assert!(matches!(
            compose_zusd_recursive_leaf_summary_v1(input),
            Err(TransitionError::InvalidInput(
                "zUSD recursive leaf state_hash must equal post_app_hash"
            ))
        ));
    }

    #[test]
    fn perps_np_recursive_leaf_derives_summary_from_checked_transition() {
        let input = perps_leaf_input();
        let journal = execute_perps_np_transition_v1(input.perps_input.clone()).unwrap();
        let rows = perps_np_recursive_leaf_asset_delta_rows_v1(&input.perps_input).unwrap();
        let summary = compose_perps_np_recursive_leaf_summary_v1(input).unwrap();
        assert_eq!(summary.lane_kind, "perps_np");
        assert_eq!(summary.proof_profile, RECURSIVE_PERPS_NP_LEAF_PROFILE_V1);
        assert_eq!(summary.pre_state_root, journal.pre_app_hash);
        assert_eq!(summary.post_state_root, journal.post_app_hash);
        assert_eq!(summary.tx_root, journal.operation_hash);
        assert_eq!(summary.receipt_root, journal.receipt_root);
        assert_eq!(journal.participant_count, 4);
        assert_eq!(journal.net_position_base, 0);
        assert_eq!(
            summary.asset_delta_root,
            recursive_asset_delta_root_v1(&rows).unwrap()
        );
        assert!(rows.is_empty());
    }

    #[test]
    fn perps_np_recursive_leaf_derives_init_market_seed_rows() {
        let pre_state = PerpsNpSnapshotV1 {
            version: 1,
            market_id: String::new(),
            collateral_asset: String::new(),
            index_price_e8: 0,
            params: PerpsMarketParamsV1::default(),
            accounts: Vec::new(),
            pending_intents: Vec::new(),
            now_epoch: 0,
            fee_pool_e8: 0,
            insurance_e8: 0,
            insurance_ext_e8: 0,
            claims_paid_e8: 0,
            net_deposited_e8: 0,
        };
        let post_state = PerpsNpSnapshotV1 {
            version: 1,
            market_id: "ETH-PERP".to_string(),
            collateral_asset: "USDC".to_string(),
            index_price_e8: 100_000_000,
            params: PerpsMarketParamsV1::default(),
            accounts: Vec::new(),
            pending_intents: Vec::new(),
            now_epoch: 0,
            fee_pool_e8: 0,
            insurance_e8: 19,
            insurance_ext_e8: 19,
            claims_paid_e8: 0,
            net_deposited_e8: 0,
        };
        let pre_app_hash = sha256_canonical_perps_np_snapshot_v1(&pre_state);
        let post_app_hash = sha256_canonical_perps_np_snapshot_v1(&post_state);
        let input = PerpsNpRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "perps-np-lane-a".to_string(),
            risc0_image_id: image(44),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
            perps_input: PerpsNpTransitionInputV1 {
                state_hash: post_app_hash,
                chain_id: "tau-test".to_string(),
                pre_app_hash_present: true,
                pre_app_hash,
                pre_state,
                actions: alloc::vec![PerpsNpActionV1::InitMarket {
                    market_id: "ETH-PERP".to_string(),
                    collateral_asset: "USDC".to_string(),
                    index_price_e8: 100_000_000,
                    params: PerpsMarketParamsV1::default(),
                    insurance_seed_e8: 19,
                }],
                expected_post_app_hash: post_app_hash,
                risc0_image_id: image(44),
            },
        };
        let rows = perps_np_recursive_leaf_asset_delta_rows_v1(&input.perps_input).unwrap();
        let summary = compose_perps_np_recursive_leaf_summary_v1(input).unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].asset_id, "USDC");
        assert_eq!(rows[0].debit_atoms, 19);
        assert_eq!(rows[0].credit_atoms, 19);
        let aggregate = single_child_input_with_rows(rows.clone());
        compose_recursive_epoch_journal_v1(&aggregate).unwrap();
        assert_eq!(
            summary.asset_delta_root,
            recursive_asset_delta_root_v1(&rows).unwrap()
        );
    }

    #[test]
    fn perps_np_recursive_leaf_derives_deposit_rows_without_epoch_floor() {
        let e8 = 100_000_000i128;
        let mut pre_state = perps_snapshot(0);
        pre_state.collateral_asset = "USDC".to_string();
        let mut post_state = pre_state.clone();
        post_state.accounts[0].collateral_e8 += 3 * e8;
        post_state.accounts[0].nonce = 2;
        post_state.net_deposited_e8 += 3 * e8;
        let pre_app_hash = sha256_canonical_perps_np_snapshot_v1(&pre_state);
        let post_app_hash = sha256_canonical_perps_np_snapshot_v1(&post_state);
        let input = PerpsNpRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "perps-np-lane-a".to_string(),
            risc0_image_id: image(44),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
            perps_input: PerpsNpTransitionInputV1 {
                state_hash: post_app_hash,
                chain_id: "tau-test".to_string(),
                pre_app_hash_present: true,
                pre_app_hash,
                pre_state,
                actions: alloc::vec![PerpsNpActionV1::DepositCollateral {
                    pubkey: "wallet-a".to_string(),
                    asset: "USDC".to_string(),
                    amount_e8: 3 * e8,
                    nonce: 2,
                    collateral_binding: None,
                }],
                expected_post_app_hash: post_app_hash,
                risc0_image_id: image(44),
            },
        };
        let rows = perps_np_recursive_leaf_asset_delta_rows_v1(&input.perps_input).unwrap();
        let summary = compose_perps_np_recursive_leaf_summary_v1(input).unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].asset_id, "USDC");
        assert_eq!(rows[0].debit_atoms, (3 * e8) as u128);
        assert_eq!(rows[0].credit_atoms, (3 * e8) as u128);
        let aggregate = single_child_input_with_rows(rows.clone());
        compose_recursive_epoch_journal_v1(&aggregate).unwrap();
        assert_eq!(
            summary.asset_delta_root,
            recursive_asset_delta_root_v1(&rows).unwrap()
        );
    }

    #[test]
    fn perps_np_recursive_leaf_derives_withdraw_rows_without_epoch_floor() {
        let e8 = 100_000_000i128;
        let mut pre_state = perps_snapshot(0);
        pre_state.collateral_asset = "USDC".to_string();
        let mut post_state = pre_state.clone();
        post_state.accounts[0].collateral_e8 -= 2 * e8;
        post_state.accounts[0].nonce = 2;
        post_state.net_deposited_e8 -= 2 * e8;
        let pre_app_hash = sha256_canonical_perps_np_snapshot_v1(&pre_state);
        let post_app_hash = sha256_canonical_perps_np_snapshot_v1(&post_state);
        let input = PerpsNpRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "perps-np-lane-a".to_string(),
            risc0_image_id: image(44),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
            perps_input: PerpsNpTransitionInputV1 {
                state_hash: post_app_hash,
                chain_id: "tau-test".to_string(),
                pre_app_hash_present: true,
                pre_app_hash,
                pre_state,
                actions: alloc::vec![PerpsNpActionV1::WithdrawCollateral {
                    pubkey: "wallet-a".to_string(),
                    asset: "USDC".to_string(),
                    amount_e8: 2 * e8,
                    nonce: 2,
                }],
                expected_post_app_hash: post_app_hash,
                risc0_image_id: image(44),
            },
        };
        let rows = perps_np_recursive_leaf_asset_delta_rows_v1(&input.perps_input).unwrap();
        let summary = compose_perps_np_recursive_leaf_summary_v1(input).unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].asset_id, "USDC");
        assert_eq!(rows[0].debit_atoms, (2 * e8) as u128);
        assert_eq!(rows[0].credit_atoms, (2 * e8) as u128);
        let aggregate = single_child_input_with_rows(rows.clone());
        compose_recursive_epoch_journal_v1(&aggregate).unwrap();
        assert_eq!(
            summary.asset_delta_root,
            recursive_asset_delta_root_v1(&rows).unwrap()
        );
    }

    #[test]
    fn perps_np_recursive_leaf_rejects_missing_pre_app_hash() {
        let mut input = perps_leaf_input();
        input.perps_input.pre_app_hash_present = false;
        input.perps_input.pre_app_hash = [0u8; 32];
        assert!(matches!(
            compose_perps_np_recursive_leaf_summary_v1(input),
            Err(TransitionError::InvalidInput(
                "perps NP recursive leaf requires pre_app_hash"
            ))
        ));
    }

    #[test]
    fn perps_np_recursive_leaf_rejects_state_hash_post_root_drift() {
        let mut input = perps_leaf_input();
        input.perps_input.state_hash = h(202);
        assert!(matches!(
            compose_perps_np_recursive_leaf_summary_v1(input),
            Err(TransitionError::InvalidInput(
                "perps NP recursive leaf state_hash must equal post_app_hash"
            ))
        ));
    }

    #[test]
    fn perps_np_recursive_leaf_rejects_chain_id_relabel() {
        let mut input = perps_leaf_input();
        input.chain_id = "tau-other".to_string();
        assert!(matches!(
            compose_perps_np_recursive_leaf_summary_v1(input),
            Err(TransitionError::InvalidInput(
                "perps NP recursive leaf chain_id mismatch"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_child_verification_claim_hash_mismatch() {
        let mut input = valid_input();
        input.children[0].descriptor.child_verification_claim_hash = h(99);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "child verification claim hash mismatch"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_child_journal_bytes_over_bound() {
        let mut input = valid_input();
        input.statement.max_child_journal_bytes = 1;
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "child journal bytes exceeds max"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_total_child_journal_bytes_over_bound() {
        let mut input = valid_input();
        input.statement.max_child_journal_bytes = 2;
        input.statement.max_total_child_journal_bytes = 3;
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "recursive total child journal bytes exceeds max"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_child_verifier_id_image_binding_mismatch() {
        let mut input = valid_input();
        input.children[0].descriptor.child_verifier_id = h(99);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "child verifier id image binding mismatch"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_stale_verifier_id() {
        let mut input = valid_input();
        input.allowed_verifier_ids = alloc::vec![input.children[1].descriptor.child_verifier_id];
        input.statement.verifier_set_root =
            recursive_verifier_set_root_v1(&input.allowed_verifier_ids).unwrap();
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "child verifier id not allowed"
            ))
        ));
    }

    #[test]
    fn recursive_composition_accepts_distinct_children_sharing_one_verifier_id() {
        let mut input = valid_input();
        let shared_image_id = input.children[0].descriptor.child_image_id;
        let shared_profile = input.children[0].descriptor.child_profile.clone();
        let shared_verifier_id = input.children[0].descriptor.child_verifier_id;
        input.children[1].summary.risc0_image_id = shared_image_id;
        input.children[1].summary.proof_profile = shared_profile.clone();
        input.children[1].descriptor.child_image_id = shared_image_id;
        input.children[1].descriptor.child_profile = shared_profile;
        input.children[1].descriptor.child_verifier_id = shared_verifier_id;
        input.children[1].descriptor.child_verification_claim_hash =
            recursive_child_verification_claim_hash_v1(
                &shared_image_id,
                &input.children[1].child_journal_bytes,
            )
            .unwrap();
        input.children[1].descriptor.child_effect_summary_hash =
            recursive_effect_summary_hash_v1(&input.children[1].summary);
        input.allowed_verifier_ids = alloc::vec![shared_verifier_id];
        input.statement.verifier_set_root =
            recursive_verifier_set_root_v1(&input.allowed_verifier_ids).unwrap();

        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();

        assert_eq!(journal.child_count, 2);
        assert_eq!(journal.verifier_set_root, input.statement.verifier_set_root);
    }

    #[test]
    fn recursive_composition_rejects_duplicate_supplied_verifier_ids() {
        let mut input = valid_input();
        let verifier_id = input.children[0].descriptor.child_verifier_id;
        input.allowed_verifier_ids = alloc::vec![verifier_id, verifier_id];

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "verifier ids not sorted unique"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_synthetic_summary_leaf_child() {
        let mut input = valid_input();
        input.children[0].summary.proof_profile =
            RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1.to_string();
        input.children[0].descriptor.child_profile =
            input.children[0].summary.proof_profile.clone();
        input.children[0].descriptor.child_effect_summary_hash =
            recursive_effect_summary_hash_v1(&input.children[0].summary);
        input.children[0].descriptor.child_verifier_id = recursive_child_verifier_id_v1(
            &input.children[0].descriptor.child_image_id,
            &input.children[0].descriptor.child_profile,
        )
        .unwrap();
        input.allowed_verifier_ids = input
            .children
            .iter()
            .map(|child| child.descriptor.child_verifier_id)
            .collect();
        input.statement.verifier_set_root =
            recursive_verifier_set_root_v1(&input.allowed_verifier_ids).unwrap();

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "recursive summary leaf profile not admissible"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_child_omission() {
        let mut input = valid_input();
        input.children.pop();
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "recursive child count mismatch"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_child_substitution_by_epoch() {
        let mut input = valid_input();
        input.children[1].summary.epoch_id = 8;
        input.children[1].descriptor.child_effect_summary_hash =
            recursive_effect_summary_hash_v1(&input.children[1].summary);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput("child epoch_id mismatch"))
        ));
    }

    #[test]
    fn recursive_prop_receipt_roots_are_invariant_to_lane_interleaving() {
        let accepted_ids = [h(1), h(3), h(5), h(7)];
        let rejected_ids = [h(2), h(4), h(6), h(8)];
        let expected_accepted_root = recursive_receipt_ids_root_v1(&accepted_ids).unwrap();
        let expected_rejected_root = recursive_receipt_ids_root_v1(&rejected_ids).unwrap();

        for lane_mask in 0u8..16 {
            let mut input = valid_input();
            for child in &mut input.children {
                child.accepted_receipt_ids.clear();
                child.rejected_receipt_ids.clear();
            }
            for (index, id) in accepted_ids.iter().enumerate() {
                let lane_index = usize::from((lane_mask >> index) & 1);
                input.children[lane_index].accepted_receipt_ids.push(*id);
            }
            for (index, id) in rejected_ids.iter().enumerate() {
                let lane_index = usize::from((lane_mask >> (3 - index)) & 1);
                input.children[lane_index].rejected_receipt_ids.push(*id);
            }
            refresh_child_effect_hashes(&mut input.children[0]);
            refresh_child_effect_hashes(&mut input.children[1]);

            let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
            assert_eq!(journal.accepted_receipts_root, expected_accepted_root);
            assert_eq!(journal.rejected_receipts_root, expected_rejected_root);
        }
    }

    #[test]
    fn recursive_composition_rejects_duplicate_receipt_id_within_lane() {
        let mut input = valid_input();
        input.children[0].accepted_receipt_ids = alloc::vec![h(81), h(81)];

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "receipt ids not sorted unique"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_duplicate_receipt_id() {
        let mut input = valid_input();
        input.children[1].accepted_receipt_ids = alloc::vec![h(81)];
        input.children[1].summary.accepted_receipts_root =
            recursive_receipt_ids_root_v1(&input.children[1].accepted_receipt_ids).unwrap();
        input.children[1].descriptor.child_effect_summary_hash =
            recursive_effect_summary_hash_v1(&input.children[1].summary);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "accepted receipt ids not sorted unique"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_duplicate_rejected_receipt_across_lanes() {
        let mut input = valid_input();
        input.children[0].rejected_receipt_ids = alloc::vec![h(83)];
        input.children[1].rejected_receipt_ids = alloc::vec![h(83)];
        refresh_child_effect_hashes(&mut input.children[0]);
        refresh_child_effect_hashes(&mut input.children[1]);

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "rejected receipt ids not sorted unique"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_accepted_rejected_receipt_collision() {
        let mut input = valid_input();
        input.children[1].rejected_receipt_ids = alloc::vec![h(81)];
        refresh_child_effect_hashes(&mut input.children[1]);

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "receipt id appears in accepted and rejected"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_cross_shard_mismatch() {
        let mut input = valid_input();
        input.children[1].inbox_messages.clear();
        input.children[1].summary.cross_shard_inbox_root =
            recursive_cross_shard_messages_root_v1(&input.children[1].inbox_messages).unwrap();
        input.children[1].descriptor.child_effect_summary_hash =
            recursive_effect_summary_hash_v1(&input.children[1].summary);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "cross-shard message count mismatch"
            ))
        ));
    }

    #[test]
    fn recursive_composition_accepts_opposite_direction_cross_shard_messages() {
        let mut input = valid_input();
        let reverse = routed_message(45, "lane-b", "lane-a");
        input.children[0].inbox_messages.push(reverse.clone());
        input.children[1].outbox_messages.push(reverse.clone());
        refresh_child_effect_hashes(&mut input.children[0]);
        refresh_child_effect_hashes(&mut input.children[1]);

        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let mut canonical_messages = alloc::vec![message(44), reverse];
        canonical_messages.sort_by_key(|row| row.message_id);
        let expected_root = recursive_cross_shard_messages_root_v1(&canonical_messages).unwrap();

        assert_eq!(journal.cross_shard_outbox_root, expected_root);
        assert_eq!(journal.cross_shard_inbox_root, expected_root);
        assert_eq!(
            journal.cross_shard_message_ids_root,
            recursive_cross_shard_message_ids_root_v1(&canonical_messages).unwrap()
        );
    }

    #[test]
    fn recursive_cross_shard_canonicalization_rejects_duplicate_message_ids() {
        let duplicate = message(44);

        assert!(matches!(
            canonical_cross_shard_messages_v1(&[duplicate.clone(), duplicate]),
            Err(TransitionError::InvalidInput(
                "cross-shard message id duplicate"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_canonical_cross_shard_substitution() {
        let mut input = valid_input();
        let reverse = routed_message(45, "lane-b", "lane-a");
        let mut substituted = reverse.clone();
        substituted.amount_atoms += 1;
        substituted.message_id = recursive_cross_shard_message_id_v1(&substituted).unwrap();
        input.children[0].inbox_messages.push(substituted);
        input.children[1].outbox_messages.push(reverse);
        refresh_child_effect_hashes(&mut input.children[0]);
        refresh_child_effect_hashes(&mut input.children[1]);

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "cross-shard message mismatch"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_cross_shard_lane_ownership_mismatch() {
        let mut input = valid_input();
        input.children[0].outbox_messages[0].source_shard_id = "lane-other".to_string();
        input.children[0].outbox_messages[0].message_id =
            recursive_cross_shard_message_id_v1(&input.children[0].outbox_messages[0]).unwrap();
        refresh_child_effect_hashes(&mut input.children[0]);

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "cross-shard outbox source lane mismatch"
            ))
        ));
    }

    #[test]
    fn recursive_lane_state_root_binds_lane_identity() {
        let roots = alloc::vec![("lane-a".to_string(), h(1)), ("lane-b".to_string(), h(2))];
        let relabeled = alloc::vec![("lane-a".to_string(), h(1)), ("lane-c".to_string(), h(2))];
        let domain = b"zenodex.risc0.recursive.post_state_vector_root.v1";

        assert_ne!(
            recursive_lane_state_vector_root_v1(domain, &roots).unwrap(),
            recursive_lane_state_vector_root_v1(domain, &relabeled).unwrap()
        );
    }

    #[test]
    fn recursive_cross_shard_message_id_binds_all_fields() {
        let original = message(44);
        let mut substituted = original.clone();
        substituted.amount_atoms += 1;

        assert_ne!(
            recursive_cross_shard_message_id_v1(&original).unwrap(),
            recursive_cross_shard_message_id_v1(&substituted).unwrap()
        );
        assert!(matches!(
            recursive_cross_shard_messages_root_v1(&[substituted]),
            Err(TransitionError::InvalidInput("message_id mismatch"))
        ));
    }

    #[test]
    fn recursive_identifier_roots_match_admission_parity_fixtures() {
        let mut id4 = [0u8; 32];
        id4[31] = 4;
        let mut id5 = [0u8; 32];
        id5[31] = 5;
        let mut id6 = [0u8; 32];
        id6[31] = 6;
        let mut id7 = [0u8; 32];
        id7[31] = 7;
        let mut id8 = [0u8; 32];
        id8[31] = 8;
        let mut id9 = [0u8; 32];
        id9[31] = 9;

        assert_eq!(
            recursive_child_verification_claims_root_v1(&[id4, id5]).unwrap(),
            [
                0xe0, 0x71, 0xbc, 0x01, 0x4d, 0xcf, 0xb4, 0x4a, 0x78, 0x19, 0xe0, 0xe5, 0x3f, 0x38,
                0xb6, 0xfe, 0x71, 0xc2, 0x25, 0x0f, 0x67, 0x27, 0x3a, 0x16, 0x7a, 0xdd, 0x7e, 0x29,
                0x2a, 0x61, 0x5a, 0x15,
            ]
        );
        assert_eq!(
            recursive_receipt_ids_root_v1(&[id6, id7]).unwrap(),
            [
                0x2c, 0x58, 0x19, 0x62, 0xec, 0xb7, 0xaf, 0xea, 0x60, 0x89, 0x28, 0xad, 0x1b, 0x35,
                0x95, 0x07, 0xca, 0xd3, 0xb5, 0xb9, 0xf6, 0x3c, 0x9e, 0x39, 0x03, 0x67, 0xf5, 0xd8,
                0x3d, 0xe6, 0xfb, 0x52,
            ]
        );
        assert_eq!(
            recursive_message_ids_root_v1(&[id8, id9]).unwrap(),
            [
                0x7a, 0xb1, 0x92, 0xd5, 0x2f, 0x17, 0x3c, 0x9c, 0x4b, 0x88, 0x58, 0x1a, 0xeb, 0xbf,
                0x98, 0xd4, 0x27, 0x2e, 0x45, 0xde, 0x31, 0x9a, 0x48, 0xc4, 0x8c, 0xb2, 0xac, 0x8b,
                0xb2, 0xa4, 0x67, 0x99,
            ]
        );
    }

    #[test]
    fn recursive_cross_shard_message_rejects_invalid_route_and_deadline() {
        let mut same_shard = message(44);
        same_shard.destination_shard_id = same_shard.source_shard_id.clone();
        assert!(matches!(
            recursive_cross_shard_message_id_v1(&same_shard),
            Err(TransitionError::InvalidInput(
                "message source and destination identical"
            ))
        ));

        let mut expired = message(44);
        expired.deadline_epoch = expired.epoch_id - 1;
        assert!(matches!(
            recursive_cross_shard_message_id_v1(&expired),
            Err(TransitionError::InvalidInput(
                "message deadline before source epoch"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_cross_epoch_message() {
        let mut input = valid_input();
        for child_index in 0..2 {
            let rows = if child_index == 0 {
                &mut input.children[child_index].outbox_messages
            } else {
                &mut input.children[child_index].inbox_messages
            };
            rows[0].epoch_id = input.statement.epoch_id + 1;
            rows[0].deadline_epoch = rows[0].epoch_id;
            rows[0].message_id = recursive_cross_shard_message_id_v1(&rows[0]).unwrap();
            refresh_child_effect_hashes(&mut input.children[child_index]);
        }

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput("message epoch_id mismatch"))
        ));
    }

    #[test]
    fn recursive_composition_rejects_authority_root_not_allowed() {
        let mut input = valid_input();
        input.children[0].asset_delta_rows[0].authorized_burn_atoms = 1;
        input.children[0].asset_delta_rows[0].authority_root = recursive_authority_scope_root_v1(
            input.statement.public_policy_hash,
            &input.children[0].summary.lane_kind,
            &input.children[0].asset_delta_rows[0].asset_id,
            RECURSIVE_AUTHORITY_EFFECT_BURN_V1,
        )
        .unwrap();
        input.children[0].summary.asset_delta_root =
            recursive_asset_delta_root_v1(&input.children[0].asset_delta_rows).unwrap();
        input.children[0].descriptor.child_effect_summary_hash =
            recursive_effect_summary_hash_v1(&input.children[0].summary);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "asset authority root not allowed"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_cross_asset_authority_reuse() {
        let wrong_scope = recursive_authority_scope_root_v1(
            h(10),
            "spot",
            "USDC",
            RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
        )
        .unwrap();
        let input = single_child_input_with_rows(alloc::vec![RecursiveAssetDeltaRowV1 {
            asset_id: "zUSD".to_string(),
            debit_atoms: 0,
            credit_atoms: 10,
            authorized_mint_atoms: 10,
            authorized_burn_atoms: 0,
            authority_root: wrong_scope,
        }]);

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "asset authority scope mismatch"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_combined_mint_and_burn_authority() {
        let authority_root = recursive_authority_scope_root_v1(
            h(10),
            "spot",
            "zUSD",
            RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
        )
        .unwrap();
        let input = single_child_input_with_rows(alloc::vec![RecursiveAssetDeltaRowV1 {
            asset_id: "zUSD".to_string(),
            debit_atoms: 1,
            credit_atoms: 1,
            authorized_mint_atoms: 1,
            authorized_burn_atoms: 1,
            authority_root,
        }]);

        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "asset row combines authorized mint and burn"
            ))
        ));
    }

    #[test]
    fn recursive_composition_rejects_pre_state_root_drift() {
        let mut input = valid_input();
        input.statement.expected_pre_state_root = h(77);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "recursive pre_state_root mismatch"
            ))
        ));
    }
}
