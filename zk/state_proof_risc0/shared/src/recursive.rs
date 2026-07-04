extern crate alloc;

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::TransitionError;

pub const PROOF_TYPE_RECURSIVE: &str = "risc0.zenodex_recursive_epoch.v1";
pub const RECURSIVE_EFFECT_SUMMARY_VERSION_V1: u32 = 1;
pub const RECURSIVE_STATEMENT_VERSION_V1: u32 = 1;
pub const RECURSIVE_JOURNAL_VERSION_V1: u32 = 1;
pub const RECURSIVE_STRICT_CROSS_SHARD_MODE_V1: &str = "strict";
pub const RECURSIVE_DOMAIN_SEPARATOR_V1: &str = "zenodex.risc0.recursive_epoch.v1";

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
    pub max_cross_shard_messages: u32,
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
    let mut pre_roots = Vec::new();
    let mut post_roots = Vec::new();
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
        pre_roots.push(child.summary.pre_state_root);
        post_roots.push(child.summary.post_state_root);
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

    let canonical_delta_rows =
        canonical_asset_delta_rows_v1(&aggregate_delta_rows, &allowed_authorities)?;
    validate_asset_conservation_v1(&canonical_delta_rows)?;
    validate_receipt_partition_v1(&all_accepted_receipts, &all_rejected_receipts)?;
    validate_cross_shard_strict_cancellation_v1(&all_outbox, &all_inbox)?;

    let pre_state_root = recursive_root_list_root_v1(
        b"zenodex.risc0.recursive.pre_state_vector_root.v1",
        &pre_roots,
    )?;
    let post_state_root = recursive_root_list_root_v1(
        b"zenodex.risc0.recursive.post_state_vector_root.v1",
        &post_roots,
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
        child_verification_claims_root: recursive_root_list_root_v1(
            b"zenodex.risc0.recursive.child_verification_claims_root.v1",
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
        cross_shard_outbox_root: recursive_cross_shard_messages_root_v1(&all_outbox)?,
        cross_shard_inbox_root: recursive_cross_shard_messages_root_v1(&all_inbox)?,
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

pub fn recursive_verifier_set_root_v1(ids: &[[u8; 32]]) -> Result<[u8; 32], TransitionError> {
    validate_sorted_unique_roots_v1(ids, "verifier id")?;
    recursive_root_list_root_v1(b"zenodex.risc0.recursive.verifier_set_root.v1", ids)
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
    require_nonempty(&statement.proof_profile, "recursive proof_profile empty")?;
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
    if !allowed_verifiers.contains(&child.descriptor.child_verifier_id) {
        return Err(TransitionError::InvalidInput(
            "child verifier id not allowed",
        ));
    }
    require_nonempty(&child.descriptor.child_profile, "child profile empty")?;
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
    if summary.proof_profile != statement.proof_profile {
        return Err(TransitionError::InvalidInput("child profile mismatch"));
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
            .checked_add(row.authorized_burn_atoms)
            .ok_or(TransitionError::Arithmetic("asset debit total overflow"))?;
        let credit_side = row
            .credit_atoms
            .checked_add(row.authorized_mint_atoms)
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
) -> Result<(), TransitionError> {
    validate_sorted_unique_messages_v1(outbox)?;
    validate_sorted_unique_messages_v1(inbox)?;
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
        require_nonempty(&row.source_shard_id, "message source_shard_id empty")?;
        require_nonempty(
            &row.destination_shard_id,
            "message destination_shard_id empty",
        )?;
        require_nonempty(&row.asset_id, "message asset_id empty")?;
        require_nonzero_root(&row.sender_scope_hash, "message sender_scope_hash zero")?;
        require_nonzero_root(
            &row.recipient_scope_hash,
            "message recipient_scope_hash zero",
        )?;
        require_nonzero_root(&row.source_receipt_hash, "message source_receipt_hash zero")?;
        if row.amount_atoms == 0 {
            return Err(TransitionError::InvalidInput("message amount zero"));
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
    use alloc::string::ToString;

    fn h(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    fn image(byte: u32) -> [u32; 8] {
        [byte; 8]
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

    fn message(byte: u8) -> RecursiveCrossShardMessageV1 {
        RecursiveCrossShardMessageV1 {
            message_id: h(byte),
            epoch_id: 7,
            source_shard_id: "shard-a".to_string(),
            destination_shard_id: "shard-b".to_string(),
            asset_id: "ASSET0".to_string(),
            amount_atoms: 5,
            sender_scope_hash: h(91),
            recipient_scope_hash: h(92),
            source_receipt_hash: h(93),
            deadline_epoch: 9,
        }
    }

    fn child(
        lane: &str,
        receipt_byte: u8,
        journal_byte: u8,
        verifier_id: [u8; 32],
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
        RecursiveChildEffectV1 {
            descriptor: RecursiveChildDescriptorV1 {
                child_verification_claim_hash,
                child_journal_hash,
                child_effect_summary_hash: summary_hash,
                child_statement_hash: summary.statement_hash,
                child_image_id: summary.risc0_image_id,
                child_verifier_id: verifier_id,
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
        let verifier_ids = alloc::vec![h(4), h(5)];
        let authority_roots = alloc::vec![h(6)];
        let left = child(
            "lane-a",
            21,
            31,
            h(4),
            alloc::vec![asset_row("ASSET0", 10, 0), asset_row("ASSET1", 0, 5)],
            alloc::vec![message(44)],
            Vec::new(),
            alloc::vec![h(81)],
        );
        let right = child(
            "lane-b",
            22,
            32,
            h(5),
            alloc::vec![asset_row("ASSET0", 0, 10), asset_row("ASSET1", 5, 0)],
            Vec::new(),
            alloc::vec![message(44)],
            alloc::vec![h(82)],
        );
        let pre_state_root = recursive_root_list_root_v1(
            b"zenodex.risc0.recursive.pre_state_vector_root.v1",
            &[left.summary.pre_state_root, right.summary.pre_state_root],
        )
        .unwrap();
        let post_state_root = recursive_root_list_root_v1(
            b"zenodex.risc0.recursive.post_state_vector_root.v1",
            &[left.summary.post_state_root, right.summary.post_state_root],
        )
        .unwrap();
        RecursiveCompositionInputV1 {
            statement: RecursiveCompositionStatementV1 {
                domain_separator: RECURSIVE_DOMAIN_SEPARATOR_V1.to_string(),
                schema_version: RECURSIVE_STATEMENT_VERSION_V1,
                chain_id: "tau-test".to_string(),
                epoch_id: 7,
                proof_profile: "recursive_block_v1".to_string(),
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

    #[test]
    fn recursive_composition_accepts_balanced_strict_children() {
        let input = valid_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        assert_eq!(journal.child_count, 2);
        assert_eq!(journal.proof_type, PROOF_TYPE_RECURSIVE);
        assert_eq!(journal.chain_id, "tau-test");
        assert_eq!(journal.proof_profile, "recursive_block_v1");
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
    fn recursive_composition_rejects_stale_verifier_id() {
        let mut input = valid_input();
        input.children[0].descriptor.child_verifier_id = h(99);
        assert!(matches!(
            compose_recursive_epoch_journal_v1(&input),
            Err(TransitionError::InvalidInput(
                "child verifier id not allowed"
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
    fn recursive_composition_rejects_authority_root_not_allowed() {
        let mut input = valid_input();
        input.children[0].asset_delta_rows[0].authorized_burn_atoms = 1;
        input.children[0].asset_delta_rows[0].authority_root = h(99);
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
