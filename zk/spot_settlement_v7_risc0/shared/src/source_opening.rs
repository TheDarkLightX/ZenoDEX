use alloc::string::ToString;
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::{
    execute_state_proof_input_v1, recursive_asset_delta_root_v1,
    recursive_cross_shard_messages_root_v1, recursive_receipt_ids_root_v1,
    spot_recursive_leaf_asset_delta_rows_v1, spot_recursive_leaf_evidence_root_v1,
    spot_recursive_leaf_statement_hash_v1, spot_recursive_leaf_write_set_root_v1,
    validate_recursive_effect_summary_shape_v1, DexSnapshotV1, RecursiveCrossShardMessageV1,
    RecursiveEffectSummaryV1, SpotRecursiveLeafInputV1, StateProofJournalV1,
    RECURSIVE_EFFECT_SUMMARY_VERSION_V1, RECURSIVE_SPOT_LEAF_PROFILE_V1,
    RECURSIVE_SUMMARY_TEXT_MAX_BYTES,
};
use zenodex_zrpf_protocol_v3::{
    decode_exact_full_blob_da_certificate_v1, decode_exact_settlement_admission_journal_v1,
    decode_exact_settlement_effect_plan_v2, CommitmentV3, FullBlobDataAvailabilityCertificateV1,
    ProgramIdV3, SettlementAdmissionJournalV1, SettlementEffectPlanV2,
};
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, program_id_from_risc0_words_v3,
};
use zenodex_zrpf_risc0_spot_settlement_v6_shared::{
    decode_exact_source_opened_spot_settlement_replay_v3,
    source_opened_spot_settlement_replay_schema_id_v3, ProposedSourceOpenedSpotSettlementReplayV3,
};
use zenodex_zrpf_risc0_spot_settlement_v7_effect_binding_shared::{
    bind_spot_settlement_effect_plan_v1, derive_spot_settlement_state_effect_opening_v1,
    BoundSpotSettlementStateV1,
};
use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::ExpectedLegacySpotCommitmentsV1;
use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::{
    compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1,
    decode_exact_bounded_spot_state_root_v7_host_input_v1, BoundedSpotStateRootV7HostInputV1,
    LegacySpotSourceProjectionV7, SpotStateRootV7SemanticJournalV1,
};

use crate::{ProposedSpotSettlementV7EnvelopeV1, SpotSettlementV7ErrorV1};

/// Fully checked proof-neutral source opening after a caller-authenticated V6
/// receipt.
///
/// This object retains the exact pre/post snapshots and internally derived
/// Plan B. It remains proof-neutral because this crate cannot establish that
/// the caller actually verified the V6 receipt.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_settlement_v7_shared::SourceOpenedSpotSettlementV7OpeningV1;
/// let opening: SourceOpenedSpotSettlementV7OpeningV1 = unimplemented!();
/// let _ = opening.settlement_authority();
/// ```
pub struct SourceOpenedSpotSettlementV7OpeningV1 {
    source_child_image_id: [u32; 8],
    source_child_program_id: ProgramIdV3,
    source_child_claim_binding: CommitmentV3,
    source_child_journal_sha256: CommitmentV3,
    source_child_journal: SettlementAdmissionJournalV1,
    data_availability_certificate: FullBlobDataAvailabilityCertificateV1,
    source_replay_sha256: CommitmentV3,
    source_replay: ProposedSourceOpenedSpotSettlementReplayV3,
    source_plan_a: SettlementEffectPlanV2,
    source_input: SpotRecursiveLeafInputV1,
    state_root_host_input_sha256: CommitmentV3,
    state_root_host_input_length: u32,
    state_root_host_input: BoundedSpotStateRootV7HostInputV1,
    state_journal: SpotStateRootV7SemanticJournalV1,
    bound_state: BoundSpotSettlementStateV1,
}

impl SourceOpenedSpotSettlementV7OpeningV1 {
    pub const fn source_child_image_id(&self) -> [u32; 8] {
        self.source_child_image_id
    }

    pub const fn source_child_program_id(&self) -> ProgramIdV3 {
        self.source_child_program_id
    }

    pub const fn source_child_claim_binding(&self) -> CommitmentV3 {
        self.source_child_claim_binding
    }

    pub const fn source_child_journal_sha256(&self) -> CommitmentV3 {
        self.source_child_journal_sha256
    }

    pub const fn source_child_journal(&self) -> &SettlementAdmissionJournalV1 {
        &self.source_child_journal
    }

    pub const fn data_availability_certificate(&self) -> &FullBlobDataAvailabilityCertificateV1 {
        &self.data_availability_certificate
    }

    pub const fn source_replay_sha256(&self) -> CommitmentV3 {
        self.source_replay_sha256
    }

    pub const fn source_replay(&self) -> &ProposedSourceOpenedSpotSettlementReplayV3 {
        &self.source_replay
    }

    pub const fn source_input(&self) -> &SpotRecursiveLeafInputV1 {
        &self.source_input
    }

    pub const fn pre_state(&self) -> &DexSnapshotV1 {
        &self.source_input.spot_input.pre_state
    }

    pub const fn post_state(&self) -> &DexSnapshotV1 {
        self.state_root_host_input.post_state()
    }

    pub const fn state_root_host_input_sha256(&self) -> CommitmentV3 {
        self.state_root_host_input_sha256
    }

    pub const fn state_root_host_input_length(&self) -> u32 {
        self.state_root_host_input_length
    }

    pub const fn state_root_host_input(&self) -> &BoundedSpotStateRootV7HostInputV1 {
        &self.state_root_host_input
    }

    pub const fn state_journal(&self) -> &SpotStateRootV7SemanticJournalV1 {
        &self.state_journal
    }

    pub const fn bound_state(&self) -> &BoundSpotSettlementStateV1 {
        &self.bound_state
    }

    pub const fn source_plan_a(&self) -> &SettlementEffectPlanV2 {
        &self.source_plan_a
    }

    pub const fn plan_b(&self) -> &SettlementEffectPlanV2 {
        self.bound_state.plan()
    }
}

/// Opens and recomposes the exact V7 source relation after V6 receipt verify.
///
/// `verified_child_claim_binding` must be derived by the receipt-bearing caller
/// from the same image and journal passed to `env::verify`. This function
/// recomputes it and rejects mismatch, but does not perform receipt verification.
pub fn open_spot_settlement_v7_after_source_receipt_verification_v1(
    envelope: ProposedSpotSettlementV7EnvelopeV1,
    verified_child_image_id: [u32; 8],
    verified_child_claim_binding: CommitmentV3,
) -> Result<SourceOpenedSpotSettlementV7OpeningV1, SpotSettlementV7ErrorV1> {
    require_verified_child_claim(
        verified_child_image_id,
        envelope.source_child_journal_bytes(),
        verified_child_claim_binding,
    )?;
    let source_child_program_id = program_id_from_risc0_words_v3(verified_child_image_id)
        .map_err(|_| SpotSettlementV7ErrorV1::ZeroVerifiedChildImageId)?;
    let source_child_journal =
        decode_exact_settlement_admission_journal_v1(envelope.source_child_journal_bytes())
            .map_err(|_| SpotSettlementV7ErrorV1::ChildJournalDecode)?;
    let source_child_journal_sha256 = sha256_commitment(
        envelope.source_child_journal_bytes(),
        "source child journal",
    )?;
    let certificate = decode_exact_full_blob_da_certificate_v1(
        envelope.proposed_data_availability_certificate_bytes(),
    )
    .map_err(|_| SpotSettlementV7ErrorV1::DataAvailabilityCertificateDecode)?;
    validate_certificate_scope(&source_child_journal, &certificate)?;
    certificate
        .validate_blob(envelope.proposed_replay_bytes())
        .map_err(|_| SpotSettlementV7ErrorV1::ReplayBlobMismatch)?;
    let replay =
        decode_exact_source_opened_spot_settlement_replay_v3(envelope.proposed_replay_bytes())
            .map_err(|_| SpotSettlementV7ErrorV1::ReplayDecode)?;
    if replay.base().settlement_effect_plan_bytes() != source_child_journal.effect_plan_bytes() {
        return Err(SpotSettlementV7ErrorV1::SourcePlanMismatch);
    }
    let source_plan =
        decode_exact_settlement_effect_plan_v2(replay.base().settlement_effect_plan_bytes())
            .map_err(|_| SpotSettlementV7ErrorV1::SettlementPlanDecode)?;
    let source_input = decode_exact_source_input(replay.source().source_input_bytes())?;
    let source_state_journal = execute_state_proof_input_v1(source_input.spot_input.clone())
        .map_err(|_| SpotSettlementV7ErrorV1::SourceTransitionRejected)?;
    require_exact_source_summary(
        &source_input,
        &source_state_journal,
        replay.source().source_journal_bytes(),
    )?;
    let (sender, ingress_nonce) = singleton_ingress(&source_input)?;
    let state_root_host_input = decode_exact_bounded_spot_state_root_v7_host_input_v1(
        envelope.proposed_state_root_host_input_bytes(),
    )
    .map_err(|_| SpotSettlementV7ErrorV1::HostInputDecode)?;
    let source_projection = LegacySpotSourceProjectionV7::new(
        &source_input.spot_input.pre_state,
        sender,
        ingress_nonce,
        ExpectedLegacySpotCommitmentsV1::new(
            source_state_journal.pre_app_hash,
            source_state_journal.post_app_hash,
            source_state_journal.pre_nonce_root,
            source_state_journal.post_nonce_root,
        ),
    );
    let state_journal =
        compose_spot_state_root_v7_semantic_journal_after_source_receipt_verification_v1(
            &source_projection,
            &state_root_host_input,
        )
        .map_err(|_| SpotSettlementV7ErrorV1::StateJournalComposition)?;
    let effect_opening = derive_spot_settlement_state_effect_opening_v1(
        &state_journal,
        &source_input.spot_input.pre_state,
        state_root_host_input.post_state(),
    )
    .map_err(|_| SpotSettlementV7ErrorV1::EffectBinding)?;
    let bound_state = bind_spot_settlement_effect_plan_v1(effect_opening, &source_plan)
        .map_err(|_| SpotSettlementV7ErrorV1::EffectBinding)?;
    let state_root_host_input_length =
        u32::try_from(envelope.proposed_state_root_host_input_bytes().len())
            .map_err(|_| SpotSettlementV7ErrorV1::LengthOverflow("state-root host input"))?;
    Ok(SourceOpenedSpotSettlementV7OpeningV1 {
        source_child_image_id: verified_child_image_id,
        source_child_program_id,
        source_child_claim_binding: verified_child_claim_binding,
        source_child_journal_sha256,
        source_child_journal,
        data_availability_certificate: certificate,
        source_replay_sha256: sha256_commitment(envelope.proposed_replay_bytes(), "source replay")?,
        source_replay: replay,
        source_plan_a: source_plan,
        source_input,
        state_root_host_input_sha256: sha256_commitment(
            envelope.proposed_state_root_host_input_bytes(),
            "state-root host input",
        )?,
        state_root_host_input_length,
        state_root_host_input,
        state_journal,
        bound_state,
    })
}

fn require_verified_child_claim(
    image_id: [u32; 8],
    journal_bytes: &[u8],
    proposed_claim: CommitmentV3,
) -> Result<(), SpotSettlementV7ErrorV1> {
    if image_id.iter().all(|word| *word == 0) {
        return Err(SpotSettlementV7ErrorV1::ZeroVerifiedChildImageId);
    }
    let expected = derive_risc0_verified_claim_binding_v1(image_id, journal_bytes)
        .map_err(|_| SpotSettlementV7ErrorV1::ChildJournalHash)?;
    if expected != proposed_claim {
        return Err(SpotSettlementV7ErrorV1::ChildClaimBindingMismatch);
    }
    Ok(())
}

fn validate_certificate_scope(
    child: &SettlementAdmissionJournalV1,
    certificate: &FullBlobDataAvailabilityCertificateV1,
) -> Result<(), SpotSettlementV7ErrorV1> {
    if child.data_availability_certificate_root() != certificate.certificate_root() {
        return Err(SpotSettlementV7ErrorV1::DataAvailabilityCertificateRootMismatch);
    }
    if child.application_id() != certificate.application_id()
        || child.chain_or_domain_id() != certificate.chain_or_domain_id()
        || child.epoch_id() != certificate.epoch_id()
    {
        return Err(SpotSettlementV7ErrorV1::DataAvailabilityScopeMismatch);
    }
    if certificate.data_schema_id()
        != source_opened_spot_settlement_replay_schema_id_v3()
            .map_err(|_| SpotSettlementV7ErrorV1::DataAvailabilitySchemaMismatch)?
    {
        return Err(SpotSettlementV7ErrorV1::DataAvailabilitySchemaMismatch);
    }
    if certificate.storage_policy_hash() != child.public_policy_hash() {
        return Err(SpotSettlementV7ErrorV1::DataAvailabilityPolicyMismatch);
    }
    Ok(())
}

fn decode_exact_source_input(
    bytes: &[u8],
) -> Result<SpotRecursiveLeafInputV1, SpotSettlementV7ErrorV1> {
    let (input, remainder) = postcard::take_from_bytes::<SpotRecursiveLeafInputV1>(bytes)
        .map_err(|_| SpotSettlementV7ErrorV1::SourceInputDecode)?;
    if !remainder.is_empty() {
        return Err(SpotSettlementV7ErrorV1::NonCanonicalSourceInput);
    }
    let canonical =
        postcard::to_allocvec(&input).map_err(|_| SpotSettlementV7ErrorV1::SourceInputDecode)?;
    if canonical.as_slice() != bytes {
        return Err(SpotSettlementV7ErrorV1::NonCanonicalSourceInput);
    }
    Ok(input)
}

fn require_exact_source_summary(
    input: &SpotRecursiveLeafInputV1,
    authenticated_transition: &StateProofJournalV1,
    bytes: &[u8],
) -> Result<(), SpotSettlementV7ErrorV1> {
    let (summary, remainder) = postcard::take_from_bytes::<RecursiveEffectSummaryV1>(bytes)
        .map_err(|_| SpotSettlementV7ErrorV1::SourceJournalDecode)?;
    if !remainder.is_empty() {
        return Err(SpotSettlementV7ErrorV1::NonCanonicalSourceJournal);
    }
    let canonical = postcard::to_allocvec(&summary)
        .map_err(|_| SpotSettlementV7ErrorV1::SourceJournalDecode)?;
    if canonical.as_slice() != bytes {
        return Err(SpotSettlementV7ErrorV1::NonCanonicalSourceJournal);
    }
    let recomposed =
        recompose_spot_recursive_leaf_summary_from_transition_v1(input, authenticated_transition)?;
    if recomposed != summary {
        return Err(SpotSettlementV7ErrorV1::SourceJournalMismatch);
    }
    Ok(())
}

/// Derives the exact legacy recursive summary from the one transition result
/// already authenticated by this source-opening invocation.
///
/// Keeping this helper transition-free prevents the V7 guest from executing
/// the same source transition once for summary checking and again for the V7
/// state opening. The transition result is the single authority source for
/// both relations.
fn recompose_spot_recursive_leaf_summary_from_transition_v1(
    input: &SpotRecursiveLeafInputV1,
    journal: &StateProofJournalV1,
) -> Result<RecursiveEffectSummaryV1, SpotSettlementV7ErrorV1> {
    require_source_summary_text(&input.chain_id, "chain ID")?;
    require_source_summary_text(&input.lane_id, "lane ID")?;
    for (value, field) in [
        (&input.public_policy_hash, "public policy"),
        (&input.feature_suite_hash, "feature suite"),
        (&input.dependency_lock_hash, "dependency lock"),
        (&input.toolchain_lock_hash, "toolchain lock"),
    ] {
        if value.iter().all(|byte| *byte == 0) {
            return Err(SpotSettlementV7ErrorV1::SourceProfileRejected(field));
        }
    }
    if input.risc0_image_id.iter().all(|word| *word == 0) {
        return Err(SpotSettlementV7ErrorV1::SourceProfileRejected(
            "source image ID",
        ));
    }
    if !journal.pre_app_hash_present {
        return Err(SpotSettlementV7ErrorV1::SourceProfileRejected(
            "source pre-state root",
        ));
    }
    if journal.state_hash != journal.post_app_hash {
        return Err(SpotSettlementV7ErrorV1::SourceProfileRejected(
            "source post-state root",
        ));
    }

    let asset_delta_rows =
        spot_recursive_leaf_asset_delta_rows_v1(&input.spot_input, input.public_policy_hash)
            .map_err(|_| SpotSettlementV7ErrorV1::SourceTransitionRejected)?;
    let empty_messages = Vec::<RecursiveCrossShardMessageV1>::new();
    let empty_receipt_ids = Vec::<[u8; 32]>::new();
    let summary = RecursiveEffectSummaryV1 {
        summary_version: RECURSIVE_EFFECT_SUMMARY_VERSION_V1,
        lane_id: input.lane_id.clone(),
        lane_kind: "spot".to_string(),
        chain_id: input.chain_id.clone(),
        epoch_id: input.epoch_id,
        proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1.to_string(),
        risc0_image_id: input.risc0_image_id,
        statement_hash: spot_recursive_leaf_statement_hash_v1(
            journal,
            input.public_policy_hash,
            input.feature_suite_hash,
            input.dependency_lock_hash,
            input.toolchain_lock_hash,
        ),
        pre_state_root: journal.pre_app_hash,
        post_state_root: journal.post_app_hash,
        tx_root: journal.txs_commitment,
        evidence_root: spot_recursive_leaf_evidence_root_v1(journal),
        receipt_root: journal.accepted_receipts_root,
        accepted_receipts_root: recursive_receipt_ids_root_v1(&empty_receipt_ids)
            .map_err(|_| SpotSettlementV7ErrorV1::SourceTransitionRejected)?,
        rejected_receipts_root: recursive_receipt_ids_root_v1(&empty_receipt_ids)
            .map_err(|_| SpotSettlementV7ErrorV1::SourceTransitionRejected)?,
        asset_delta_root: recursive_asset_delta_root_v1(&asset_delta_rows)
            .map_err(|_| SpotSettlementV7ErrorV1::SourceTransitionRejected)?,
        cross_shard_outbox_root: recursive_cross_shard_messages_root_v1(&empty_messages)
            .map_err(|_| SpotSettlementV7ErrorV1::SourceTransitionRejected)?,
        cross_shard_inbox_root: recursive_cross_shard_messages_root_v1(&empty_messages)
            .map_err(|_| SpotSettlementV7ErrorV1::SourceTransitionRejected)?,
        write_set_root: spot_recursive_leaf_write_set_root_v1(journal),
        public_policy_hash: input.public_policy_hash,
        feature_suite_hash: input.feature_suite_hash,
        dependency_lock_hash: input.dependency_lock_hash,
        toolchain_lock_hash: input.toolchain_lock_hash,
    };
    validate_recursive_effect_summary_shape_v1(&summary)
        .map_err(|_| SpotSettlementV7ErrorV1::SourceTransitionRejected)?;
    Ok(summary)
}

fn require_source_summary_text(
    value: &str,
    field: &'static str,
) -> Result<(), SpotSettlementV7ErrorV1> {
    if value.is_empty() || value.len() > RECURSIVE_SUMMARY_TEXT_MAX_BYTES {
        return Err(SpotSettlementV7ErrorV1::SourceProfileRejected(field));
    }
    Ok(())
}

fn singleton_ingress(
    input: &SpotRecursiveLeafInputV1,
) -> Result<(&str, u64), SpotSettlementV7ErrorV1> {
    let [transaction] = input.spot_input.txs.as_slice() else {
        return Err(SpotSettlementV7ErrorV1::SourceProfileRejected(
            "exactly one transaction",
        ));
    };
    let [ingress] = input.spot_input.tx_ingress.as_slice() else {
        return Err(SpotSettlementV7ErrorV1::SourceProfileRejected(
            "exactly one ingress fact",
        ));
    };
    if transaction.sender_pubkey != ingress.sender_pubkey {
        return Err(SpotSettlementV7ErrorV1::SourceProfileRejected(
            "sender and ingress",
        ));
    }
    Ok((&transaction.sender_pubkey, ingress.nonce))
}

fn sha256_commitment(
    bytes: &[u8],
    field: &'static str,
) -> Result<CommitmentV3, SpotSettlementV7ErrorV1> {
    CommitmentV3::new(Sha256::digest(bytes).into())
        .map_err(|_| SpotSettlementV7ErrorV1::DerivedCommitment(field))
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use tau_state_proof_risc0_shared::{
        compose_spot_recursive_leaf_summary_v1, compute_pool_id, DexBalanceEntryV1, DexIntentV1,
        DexPoolEntryV1, DexSnapshotV1, DexStateV1, FeeAccumulatorV1, ProtocolFeeConfig,
        SignedIntentV1, StateProofInputV1, SwapExactInIntentV1, TauTxAppOpsV1, TauTxV1,
        TxIngressFactV1, CURVE_PARAMS, CURVE_TAG,
    };

    use super::*;

    #[test]
    fn transition_free_summary_recomposition_matches_legacy_composer() {
        let input = empty_spot_leaf_input();
        let expected = compose_spot_recursive_leaf_summary_v1(input.clone()).unwrap();
        let transition = execute_state_proof_input_v1(input.spot_input.clone()).unwrap();
        let actual =
            recompose_spot_recursive_leaf_summary_from_transition_v1(&input, &transition).unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn transition_free_summary_recomposition_matches_accepted_single_swap() {
        let input = single_swap_spot_leaf_input();
        let expected = compose_spot_recursive_leaf_summary_v1(input.clone()).unwrap();
        let transition = execute_state_proof_input_v1(input.spot_input.clone()).unwrap();
        let actual =
            recompose_spot_recursive_leaf_summary_from_transition_v1(&input, &transition).unwrap();
        assert_eq!(actual, expected);
        assert_eq!(singleton_ingress(&input).unwrap(), ("sender-a", 0));
    }

    fn empty_spot_leaf_input() -> SpotRecursiveLeafInputV1 {
        let snapshot = DexStateV1::empty().to_snapshot();
        let app_hash = DexStateV1::from_snapshot(snapshot.clone())
            .unwrap()
            .canonical_app_hash_sha256();
        SpotRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "spot-lane-a".to_string(),
            risc0_image_id: [41; 8],
            public_policy_hash: [10; 32],
            feature_suite_hash: [11; 32],
            dependency_lock_hash: [12; 32],
            toolchain_lock_hash: [13; 32],
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

    fn single_swap_spot_leaf_input() -> SpotRecursiveLeafInputV1 {
        let pool_id = compute_pool_id("asset-a", "asset-b", 30, CURVE_TAG, CURVE_PARAMS);
        let snapshot = DexSnapshotV1 {
            version: 1,
            balances: vec![DexBalanceEntryV1 {
                pubkey: "sender-a".to_string(),
                asset: "asset-a".to_string(),
                amount: 1_000,
            }],
            pools: vec![DexPoolEntryV1 {
                pool_id: pool_id.clone(),
                asset0: "asset-a".to_string(),
                asset1: "asset-b".to_string(),
                reserve0: 10_000,
                reserve1: 10_000,
                fee_bps: 30,
                lp_supply: 10_000,
                status: "ACTIVE".to_string(),
                created_at: 0,
            }],
            lp_balances: Vec::new(),
            fee_accumulator: FeeAccumulatorV1 { dust: 0 },
            vault: None,
            oracle: None,
        };
        let pre_hash = DexStateV1::from_snapshot(snapshot.clone())
            .unwrap()
            .canonical_app_hash_sha256();
        let transaction = TauTxV1 {
            sender_pubkey: "sender-a".to_string(),
            app_ops: TauTxAppOpsV1 {
                has_faucet: false,
                faucet_mint: Vec::new(),
                has_intents: true,
                intents: vec![SignedIntentV1 {
                    signature: None,
                    intent: DexIntentV1::SwapExactIn(SwapExactInIntentV1 {
                        module: "TauSwap".to_string(),
                        version: "v1".to_string(),
                        intent_id: "settlement-v7-parity-swap".to_string(),
                        sender_pubkey: "sender-a".to_string(),
                        deadline: 100,
                        pool_id,
                        asset_in: "asset-a".to_string(),
                        asset_out: "asset-b".to_string(),
                        amount_in: 1_000,
                        min_amount_out: 900,
                        recipient: "recipient-b".to_string(),
                        salt: None,
                    }),
                }],
            },
        };
        let mut post_state = DexStateV1::from_snapshot(snapshot.clone()).unwrap();
        post_state
            .apply_tx(&transaction, 1, &ProtocolFeeConfig::default())
            .unwrap();
        let post_hash = post_state.canonical_app_hash_sha256();
        SpotRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "spot-lane-a".to_string(),
            risc0_image_id: [41; 8],
            public_policy_hash: [10; 32],
            feature_suite_hash: [11; 32],
            dependency_lock_hash: [12; 32],
            toolchain_lock_hash: [13; 32],
            spot_input: StateProofInputV1 {
                state_hash: post_hash,
                block_timestamp: 1,
                pre_app_hash_present: true,
                pre_app_hash: pre_hash,
                pre_state: snapshot,
                txs: vec![transaction],
                pre_nonces: Vec::new(),
                tx_ingress: vec![TxIngressFactV1 {
                    sender_pubkey: "sender-a".to_string(),
                    nonce: 0,
                }],
                chain_balances_post: Vec::new(),
                expected_post_app_hash: post_hash,
                protocol_fee_share_bps: 0,
                protocol_fee_recipient_pubkey: None,
                tx_execution_order: vec![0],
                route_price_intervals: Vec::new(),
                route_price_interval_authority: None,
                route_price_interval_authority_policy: None,
                route_price_interval_max_width_bps: None,
                shared_pool_frontier_signature_certificates: Vec::new(),
            },
        }
    }
}
