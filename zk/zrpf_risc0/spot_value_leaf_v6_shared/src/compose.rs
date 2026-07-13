use alloc::vec;
use alloc::vec::Vec;

use tau_state_proof_risc0_shared::{
    compose_spot_recursive_leaf_summary_v1, recursive_asset_delta_root_v1,
    tx_execution_order_commitment_v1, txs_commitment_v1, DexIntentV1, DexPoolEntryV1, DexStateV1,
    ProtocolFeeConfig, RecursiveAssetDeltaRowV1, RecursiveEffectSummaryV1,
    SpotRecursiveLeafInputV1, SwapExactInIntentV1, TauTxV1,
};
use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v3, AuthorizationGrantIdV1, AuthorizationScopeIdV1,
    AuthorizationSubjectIdV1, CommitmentV3, ExpectedV1AdapterLeafIdentityV1,
    ProposedSemanticLeafV1, SemanticAssetFlowInputV2, SemanticAssetFlowV2, SemanticSubtreeInputV2,
    SemanticSubtreeV2, SemanticValueLeafRecordInputV2, SemanticValueLeafRecordV2,
    V1AdapterSemanticLeafOpeningV1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    spot_accounting_domain_id_v1, spot_atoms_unit_id_v1, spot_lane_id_hash_v1,
    spot_represented_value_profile_id_v1, spot_state_root_scheme_id_v1,
    SpotRepresentedValuePolicyV1,
};
use zenodex_zrpf_risc0_shared::{
    program_id_from_risc0_words_v3, project_policy_bound_v1_journal, source_policy_v1, SourceKindV1,
};

use crate::statement::{
    hash_framed, semantic_leaf_hash_v6, singleton_schedule_commitment_v6,
    SourceOpenedSpotValueLeafStatementInputV6,
};
use crate::{
    SourceOpenedSpotValueLeafEnvelopeV6, SourceOpenedSpotValueLeafErrorV6,
    SourceOpenedSpotValueLeafStatementV6, PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
};

const CANONICAL_TX_DOMAIN_V6: &[u8] = b"zenodex.zrpf.ordinary_spot_canonical_tx.v6";
const ACTION_NULLIFIER_DOMAIN_V6: &[u8] = b"zenodex.zrpf.ordinary_spot_action_nullifier.v6";
const DA_PAYLOAD_DOMAIN_V6: &[u8] = b"zenodex.zrpf.source_opened_spot_da_payload.v6";
const AUTHORIZATION_SUBJECT_DOMAIN_V6: &[u8] =
    b"zenodex.zrpf.source_opened_spot.authorization_subject.v6";
const AUTHORIZATION_SCOPE_DOMAIN_V6: &[u8] =
    b"zenodex.zrpf.source_opened_spot.authorization_scope.v6";
const AUTHORIZATION_GRANT_DOMAIN_V6: &[u8] =
    b"zenodex.zrpf.source_opened_spot.source_receipt_grant.v6";

struct CheckedSourceOpeningV6 {
    source_input: SpotRecursiveLeafInputV1,
    source_summary: RecursiveEffectSummaryV1,
    transaction: TauTxV1,
    intent: SwapExactInIntentV1,
    ingress_nonce: u64,
}

struct CheckedSwapEffectsV6 {
    flows: Vec<SemanticAssetFlowV2>,
    ordinary_flow_row_root: CommitmentV3,
}

struct SourceBoundAuthorizationV6 {
    subject_id: AuthorizationSubjectIdV1,
    scope_id: AuthorizationScopeIdV1,
    nonce: u64,
    grant_id: AuthorizationGrantIdV1,
}

/// Recompose the exact V6 statement after an enclosing guest authenticates the
/// adapter journal bytes under [`PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID`].
///
/// This function performs no receipt verification. Its result remains a
/// proof-neutral expected statement until a receipt-bearing caller satisfies
/// that precondition and an outer verifier authenticates the V6 receipt.
pub fn recompose_source_opened_spot_value_leaf_statement_v6(
    envelope: &SourceOpenedSpotValueLeafEnvelopeV6,
) -> Result<SourceOpenedSpotValueLeafStatementV6, SourceOpenedSpotValueLeafErrorV6> {
    let checked = check_source_opening(envelope)?;
    let projection = project_policy_bound_v1_journal(
        SourceKindV1::Spot,
        envelope.source_journal_bytes(),
        envelope.assigned_leaf_ordinal(),
        PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
    )
    .map_err(|_| SourceOpenedSpotValueLeafErrorV6::AdapterProjectionRejected)?;
    require_exact_adapter_journal(envelope.adapter_journal_bytes(), &projection.journal)?;

    let canonical_tx_commitment = canonical_tx_commitment_v6(
        &checked.source_input.chain_id,
        &checked.transaction,
        &checked.intent,
        checked.ingress_nonce,
    )?;
    let action_nullifier = action_nullifier_v6(
        &projection.journal,
        &checked.transaction,
        &checked.intent,
        checked.ingress_nonce,
        canonical_tx_commitment,
    )?;
    let execution_order = CommitmentV3::new(
        tx_execution_order_commitment_v1(&[0])
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SwapReexecutionRejected)?,
    )
    .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("execution order"))?;
    let schedule = singleton_schedule_commitment_v6(
        execution_order,
        canonical_tx_commitment,
        action_nullifier,
    )?;
    let effects = derive_checked_swap_effects(
        &checked.source_input,
        &checked.source_summary,
        &checked.intent,
    )?;
    let authorization = derive_source_bound_authorization_v6(
        &projection.journal,
        &checked.transaction.sender_pubkey,
        checked.ingress_nonce,
        canonical_tx_commitment,
    )?;
    let semantic_subtree = derive_semantic_subtree(
        &projection,
        &checked,
        &effects,
        canonical_tx_commitment,
        action_nullifier,
        schedule,
    )?;
    let da_payload = data_availability_payload_commitment_v6(envelope)?;
    SourceOpenedSpotValueLeafStatementV6::derive(SourceOpenedSpotValueLeafStatementInputV6 {
        structural_adapter_journal: projection.journal,
        semantic_subtree,
        source_transaction_commitment: commitment(checked.source_summary.tx_root)?,
        canonical_tx_commitment,
        source_execution_order_commitment: execution_order,
        singleton_schedule_commitment: schedule,
        data_availability_payload_commitment: da_payload,
        authorization_subject_id: authorization.subject_id,
        authorization_scope_id: authorization.scope_id,
        authorization_nonce: authorization.nonce,
        authorization_grant_id: authorization.grant_id,
    })
}

fn derive_source_bound_authorization_v6(
    adapter: &zenodex_zrpf_protocol_v3::NodeJournalV3,
    sender: &str,
    nonce: u64,
    canonical_tx_commitment: CommitmentV3,
) -> Result<SourceBoundAuthorizationV6, SourceOpenedSpotValueLeafErrorV6> {
    let subject = hash_framed(AUTHORIZATION_SUBJECT_DOMAIN_V6, &[sender.as_bytes()])?;
    let scope = hash_framed(
        AUTHORIZATION_SCOPE_DOMAIN_V6,
        &[
            adapter.scope().application_id().as_bytes(),
            adapter.scope().chain_or_domain_id().as_bytes(),
            adapter.scope().public_policy_hash().as_bytes(),
        ],
    )?;
    let adapter_hash = adapter
        .canonical_hash()
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("authorization"))?;
    let grant = hash_framed(
        AUTHORIZATION_GRANT_DOMAIN_V6,
        &[
            adapter_hash.as_bytes(),
            subject.as_bytes(),
            scope.as_bytes(),
            &nonce.to_be_bytes(),
            canonical_tx_commitment.as_bytes(),
        ],
    )?;
    Ok(SourceBoundAuthorizationV6 {
        subject_id: AuthorizationSubjectIdV1::new(subject.into_bytes())
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("subject"))?,
        scope_id: AuthorizationScopeIdV1::new(scope.into_bytes())
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("scope"))?,
        nonce,
        grant_id: AuthorizationGrantIdV1::new(grant.into_bytes())
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("grant"))?,
    })
}

fn check_source_opening(
    envelope: &SourceOpenedSpotValueLeafEnvelopeV6,
) -> Result<CheckedSourceOpeningV6, SourceOpenedSpotValueLeafErrorV6> {
    let source_input = decode_exact_source_input(envelope.source_input_bytes())?;
    let source_summary = decode_exact_source_summary(envelope.source_journal_bytes())?;
    require_source_profile(&source_input, &source_summary)?;
    let recomposed = compose_spot_recursive_leaf_summary_v1(source_input.clone())
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SourceTransitionRejected)?;
    if recomposed != source_summary {
        return Err(SourceOpenedSpotValueLeafErrorV6::SourceJournalMismatch);
    }
    let (transaction, intent, ingress_nonce) = require_singleton_swap(&source_input)?;
    if txs_commitment_v1(core::slice::from_ref(&transaction)) != source_summary.tx_root {
        return Err(SourceOpenedSpotValueLeafErrorV6::SourceProfileRejected(
            "source transaction commitment",
        ));
    }
    Ok(CheckedSourceOpeningV6 {
        source_input,
        source_summary,
        transaction,
        intent,
        ingress_nonce,
    })
}

fn decode_exact_source_input(
    bytes: &[u8],
) -> Result<SpotRecursiveLeafInputV1, SourceOpenedSpotValueLeafErrorV6> {
    let (input, remainder) = postcard::take_from_bytes::<SpotRecursiveLeafInputV1>(bytes)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SourceInputDecode)?;
    if !remainder.is_empty() {
        return Err(SourceOpenedSpotValueLeafErrorV6::NonCanonicalSourceInput);
    }
    let canonical = postcard::to_allocvec(&input)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SourceInputDecode)?;
    if canonical.as_slice() != bytes {
        return Err(SourceOpenedSpotValueLeafErrorV6::NonCanonicalSourceInput);
    }
    Ok(input)
}

fn decode_exact_source_summary(
    bytes: &[u8],
) -> Result<RecursiveEffectSummaryV1, SourceOpenedSpotValueLeafErrorV6> {
    let (summary, remainder) = postcard::take_from_bytes::<RecursiveEffectSummaryV1>(bytes)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SourceJournalDecode)?;
    if !remainder.is_empty() {
        return Err(SourceOpenedSpotValueLeafErrorV6::NonCanonicalSourceJournal);
    }
    let canonical = postcard::to_allocvec(&summary)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SourceJournalDecode)?;
    if canonical.as_slice() != bytes {
        return Err(SourceOpenedSpotValueLeafErrorV6::NonCanonicalSourceJournal);
    }
    Ok(summary)
}

fn require_source_profile(
    input: &SpotRecursiveLeafInputV1,
    summary: &RecursiveEffectSummaryV1,
) -> Result<(), SourceOpenedSpotValueLeafErrorV6> {
    let policy = source_policy_v1(SourceKindV1::Spot);
    for (field, matches) in [
        ("input image", input.risc0_image_id == policy.image_id),
        ("summary image", summary.risc0_image_id == policy.image_id),
        (
            "summary proof profile",
            summary.proof_profile == policy.proof_profile,
        ),
        ("summary lane kind", summary.lane_kind == policy.lane_kind),
        ("chain", input.chain_id == summary.chain_id),
        ("lane", input.lane_id == summary.lane_id),
        ("epoch", input.epoch_id == summary.epoch_id),
        (
            "public policy",
            input.public_policy_hash == summary.public_policy_hash,
        ),
        (
            "feature suite",
            input.feature_suite_hash == summary.feature_suite_hash,
        ),
        (
            "dependency lock",
            input.dependency_lock_hash == summary.dependency_lock_hash,
        ),
        (
            "toolchain lock",
            input.toolchain_lock_hash == summary.toolchain_lock_hash,
        ),
    ] {
        if !matches {
            return Err(SourceOpenedSpotValueLeafErrorV6::SourceProfileRejected(
                field,
            ));
        }
    }
    Ok(())
}

fn require_singleton_swap(
    input: &SpotRecursiveLeafInputV1,
) -> Result<(TauTxV1, SwapExactInIntentV1, u64), SourceOpenedSpotValueLeafErrorV6> {
    let spot = &input.spot_input;
    if !spot.pre_app_hash_present {
        return profile_reject("pre app hash");
    }
    if spot.txs.len() != 1 || spot.tx_ingress.len() != 1 || spot.tx_execution_order != [0] {
        return profile_reject("singleton execution");
    }
    if !spot.chain_balances_post.is_empty()
        || spot.protocol_fee_share_bps != 0
        || spot.protocol_fee_recipient_pubkey.is_some()
    {
        return profile_reject("external or protocol fee effects");
    }
    if !spot.route_price_intervals.is_empty()
        || spot.route_price_interval_authority.is_some()
        || spot.route_price_interval_authority_policy.is_some()
        || spot.route_price_interval_max_width_bps.is_some()
        || !spot.shared_pool_frontier_signature_certificates.is_empty()
    {
        return profile_reject("route or frontier evidence");
    }
    let transaction = spot.txs[0].clone();
    let ingress = &spot.tx_ingress[0];
    require_canonical_singleton_nonce(&spot.pre_nonces, &transaction.sender_pubkey, ingress.nonce)?;
    if transaction.sender_pubkey != ingress.sender_pubkey
        || transaction.app_ops.has_faucet
        || !transaction.app_ops.faucet_mint.is_empty()
        || !transaction.app_ops.has_intents
        || transaction.app_ops.intents.len() != 1
    {
        return profile_reject("transaction envelope");
    }
    let signed = &transaction.app_ops.intents[0];
    if signed.signature.is_some() {
        return profile_reject("signature mode");
    }
    let DexIntentV1::SwapExactIn(intent) = &signed.intent else {
        return profile_reject("intent kind");
    };
    let intent = intent.clone();
    if intent.module != "TauSwap"
        || intent.version != "v1"
        || intent.salt.is_some()
        || intent.sender_pubkey != transaction.sender_pubkey
        || intent.deadline < spot.block_timestamp
    {
        return profile_reject("intent envelope");
    }
    Ok((transaction, intent, ingress.nonce))
}

fn require_canonical_singleton_nonce(
    pre_nonces: &[tau_state_proof_risc0_shared::NonceEntryV1],
    sender: &str,
    ingress_nonce: u64,
) -> Result<(), SourceOpenedSpotValueLeafErrorV6> {
    if ingress_nonce == 0 {
        if pre_nonces.is_empty() {
            return Ok(());
        }
        return profile_reject("canonical initial nonce");
    }
    if pre_nonces.len() == 1
        && pre_nonces[0].pubkey == sender
        && pre_nonces[0].next_nonce == ingress_nonce
    {
        return Ok(());
    }
    profile_reject("canonical existing nonce")
}

fn derive_checked_swap_effects(
    source_input: &SpotRecursiveLeafInputV1,
    source_summary: &RecursiveEffectSummaryV1,
    intent: &SwapExactInIntentV1,
) -> Result<CheckedSwapEffectsV6, SourceOpenedSpotValueLeafErrorV6> {
    let pre_pool = unique_pool(&source_input.spot_input.pre_state.pools, &intent.pool_id)?;
    let mut state = DexStateV1::from_snapshot(source_input.spot_input.pre_state.clone())
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SwapReexecutionRejected)?;
    let recomputed_pre = state.canonical_app_hash_sha256();
    if recomputed_pre != source_input.spot_input.pre_app_hash
        || recomputed_pre != source_summary.pre_state_root
    {
        return Err(SourceOpenedSpotValueLeafErrorV6::SwapReexecutionRejected);
    }
    state
        .apply_tx(
            &source_input.spot_input.txs[0],
            source_input.spot_input.block_timestamp,
            &ProtocolFeeConfig::default(),
        )
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SwapReexecutionRejected)?;
    let recomputed_post = state.canonical_app_hash_sha256();
    if recomputed_post != source_input.spot_input.expected_post_app_hash
        || recomputed_post != source_summary.post_state_root
    {
        return Err(SourceOpenedSpotValueLeafErrorV6::SwapReexecutionRejected);
    }
    let post = state.to_snapshot();
    let post_pool = unique_pool(&post.pools, &intent.pool_id)?;
    let amount_out = require_reserve_deltas(pre_pool, post_pool, intent)?;
    let mut rows = vec![
        ordinary_row(&intent.asset_in, intent.amount_in),
        ordinary_row(&intent.asset_out, amount_out),
    ];
    rows.sort_by(|left, right| left.asset_id.cmp(&right.asset_id));
    if rows[0].asset_id == rows[1].asset_id {
        return Err(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
            "identical assets",
        ));
    }
    let flows = rows
        .iter()
        .map(|row| {
            SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
                asset_id: decode_asset_id(&row.asset_id)?,
                outflow_atoms: row.debit_atoms,
                inflow_atoms: row.credit_atoms,
                issued_atoms: 0,
                destroyed_atoms: 0,
            })
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected("semantic flow"))
        })
        .collect::<Result<Vec<_>, SourceOpenedSpotValueLeafErrorV6>>()?;
    // This root represents gross ordinary swap flow rows. The source
    // summary's asset_delta_root has a different contract: authorized
    // issuance, destruction, and external native-asset movement. For this
    // profile the source root is empty while the balanced ordinary-flow rows
    // are nonempty, so equality would conflate two accounting domains.
    let ordinary_flow_row_root = CommitmentV3::new(
        recursive_asset_delta_root_v1(&rows)
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected("asset root"))?,
    )
    .map_err(|_| SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected("asset root"))?;
    Ok(CheckedSwapEffectsV6 {
        flows,
        ordinary_flow_row_root,
    })
}

fn unique_pool<'a>(
    pools: &'a [DexPoolEntryV1],
    pool_id: &str,
) -> Result<&'a DexPoolEntryV1, SourceOpenedSpotValueLeafErrorV6> {
    let mut matches = pools.iter().filter(|pool| pool.pool_id == pool_id);
    let pool = matches
        .next()
        .ok_or(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
            "pool missing",
        ))?;
    if matches.next().is_some() {
        return Err(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
            "duplicate pool",
        ));
    }
    Ok(pool)
}

fn require_reserve_deltas(
    pre: &DexPoolEntryV1,
    post: &DexPoolEntryV1,
    intent: &SwapExactInIntentV1,
) -> Result<u128, SourceOpenedSpotValueLeafErrorV6> {
    let (pre_in, post_in, pre_out, post_out) =
        if intent.asset_in == pre.asset0 && intent.asset_out == pre.asset1 {
            (pre.reserve0, post.reserve0, pre.reserve1, post.reserve1)
        } else if intent.asset_in == pre.asset1 && intent.asset_out == pre.asset0 {
            (pre.reserve1, post.reserve1, pre.reserve0, post.reserve0)
        } else {
            return Err(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
                "pool asset pair",
            ));
        };
    let amount_in =
        post_in
            .checked_sub(pre_in)
            .ok_or(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
                "input reserve direction",
            ))?;
    let amount_out =
        pre_out
            .checked_sub(post_out)
            .ok_or(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
                "output reserve direction",
            ))?;
    if amount_in != intent.amount_in || amount_out == 0 || amount_out < intent.min_amount_out {
        return Err(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
            "reserve amount",
        ));
    }
    Ok(amount_out)
}

fn ordinary_row(asset_id: &str, atoms: u128) -> RecursiveAssetDeltaRowV1 {
    RecursiveAssetDeltaRowV1 {
        asset_id: asset_id.into(),
        debit_atoms: atoms,
        credit_atoms: atoms,
        authorized_mint_atoms: 0,
        authorized_burn_atoms: 0,
        authority_root: [0; 32],
    }
}

fn derive_semantic_subtree(
    projection: &zenodex_zrpf_risc0_shared::V1LeafProjectionV3,
    checked: &CheckedSourceOpeningV6,
    effects: &CheckedSwapEffectsV6,
    canonical_tx_commitment: CommitmentV3,
    action_nullifier: CommitmentV3,
    schedule: CommitmentV3,
) -> Result<SemanticSubtreeV2, SourceOpenedSpotValueLeafErrorV6> {
    let source_binding_hash = projection
        .source_binding
        .canonical_hash()
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::AdapterProjectionRejected)?;
    let adapter_program = program_id_from_risc0_words_v3(PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::AdapterProjectionRejected)?;
    let expected_adapter = ExpectedV1AdapterLeafIdentityV1::new(adapter_program)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::AdapterProjectionRejected)?;
    let semantic_leaf = ProposedSemanticLeafV1::bind_v1_adapter_journal(
        &projection.journal,
        V1AdapterSemanticLeafOpeningV1::new(source_binding_hash),
        &expected_adapter,
    )
    .map_err(|_| SourceOpenedSpotValueLeafErrorV6::AdapterProjectionRejected)?;
    let asset_delta_root = effects.ordinary_flow_row_root;
    let adapter_hash = projection
        .journal
        .canonical_hash()
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::AdapterJournalDecode)?;
    let semantic_leaf_hash = semantic_leaf_hash_v6(
        adapter_hash,
        commitment(checked.source_summary.tx_root)?,
        canonical_tx_commitment,
        action_nullifier,
        asset_delta_root,
        schedule,
    )?;
    let commitments = projection.journal.commitments().to_input();
    let record = SemanticValueLeafRecordV2::new(SemanticValueLeafRecordInputV2 {
        partition: projection.journal.partition(),
        semantic_leaf_hash,
        source_claim_id: semantic_leaf.source_claim_id().into_commitment(),
        semantic_source_id: semantic_leaf.semantic_source_id().into_commitment(),
        task_id: semantic_leaf.task_id(),
        pre_state_vector_root: commitments.pre_state_vector_root,
        post_state_vector_root: commitments.post_state_vector_root,
        transaction_root: action_nullifier,
        effect_root: commitments.effect_root,
        asset_delta_root,
        raw_pre_state_root: commitment(checked.source_summary.pre_state_root)?,
        raw_post_state_root: commitment(checked.source_summary.post_state_root)?,
    })
    .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("leaf record"))?;
    let policy =
        SpotRepresentedValuePolicyV1::new(checked.source_summary.public_policy_hash, Vec::new())
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("empty grants"))?;
    SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: spot_represented_value_profile_id_v1()
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("value profile"))?,
        accounting_domain_id: spot_accounting_domain_id_v1().map_err(|_| {
            SourceOpenedSpotValueLeafErrorV6::StatementDerivation("accounting domain")
        })?,
        atoms_unit_id: spot_atoms_unit_id_v1()
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("atoms unit"))?,
        state_root_scheme_id: spot_state_root_scheme_id_v1().map_err(|_| {
            SourceOpenedSpotValueLeafErrorV6::StatementDerivation("state root scheme")
        })?,
        scope_hash: projection
            .journal
            .scope()
            .canonical_hash()
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("scope"))?,
        lane_id_hash: spot_lane_id_hash_v1(&checked.source_summary.lane_id)
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("lane"))?,
        partition: projection.journal.partition(),
        raw_subtree_pre_state_root: commitment(checked.source_summary.pre_state_root)?,
        raw_subtree_post_state_root: commitment(checked.source_summary.post_state_root)?,
        represented_row_count: 2,
        leaf_records: vec![record],
        authority_grants_root: policy.authority_grants_root(),
        asset_flows: effects.flows.clone(),
        authority_uses: Vec::new(),
    })
    .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("semantic subtree"))
}

fn require_exact_adapter_journal(
    authenticated_bytes: &[u8],
    expected: &zenodex_zrpf_protocol_v3::NodeJournalV3,
) -> Result<(), SourceOpenedSpotValueLeafErrorV6> {
    let expected_bytes = encode_node_journal_v3(expected)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::AdapterJournalDecode)?;
    if expected_bytes.as_slice() != authenticated_bytes {
        return Err(SourceOpenedSpotValueLeafErrorV6::AdapterJournalMismatch);
    }
    Ok(())
}

fn canonical_tx_commitment_v6(
    chain_id: &str,
    transaction: &TauTxV1,
    intent: &SwapExactInIntentV1,
    ingress_nonce: u64,
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    let salt = intent.salt.as_deref().unwrap_or("");
    hash_framed(
        CANONICAL_TX_DOMAIN_V6,
        &[
            chain_id.as_bytes(),
            transaction.sender_pubkey.as_bytes(),
            &ingress_nonce.to_be_bytes(),
            intent.module.as_bytes(),
            intent.version.as_bytes(),
            intent.intent_id.as_bytes(),
            &intent.deadline.to_be_bytes(),
            intent.pool_id.as_bytes(),
            intent.asset_in.as_bytes(),
            intent.asset_out.as_bytes(),
            &intent.amount_in.to_be_bytes(),
            &intent.min_amount_out.to_be_bytes(),
            intent.recipient.as_bytes(),
            &[u8::from(intent.salt.is_some())],
            salt.as_bytes(),
        ],
    )
}

fn action_nullifier_v6(
    adapter: &zenodex_zrpf_protocol_v3::NodeJournalV3,
    transaction: &TauTxV1,
    intent: &SwapExactInIntentV1,
    ingress_nonce: u64,
    canonical_tx_commitment: CommitmentV3,
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    // Epoch, lane, task, and proof topology are deliberately excluded. The
    // durable ledger consumes this identity globally, so replaying the same
    // canonical sender nonce and action under another proof grouping, lane,
    // or epoch produces the same nullifier and must conflict.
    hash_framed(
        ACTION_NULLIFIER_DOMAIN_V6,
        &[
            adapter.scope().application_id().as_bytes(),
            adapter.scope().chain_or_domain_id().as_bytes(),
            transaction.sender_pubkey.as_bytes(),
            &ingress_nonce.to_be_bytes(),
            intent.intent_id.as_bytes(),
            canonical_tx_commitment.as_bytes(),
        ],
    )
}

fn data_availability_payload_commitment_v6(
    envelope: &SourceOpenedSpotValueLeafEnvelopeV6,
) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    hash_framed(
        DA_PAYLOAD_DOMAIN_V6,
        &[
            envelope.adapter_journal_bytes(),
            envelope.source_input_bytes(),
            envelope.source_journal_bytes(),
        ],
    )
}

fn decode_asset_id(value: &str) -> Result<[u8; 32], SourceOpenedSpotValueLeafErrorV6> {
    let bytes = value.as_bytes();
    if bytes.len() != 66 || &bytes[..2] != b"0x" {
        return Err(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
            "asset encoding",
        ));
    }
    let mut output = [0u8; 32];
    for (index, pair) in bytes[2..].chunks_exact(2).enumerate() {
        output[index] = decode_nibble(pair[0])?
            .checked_mul(16)
            .and_then(|high| high.checked_add(decode_nibble(pair[1]).ok()?))
            .ok_or(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
                "asset encoding",
            ))?;
    }
    if output == [0; 32] {
        return Err(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
            "zero asset",
        ));
    }
    Ok(output)
}

fn decode_nibble(value: u8) -> Result<u8, SourceOpenedSpotValueLeafErrorV6> {
    match value {
        b'0'..=b'9' => Ok(value - b'0'),
        b'a'..=b'f' => Ok(value - b'a' + 10),
        _ => Err(SourceOpenedSpotValueLeafErrorV6::SwapFlowRejected(
            "asset encoding",
        )),
    }
}

fn commitment(bytes: [u8; 32]) -> Result<CommitmentV3, SourceOpenedSpotValueLeafErrorV6> {
    CommitmentV3::new(bytes)
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::StatementDerivation("commitment"))
}

fn profile_reject<T>(field: &'static str) -> Result<T, SourceOpenedSpotValueLeafErrorV6> {
    Err(SourceOpenedSpotValueLeafErrorV6::SourceProfileRejected(
        field,
    ))
}
