use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::{perps_np_operation_hash_v1, PerpsNpActionV1};
use zenodex_zrpf_protocol_v3::{
    decode_exact_value_transfer_set_v2, CommitmentV3, ValueTransferInputV2, ValueTransferKindV2,
    ValueTransferSetV2, ValueTransferV2, MAX_VALUE_TRANSFER_ACTION_INDEX_V2,
};

use crate::model::expected_route;
use crate::{
    PerpsCollateralReferenceContextV1, PerpsSourceFinalityReferenceErrorV1,
    ProposedPerpsCollateralRowsV1, ProposedSourceEvidenceV1,
};

struct ActionExpectationV1 {
    action_index: u32,
    kind: ValueTransferKindV2,
    action_hash: CommitmentV3,
    asset_id: CommitmentV3,
    amount_atoms: u128,
    counterparty_actor_scope_hash: Option<CommitmentV3>,
    perps_scope_hash: CommitmentV3,
}

struct ActionMaterialV1<'a> {
    kind: ValueTransferKindV2,
    actor: Option<&'a str>,
    asset: &'a str,
    amount: u128,
}

pub fn perps_counterparty_actor_scope_v1(
    actor: &str,
) -> Result<CommitmentV3, PerpsSourceFinalityReferenceErrorV1> {
    if actor.is_empty() {
        return Err(
            PerpsSourceFinalityReferenceErrorV1::InvalidDerivedCommitment(
                "empty_counterparty_actor",
            ),
        );
    }
    framed_commitment(
        b"zenodex.zrpf.perps_collateral.actor_scope.v1",
        &[actor.as_bytes()],
    )
}

pub fn proposed_transfer_input_for_perps_action_v1(
    context: PerpsCollateralReferenceContextV1,
    action_index: u32,
    action: &PerpsNpActionV1,
    source_evidence: ProposedSourceEvidenceV1,
) -> Result<ValueTransferInputV2, PerpsSourceFinalityReferenceErrorV1> {
    let expected = action_expectation(context, action_index, action)?
        .ok_or(PerpsSourceFinalityReferenceErrorV1::UnsupportedAction { action_index })?;
    let (source_lane_id, destination_lane_id) = expected_route(context, expected.kind);
    let proposed_counterparty_scope = source_evidence.counterparty_actor_scope_hash();
    let counterparty_scope = match expected.counterparty_actor_scope_hash {
        Some(required) if required != proposed_counterparty_scope => {
            return Err(PerpsSourceFinalityReferenceErrorV1::InvalidAction {
                action_index,
                field: "counterparty_actor_scope_hash",
            });
        }
        Some(required) => required,
        None => proposed_counterparty_scope,
    };
    let (sender_scope_hash, recipient_scope_hash) =
        expected_scopes(expected.kind, expected.perps_scope_hash, counterparty_scope);
    Ok(ValueTransferInputV2 {
        application_id: context.application_id(),
        chain_or_domain_id: context.chain_or_domain_id(),
        epoch_id: context.epoch_id(),
        action_index,
        kind: expected.kind,
        action_hash: expected.action_hash,
        source_lane_id,
        destination_lane_id,
        asset_id: expected.asset_id,
        amount_atoms: expected.amount_atoms,
        sender_scope_hash,
        recipient_scope_hash,
        source_state_transition_hash: source_evidence.source_state_transition_hash(),
        source_receipt_claim_hash: source_evidence.source_receipt_claim_hash(),
        deadline_epoch: context.deadline_epoch(),
    })
}

pub fn derive_proposed_perps_collateral_rows_v1(
    context: PerpsCollateralReferenceContextV1,
    actions: &[PerpsNpActionV1],
    exact_transfer_set_bytes: &[u8],
) -> Result<ProposedPerpsCollateralRowsV1, PerpsSourceFinalityReferenceErrorV1> {
    let transfer_set = decode_exact_value_transfer_set_v2(exact_transfer_set_bytes)?;
    require_transfer_scope(context, &transfer_set)?;
    let expectations = collect_expectations(context, actions)?;
    if expectations.is_empty() {
        return Err(PerpsSourceFinalityReferenceErrorV1::NoValueMovingActions);
    }
    match_transfers(context, &expectations, &transfer_set)?;
    ProposedPerpsCollateralRowsV1::new(context, transfer_set)
}

fn collect_expectations(
    context: PerpsCollateralReferenceContextV1,
    actions: &[PerpsNpActionV1],
) -> Result<Vec<ActionExpectationV1>, PerpsSourceFinalityReferenceErrorV1> {
    let mut expected = Vec::new();
    for (index, action) in actions.iter().enumerate() {
        let action_index = u32::try_from(index).map_err(|_| {
            PerpsSourceFinalityReferenceErrorV1::InvalidAction {
                action_index: u32::MAX,
                field: "action_index",
            }
        })?;
        if let Some(expectation) = action_expectation(context, action_index, action)? {
            expected.push(expectation);
        }
    }
    Ok(expected)
}

fn match_transfers(
    context: PerpsCollateralReferenceContextV1,
    expectations: &[ActionExpectationV1],
    transfer_set: &ValueTransferSetV2,
) -> Result<(), PerpsSourceFinalityReferenceErrorV1> {
    let mut by_action = BTreeMap::<u32, &ValueTransferV2>::new();
    for transfer in transfer_set.transfers() {
        if by_action
            .insert(transfer.action_index(), transfer)
            .is_some()
        {
            return Err(
                PerpsSourceFinalityReferenceErrorV1::DuplicateTransferForAction {
                    action_index: transfer.action_index(),
                },
            );
        }
    }
    for expected in expectations {
        let transfer = by_action.remove(&expected.action_index).ok_or(
            PerpsSourceFinalityReferenceErrorV1::MissingTransfer {
                action_index: expected.action_index,
            },
        )?;
        require_transfer_match(context, expected, transfer)?;
    }
    if let Some(action_index) = by_action.keys().next().copied() {
        return Err(PerpsSourceFinalityReferenceErrorV1::UnexpectedTransfer { action_index });
    }
    Ok(())
}

fn require_transfer_match(
    context: PerpsCollateralReferenceContextV1,
    expected: &ActionExpectationV1,
    transfer: &ValueTransferV2,
) -> Result<(), PerpsSourceFinalityReferenceErrorV1> {
    let action_index = expected.action_index;
    let (source, destination) = expected_route(context, expected.kind);
    if transfer.source_lane_id() != source || transfer.destination_lane_id() != destination {
        return Err(PerpsSourceFinalityReferenceErrorV1::WrongCounterparty { action_index });
    }
    let checks = [
        (transfer.kind() == expected.kind, "kind"),
        (
            transfer.action_hash() == expected.action_hash,
            "action_hash",
        ),
        (transfer.asset_id() == expected.asset_id, "asset_id"),
        (
            transfer.amount_atoms() == expected.amount_atoms,
            "amount_atoms",
        ),
        (
            transfer.deadline_epoch() == context.deadline_epoch(),
            "deadline_epoch",
        ),
    ];
    for (matches, field) in checks {
        if !matches {
            return Err(PerpsSourceFinalityReferenceErrorV1::TransferMismatch {
                action_index,
                field,
            });
        }
    }
    require_transfer_scopes(expected, transfer)?;
    Ok(())
}

fn require_transfer_scopes(
    expected: &ActionExpectationV1,
    transfer: &ValueTransferV2,
) -> Result<(), PerpsSourceFinalityReferenceErrorV1> {
    let action_index = expected.action_index;
    let (perps_matches, counterparty_matches, counterparty_field) = match expected.kind {
        ValueTransferKindV2::InsuranceSeed | ValueTransferKindV2::CollateralDeposit => (
            transfer.recipient_scope_hash() == expected.perps_scope_hash,
            expected
                .counterparty_actor_scope_hash
                .is_none_or(|scope| transfer.sender_scope_hash() == scope),
            "sender_scope_hash",
        ),
        ValueTransferKindV2::CollateralWithdrawal => (
            transfer.sender_scope_hash() == expected.perps_scope_hash,
            expected
                .counterparty_actor_scope_hash
                .is_none_or(|scope| transfer.recipient_scope_hash() == scope),
            "recipient_scope_hash",
        ),
    };
    if !perps_matches {
        return Err(PerpsSourceFinalityReferenceErrorV1::TransferMismatch {
            action_index,
            field: "perps_scope_hash",
        });
    }
    if !counterparty_matches {
        return Err(PerpsSourceFinalityReferenceErrorV1::TransferMismatch {
            action_index,
            field: counterparty_field,
        });
    }
    Ok(())
}

fn expected_scopes(
    kind: ValueTransferKindV2,
    perps_scope_hash: CommitmentV3,
    counterparty_scope_hash: CommitmentV3,
) -> (CommitmentV3, CommitmentV3) {
    match kind {
        ValueTransferKindV2::InsuranceSeed | ValueTransferKindV2::CollateralDeposit => {
            (counterparty_scope_hash, perps_scope_hash)
        }
        ValueTransferKindV2::CollateralWithdrawal => (perps_scope_hash, counterparty_scope_hash),
    }
}

fn require_transfer_scope(
    context: PerpsCollateralReferenceContextV1,
    transfer_set: &ValueTransferSetV2,
) -> Result<(), PerpsSourceFinalityReferenceErrorV1> {
    if transfer_set.application_id() != context.application_id()
        || transfer_set.chain_or_domain_id() != context.chain_or_domain_id()
        || transfer_set.epoch_id() != context.epoch_id()
    {
        return Err(PerpsSourceFinalityReferenceErrorV1::InvalidContext(
            "transfer_scope",
        ));
    }
    Ok(())
}

fn action_expectation(
    context: PerpsCollateralReferenceContextV1,
    action_index: u32,
    action: &PerpsNpActionV1,
) -> Result<Option<ActionExpectationV1>, PerpsSourceFinalityReferenceErrorV1> {
    if action_index > MAX_VALUE_TRANSFER_ACTION_INDEX_V2 {
        return Err(invalid_action(action_index, "action_index"));
    }
    let Some(material) = action_material(action_index, action)? else {
        return Ok(None);
    };
    if material.asset.is_empty() || material.actor.is_some_and(str::is_empty) {
        return Err(invalid_action(action_index, "empty_actor_or_asset"));
    }
    let action_hash = commitment_from_bytes(
        perps_np_operation_hash_v1(core::slice::from_ref(action)),
        "action_hash",
    )?;
    let asset_id = framed_commitment(
        b"zenodex.zrpf.perps_collateral.asset_id.v1",
        &[material.asset.as_bytes()],
    )?;
    let counterparty_actor_scope_hash = material
        .actor
        .map(perps_counterparty_actor_scope_v1)
        .transpose()?;
    let perps_scope = framed_commitment(
        b"zenodex.zrpf.perps_collateral.lane_scope.v1",
        &[context.perps_lane_id().as_bytes()],
    )?;
    Ok(Some(ActionExpectationV1 {
        action_index,
        kind: material.kind,
        action_hash,
        asset_id,
        amount_atoms: material.amount,
        counterparty_actor_scope_hash,
        perps_scope_hash: perps_scope,
    }))
}

fn action_material(
    action_index: u32,
    action: &PerpsNpActionV1,
) -> Result<Option<ActionMaterialV1<'_>>, PerpsSourceFinalityReferenceErrorV1> {
    let material = match action {
        PerpsNpActionV1::InitMarket {
            collateral_asset,
            insurance_seed_e8,
            ..
        } => {
            if *insurance_seed_e8 < 0 {
                return Err(invalid_action(action_index, "insurance_seed_e8"));
            }
            if *insurance_seed_e8 == 0 {
                return Ok(None);
            }
            ActionMaterialV1 {
                kind: ValueTransferKindV2::InsuranceSeed,
                actor: None,
                asset: collateral_asset.as_str(),
                amount: u128::try_from(*insurance_seed_e8)
                    .map_err(|_| invalid_action(action_index, "insurance_seed_e8"))?,
            }
        }
        PerpsNpActionV1::DepositCollateral {
            pubkey,
            asset,
            amount_e8,
            ..
        } => ActionMaterialV1 {
            kind: ValueTransferKindV2::CollateralDeposit,
            actor: Some(pubkey.as_str()),
            asset: asset.as_str(),
            amount: positive_amount(*amount_e8, action_index)?,
        },
        PerpsNpActionV1::WithdrawCollateral {
            pubkey,
            asset,
            amount_e8,
            ..
        } => ActionMaterialV1 {
            kind: ValueTransferKindV2::CollateralWithdrawal,
            actor: Some(pubkey.as_str()),
            asset: asset.as_str(),
            amount: positive_amount(*amount_e8, action_index)?,
        },
        PerpsNpActionV1::SubmitIntent { .. } | PerpsNpActionV1::RunEpoch { .. } => return Ok(None),
    };
    Ok(Some(material))
}

fn positive_amount(
    amount: i128,
    action_index: u32,
) -> Result<u128, PerpsSourceFinalityReferenceErrorV1> {
    if amount <= 0 {
        return Err(invalid_action(action_index, "amount_e8"));
    }
    u128::try_from(amount).map_err(|_| invalid_action(action_index, "amount_e8"))
}

fn invalid_action(action_index: u32, field: &'static str) -> PerpsSourceFinalityReferenceErrorV1 {
    PerpsSourceFinalityReferenceErrorV1::InvalidAction {
        action_index,
        field,
    }
}

fn framed_commitment(
    domain: &[u8],
    fields: &[&[u8]],
) -> Result<CommitmentV3, PerpsSourceFinalityReferenceErrorV1> {
    let mut hasher = Sha256::new();
    let domain_len = u16::try_from(domain.len()).map_err(|_| {
        PerpsSourceFinalityReferenceErrorV1::InvalidDerivedCommitment("domain_length")
    })?;
    hasher.update(domain_len.to_be_bytes());
    hasher.update(domain);
    for field in fields {
        let len = u32::try_from(field.len()).map_err(|_| {
            PerpsSourceFinalityReferenceErrorV1::InvalidDerivedCommitment("field_length")
        })?;
        hasher.update(len.to_be_bytes());
        hasher.update(field);
    }
    commitment_from_bytes(hasher.finalize().into(), "framed_hash")
}

fn commitment_from_bytes(
    bytes: [u8; 32],
    field: &'static str,
) -> Result<CommitmentV3, PerpsSourceFinalityReferenceErrorV1> {
    CommitmentV3::new(bytes)
        .map_err(|_| PerpsSourceFinalityReferenceErrorV1::InvalidDerivedCommitment(field))
}
