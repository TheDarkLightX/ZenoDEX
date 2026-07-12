use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, MAX_VALUE_TRANSFER_ACTION_INDEX_V2};

use crate::{
    ProposedZusdValueFlowV1, ZusdValueFlowErrorV1, ZusdValueOperationInputV1, ZusdValueOperationV1,
    MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1,
};

const OPERATION_ID_DOMAIN_V1: &[u8] = b"zenodex.zrpf.zusd_value_operation.v1";
const PROPOSAL_COMMITMENT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.zusd_value_flow_proposal.v1";

pub(crate) fn operation_id_v1(
    operation: &ZusdValueOperationV1,
) -> Result<CommitmentV3, ZusdValueFlowErrorV1> {
    if operation.action_index() > MAX_VALUE_TRANSFER_ACTION_INDEX_V2 {
        return Err(ZusdValueFlowErrorV1::ActionIndexOutOfRange {
            actual: operation.action_index(),
            maximum: MAX_VALUE_TRANSFER_ACTION_INDEX_V2,
        });
    }
    let mut hasher = Sha256::new();
    hasher.update(OPERATION_ID_DOMAIN_V1);
    hasher.update(1u16.to_be_bytes());
    hasher.update(operation.action_index().to_be_bytes());
    hasher.update([operation.kind().tag()]);
    hash_operation_fields(&mut hasher, operation.input());
    commitment(hasher, "operation_id")
}

pub(crate) fn proposal_commitment_v1(
    proposal: &ProposedZusdValueFlowV1,
) -> Result<CommitmentV3, ZusdValueFlowErrorV1> {
    proposal.validate_self_consistency()?;
    let bytes =
        postcard::to_allocvec(proposal).map_err(|_| ZusdValueFlowErrorV1::PostcardDecode)?;
    if bytes.len() > MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1 {
        return Err(ZusdValueFlowErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1,
        });
    }
    let mut hasher = Sha256::new();
    hasher.update(PROPOSAL_COMMITMENT_DOMAIN_V1);
    hasher.update(
        u64::try_from(bytes.len())
            .map_err(|_| ZusdValueFlowErrorV1::InvalidDerivedCommitment("proposal_length"))?
            .to_be_bytes(),
    );
    hasher.update(bytes);
    commitment(hasher, "proposal_commitment")
}

fn hash_operation_fields(hasher: &mut Sha256, input: &ZusdValueOperationInputV1) {
    match input {
        ZusdValueOperationInputV1::DepositCollateral {
            depositor_scope_id,
            vault_scope_id,
            collateral_atoms,
            ..
        } => {
            update_commitments(hasher, &[*depositor_scope_id, *vault_scope_id]);
            hasher.update(collateral_atoms.to_be_bytes());
        }
        ZusdValueOperationInputV1::WithdrawCollateral {
            recipient_scope_id,
            vault_scope_id,
            collateral_atoms,
            ..
        } => {
            update_commitments(hasher, &[*recipient_scope_id, *vault_scope_id]);
            hasher.update(collateral_atoms.to_be_bytes());
        }
        ZusdValueOperationInputV1::MintZusd {
            recipient_scope_id,
            vault_scope_id,
            principal_atoms,
            fee_bps,
            ..
        } => {
            update_commitments(hasher, &[*recipient_scope_id, *vault_scope_id]);
            hasher.update(principal_atoms.to_be_bytes());
            hasher.update(fee_bps.to_be_bytes());
        }
        ZusdValueOperationInputV1::RepayBurn {
            payer_scope_id,
            vault_scope_id,
            zusd_atoms,
            ..
        } => {
            update_commitments(hasher, &[*payer_scope_id, *vault_scope_id]);
            hasher.update(zusd_atoms.to_be_bytes());
        }
        ZusdValueOperationInputV1::StabilityPoolDeposit {
            depositor_scope_id,
            zusd_atoms,
            ..
        } => {
            hasher.update(depositor_scope_id.as_bytes());
            hasher.update(zusd_atoms.to_be_bytes());
        }
        ZusdValueOperationInputV1::StabilityPoolWithdraw {
            recipient_scope_id,
            zusd_atoms,
            ..
        } => {
            hasher.update(recipient_scope_id.as_bytes());
            hasher.update(zusd_atoms.to_be_bytes());
        }
        ZusdValueOperationInputV1::RedeemZusd {
            redeemer_scope_id,
            vault_scope_id,
            zusd_atoms,
            oracle_price_e8,
            redemption_fee_bps,
            proposed_oracle_binding_hash,
            ..
        } => {
            update_commitments(hasher, &[*redeemer_scope_id, *vault_scope_id]);
            hasher.update(zusd_atoms.to_be_bytes());
            hasher.update(oracle_price_e8.to_be_bytes());
            hasher.update(redemption_fee_bps.to_be_bytes());
            hasher.update(proposed_oracle_binding_hash.as_bytes());
        }
        ZusdValueOperationInputV1::Liquidate {
            vault_scope_id,
            liquidator_scope_id,
            debt_zusd_atoms,
            collateral_atoms,
            gas_comp_fixed_collateral_atoms,
            gas_comp_bps,
            proposed_oracle_binding_hash,
            ..
        } => {
            update_commitments(hasher, &[*vault_scope_id, *liquidator_scope_id]);
            hasher.update(debt_zusd_atoms.to_be_bytes());
            hasher.update(collateral_atoms.to_be_bytes());
            hasher.update(gas_comp_fixed_collateral_atoms.to_be_bytes());
            hasher.update(gas_comp_bps.to_be_bytes());
            hasher.update(proposed_oracle_binding_hash.as_bytes());
        }
    }
}

fn update_commitments(hasher: &mut Sha256, commitments: &[CommitmentV3]) {
    for value in commitments {
        hasher.update(value.as_bytes());
    }
}

fn commitment(hasher: Sha256, field: &'static str) -> Result<CommitmentV3, ZusdValueFlowErrorV1> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| ZusdValueFlowErrorV1::InvalidDerivedCommitment(field))
}
