use sha2::{Digest, Sha256};

use super::{ValueTransferErrorV2, ValueTransferIdV2, ValueTransferV2};
use crate::CommitmentV3;

const VALUE_TRANSFER_ID_DOMAIN_V2: &[u8] = b"zenodex.zrpf.value_transfer_id.v2";
const VALUE_TRANSFER_SET_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.value_transfer_set_root.v2";
const VALUE_TRANSFER_SOURCE_CLAIMS_ROOT_DOMAIN_V2: &[u8] =
    b"zenodex.zrpf.value_transfer_source_claims_root.v2";
const VALUE_TRANSFER_SOURCE_TRANSITIONS_ROOT_DOMAIN_V2: &[u8] =
    b"zenodex.zrpf.value_transfer_source_transitions_root.v2";

pub(super) fn derive_value_transfer_id_v2(
    transfer: &ValueTransferV2,
) -> Result<ValueTransferIdV2, ValueTransferErrorV2> {
    let mut hasher = domain_hasher(VALUE_TRANSFER_ID_DOMAIN_V2)?;
    hasher.update(transfer.application_id().as_bytes());
    hasher.update(transfer.chain_or_domain_id().as_bytes());
    hasher.update(transfer.epoch_id().to_be_bytes());
    hasher.update(transfer.action_index().to_be_bytes());
    hasher.update([transfer.kind().tag()]);
    hasher.update(transfer.action_hash().as_bytes());
    hasher.update(transfer.source_lane_id().as_bytes());
    hasher.update(transfer.destination_lane_id().as_bytes());
    hasher.update(transfer.asset_id().as_bytes());
    hasher.update(transfer.amount_atoms().to_be_bytes());
    hasher.update(transfer.sender_scope_hash().as_bytes());
    hasher.update(transfer.recipient_scope_hash().as_bytes());
    hasher.update(transfer.source_state_transition_hash().as_bytes());
    hasher.update(transfer.source_receipt_claim_hash().as_bytes());
    hasher.update(transfer.deadline_epoch().to_be_bytes());
    ValueTransferIdV2::new(hasher.finalize().into())
}

pub(super) fn transfer_set_root_v2(
    transfers: &[ValueTransferV2],
) -> Result<CommitmentV3, ValueTransferErrorV2> {
    list_root(
        VALUE_TRANSFER_SET_ROOT_DOMAIN_V2,
        transfers
            .iter()
            .map(ValueTransferV2::canonical_id)
            .collect::<Result<alloc::vec::Vec<_>, _>>()?
            .iter()
            .map(ValueTransferIdV2::as_bytes),
        "value_transfer_set_root",
    )
}

pub(super) fn source_claims_root_v2(
    transfers: &[ValueTransferV2],
) -> Result<CommitmentV3, ValueTransferErrorV2> {
    list_root(
        VALUE_TRANSFER_SOURCE_CLAIMS_ROOT_DOMAIN_V2,
        transfers
            .iter()
            .map(|transfer| transfer.source_receipt_claim_hash().into_bytes())
            .collect::<alloc::vec::Vec<_>>()
            .iter(),
        "value_transfer_source_claims_root",
    )
}

pub(super) fn source_transitions_root_v2(
    transfers: &[ValueTransferV2],
) -> Result<CommitmentV3, ValueTransferErrorV2> {
    list_root(
        VALUE_TRANSFER_SOURCE_TRANSITIONS_ROOT_DOMAIN_V2,
        transfers
            .iter()
            .map(|transfer| transfer.source_state_transition_hash().into_bytes())
            .collect::<alloc::vec::Vec<_>>()
            .iter(),
        "value_transfer_source_transitions_root",
    )
}

fn list_root<'a>(
    domain: &'static [u8],
    values: impl ExactSizeIterator<Item = &'a [u8; 32]>,
    field: &'static str,
) -> Result<CommitmentV3, ValueTransferErrorV2> {
    let mut hasher = domain_hasher(domain)?;
    let count =
        u32::try_from(values.len()).map_err(|_| ValueTransferErrorV2::ArithmeticOverflow(field))?;
    hasher.update(count.to_be_bytes());
    for value in values {
        hasher.update(value);
    }
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| ValueTransferErrorV2::InvalidDerivedCommitment(field))
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, ValueTransferErrorV2> {
    let length = u16::try_from(domain.len())
        .map_err(|_| ValueTransferErrorV2::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}
