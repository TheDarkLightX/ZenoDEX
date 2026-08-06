use sha2::{Digest, Sha256};

use super::{
    AssetTransferAccountIdV1, AssetTransferAssetIdV1, AssetTransferBalanceV1,
    AssetTransferCommandV1, AssetTransferErrorV1, AssetTransferMovementV1,
    AssetTransferStateRootV1,
};
use crate::{AuthorizationSubjectIdV1, CommitmentV3};

const STATE_ROOT_DOMAIN_V1: &[u8] = b"zenodex.asset_transfer.state_root.v1";
const COMMAND_HASH_DOMAIN_V1: &[u8] = b"zenodex.asset_transfer.command_hash.v1";
const RECEIPT_HASH_DOMAIN_V1: &[u8] = b"zenodex.asset_transfer.receipt_hash.v1";

pub(super) fn derive_state_root_v1(
    state_version: u16,
    balances: &[AssetTransferBalanceV1],
) -> Result<AssetTransferStateRootV1, AssetTransferErrorV1> {
    let mut hasher = domain_hasher(STATE_ROOT_DOMAIN_V1);
    absorb(&mut hasher, &state_version.to_be_bytes());
    let count = u16::try_from(balances.len())
        .map_err(|_| AssetTransferErrorV1::ArithmeticOverflow("balance_count"))?;
    absorb(&mut hasher, &count.to_be_bytes());
    for balance in balances {
        absorb(&mut hasher, balance.account_id().as_bytes());
        absorb(&mut hasher, balance.asset_id().as_bytes());
        absorb(&mut hasher, &balance.amount_atoms().to_be_bytes());
    }
    AssetTransferStateRootV1::new(finalize(hasher))
}

pub(super) fn derive_command_hash_v1(
    command_version: u16,
    source_account_id: AssetTransferAccountIdV1,
    destination_account_id: AssetTransferAccountIdV1,
    asset_id: AssetTransferAssetIdV1,
    amount_atoms: u128,
) -> Result<CommitmentV3, AssetTransferErrorV1> {
    let mut hasher = domain_hasher(COMMAND_HASH_DOMAIN_V1);
    absorb(&mut hasher, &command_version.to_be_bytes());
    absorb(&mut hasher, source_account_id.as_bytes());
    absorb(&mut hasher, destination_account_id.as_bytes());
    absorb(&mut hasher, asset_id.as_bytes());
    absorb(&mut hasher, &amount_atoms.to_be_bytes());
    CommitmentV3::new(finalize(hasher))
        .map_err(|_| AssetTransferErrorV1::InvalidDerivedCommitment("command_hash"))
}

pub(super) struct AssetTransferReceiptHashInputV1<'a> {
    pub expected_pre_state_root: AssetTransferStateRootV1,
    pub expected_command_hash: CommitmentV3,
    pub expected_authorization_subject_id: AuthorizationSubjectIdV1,
    pub command: &'a AssetTransferCommandV1,
    pub post_state_root: AssetTransferStateRootV1,
    pub movement: AssetTransferMovementV1,
    pub pre_asset_total_atoms: u128,
    pub post_asset_total_atoms: u128,
}

pub(super) fn derive_receipt_hash_v1(
    input: AssetTransferReceiptHashInputV1<'_>,
) -> Result<CommitmentV3, AssetTransferErrorV1> {
    let mut hasher = domain_hasher(RECEIPT_HASH_DOMAIN_V1);
    absorb(&mut hasher, input.expected_pre_state_root.as_bytes());
    absorb(&mut hasher, input.expected_command_hash.as_bytes());
    absorb(
        &mut hasher,
        input.expected_authorization_subject_id.as_bytes(),
    );
    absorb(&mut hasher, input.command.canonical_hash()?.as_bytes());
    absorb(&mut hasher, input.post_state_root.as_bytes());
    absorb(&mut hasher, input.movement.source_account_id().as_bytes());
    absorb(
        &mut hasher,
        input.movement.destination_account_id().as_bytes(),
    );
    absorb(&mut hasher, input.movement.asset_id().as_bytes());
    absorb(&mut hasher, &input.movement.amount_atoms().to_be_bytes());
    absorb(&mut hasher, &input.pre_asset_total_atoms.to_be_bytes());
    absorb(&mut hasher, &input.post_asset_total_atoms.to_be_bytes());
    CommitmentV3::new(finalize(hasher))
        .map_err(|_| AssetTransferErrorV1::InvalidDerivedCommitment("receipt_hash"))
}

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    absorb(&mut hasher, domain);
    hasher
}

fn absorb(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

fn finalize(hasher: Sha256) -> [u8; 32] {
    hasher.finalize().into()
}
