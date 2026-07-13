use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

use super::hash::derive_value_transfer_id_v2;
use super::{ValueTransferErrorV2, MAX_VALUE_TRANSFER_ACTION_INDEX_V2, VALUE_TRANSFER_VERSION_V2};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ValueTransferKindV2 {
    InsuranceSeed,
    CollateralDeposit,
    CollateralWithdrawal,
}

impl ValueTransferKindV2 {
    pub const fn tag(self) -> u8 {
        match self {
            Self::InsuranceSeed => 1,
            Self::CollateralDeposit => 2,
            Self::CollateralWithdrawal => 3,
        }
    }

    fn from_tag(tag: u8) -> Result<Self, ValueTransferErrorV2> {
        match tag {
            1 => Ok(Self::InsuranceSeed),
            2 => Ok(Self::CollateralDeposit),
            3 => Ok(Self::CollateralWithdrawal),
            _ => Err(ValueTransferErrorV2::InvalidKind(tag)),
        }
    }
}

impl Serialize for ValueTransferKindV2 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u8(self.tag())
    }
}

impl<'de> Deserialize<'de> for ValueTransferKindV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let tag = u8::deserialize(deserializer)?;
        Self::from_tag(tag).map_err(de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueTransferIdV2([u8; 32]);

impl ValueTransferIdV2 {
    pub(super) fn new(bytes: [u8; 32]) -> Result<Self, ValueTransferErrorV2> {
        if bytes == [0; 32] {
            return Err(ValueTransferErrorV2::InvalidDerivedCommitment(
                "value_transfer_id",
            ));
        }
        Ok(Self(bytes))
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    pub const fn into_bytes(self) -> [u8; 32] {
        self.0
    }
}

impl Serialize for ValueTransferIdV2 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for ValueTransferIdV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let bytes = <[u8; 32]>::deserialize(deserializer)?;
        Self::new(bytes).map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueTransferInputV2 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub epoch_id: u64,
    pub action_index: u32,
    pub kind: ValueTransferKindV2,
    pub action_hash: CommitmentV3,
    pub source_lane_id: CommitmentV3,
    pub destination_lane_id: CommitmentV3,
    pub asset_id: CommitmentV3,
    pub amount_atoms: u128,
    pub sender_scope_hash: CommitmentV3,
    pub recipient_scope_hash: CommitmentV3,
    pub source_state_transition_hash: CommitmentV3,
    pub source_receipt_claim_hash: CommitmentV3,
    pub deadline_epoch: u64,
}

/// Proof-neutral cross-lane value-transfer proposal.
///
/// Cryptographic authority must be attached by a verifier that authenticates
/// `source_receipt_claim_hash` and the source transition under a governed
/// program. Construction and decoding establish only canonical structure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ValueTransferV2 {
    transfer_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    action_index: u32,
    kind: ValueTransferKindV2,
    action_hash: CommitmentV3,
    source_lane_id: CommitmentV3,
    destination_lane_id: CommitmentV3,
    asset_id: CommitmentV3,
    amount_atoms: u128,
    sender_scope_hash: CommitmentV3,
    recipient_scope_hash: CommitmentV3,
    source_state_transition_hash: CommitmentV3,
    source_receipt_claim_hash: CommitmentV3,
    deadline_epoch: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ValueTransferWireV2 {
    transfer_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    action_index: u32,
    kind: ValueTransferKindV2,
    action_hash: CommitmentV3,
    source_lane_id: CommitmentV3,
    destination_lane_id: CommitmentV3,
    asset_id: CommitmentV3,
    amount_atoms: u128,
    sender_scope_hash: CommitmentV3,
    recipient_scope_hash: CommitmentV3,
    source_state_transition_hash: CommitmentV3,
    source_receipt_claim_hash: CommitmentV3,
    deadline_epoch: u64,
}

impl ValueTransferV2 {
    pub fn new(input: ValueTransferInputV2) -> Result<Self, ValueTransferErrorV2> {
        Self::from_parts(VALUE_TRANSFER_VERSION_V2, input)
    }

    fn from_parts(
        transfer_version: u16,
        input: ValueTransferInputV2,
    ) -> Result<Self, ValueTransferErrorV2> {
        let transfer = Self {
            transfer_version,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            epoch_id: input.epoch_id,
            action_index: input.action_index,
            kind: input.kind,
            action_hash: input.action_hash,
            source_lane_id: input.source_lane_id,
            destination_lane_id: input.destination_lane_id,
            asset_id: input.asset_id,
            amount_atoms: input.amount_atoms,
            sender_scope_hash: input.sender_scope_hash,
            recipient_scope_hash: input.recipient_scope_hash,
            source_state_transition_hash: input.source_state_transition_hash,
            source_receipt_claim_hash: input.source_receipt_claim_hash,
            deadline_epoch: input.deadline_epoch,
        };
        transfer.validate_self_consistency()?;
        Ok(transfer)
    }

    pub fn validate_self_consistency(&self) -> Result<(), ValueTransferErrorV2> {
        if self.transfer_version != VALUE_TRANSFER_VERSION_V2 {
            return Err(ValueTransferErrorV2::InvalidTransferVersion(
                self.transfer_version,
            ));
        }
        if self.source_lane_id == self.destination_lane_id {
            return Err(ValueTransferErrorV2::InvalidRoute);
        }
        if self.amount_atoms == 0 {
            return Err(ValueTransferErrorV2::ZeroAmount);
        }
        if self.action_index > MAX_VALUE_TRANSFER_ACTION_INDEX_V2 {
            return Err(ValueTransferErrorV2::ActionIndexOutOfRange {
                actual: self.action_index,
                maximum: MAX_VALUE_TRANSFER_ACTION_INDEX_V2,
            });
        }
        if self.deadline_epoch < self.epoch_id {
            return Err(ValueTransferErrorV2::DeadlineBeforeEpoch);
        }
        Ok(())
    }

    pub fn canonical_id(&self) -> Result<ValueTransferIdV2, ValueTransferErrorV2> {
        self.validate_self_consistency()?;
        derive_value_transfer_id_v2(self)
    }

    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }

    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }

    pub const fn epoch_id(&self) -> u64 {
        self.epoch_id
    }

    pub const fn action_index(&self) -> u32 {
        self.action_index
    }

    pub const fn kind(&self) -> ValueTransferKindV2 {
        self.kind
    }

    pub const fn action_hash(&self) -> CommitmentV3 {
        self.action_hash
    }

    pub const fn source_lane_id(&self) -> CommitmentV3 {
        self.source_lane_id
    }

    pub const fn destination_lane_id(&self) -> CommitmentV3 {
        self.destination_lane_id
    }

    pub const fn asset_id(&self) -> CommitmentV3 {
        self.asset_id
    }

    pub const fn amount_atoms(&self) -> u128 {
        self.amount_atoms
    }

    pub const fn sender_scope_hash(&self) -> CommitmentV3 {
        self.sender_scope_hash
    }

    pub const fn recipient_scope_hash(&self) -> CommitmentV3 {
        self.recipient_scope_hash
    }

    pub const fn source_state_transition_hash(&self) -> CommitmentV3 {
        self.source_state_transition_hash
    }

    pub const fn source_receipt_claim_hash(&self) -> CommitmentV3 {
        self.source_receipt_claim_hash
    }

    pub const fn deadline_epoch(&self) -> u64 {
        self.deadline_epoch
    }
}

impl<'de> Deserialize<'de> for ValueTransferV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ValueTransferWireV2::deserialize(deserializer)?;
        Self::from_parts(
            wire.transfer_version,
            ValueTransferInputV2 {
                application_id: wire.application_id,
                chain_or_domain_id: wire.chain_or_domain_id,
                epoch_id: wire.epoch_id,
                action_index: wire.action_index,
                kind: wire.kind,
                action_hash: wire.action_hash,
                source_lane_id: wire.source_lane_id,
                destination_lane_id: wire.destination_lane_id,
                asset_id: wire.asset_id,
                amount_atoms: wire.amount_atoms,
                sender_scope_hash: wire.sender_scope_hash,
                recipient_scope_hash: wire.recipient_scope_hash,
                source_state_transition_hash: wire.source_state_transition_hash,
                source_receipt_claim_hash: wire.source_receipt_claim_hash,
                deadline_epoch: wire.deadline_epoch,
            },
        )
        .map_err(de::Error::custom)
    }
}
