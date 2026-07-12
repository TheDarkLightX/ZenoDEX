use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;
use core::marker::PhantomData;

use serde::de::{self, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};

use super::hash::{source_claims_root_v2, source_transitions_root_v2, transfer_set_root_v2};
use super::{
    ValueTransferErrorV2, ValueTransferIdV2, ValueTransferKindV2, ValueTransferV2,
    MAX_VALUE_TRANSFERS_PER_SET_V2, VALUE_TRANSFER_SET_VERSION_V2,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ValueTransferSetV2 {
    set_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    #[serde(serialize_with = "serialize_transfers")]
    transfers: Vec<ValueTransferV2>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ValueTransferSetWireV2 {
    set_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    #[serde(deserialize_with = "deserialize_transfers")]
    transfers: Vec<ValueTransferV2>,
}

impl ValueTransferSetV2 {
    pub fn new(transfers: Vec<ValueTransferV2>) -> Result<Self, ValueTransferErrorV2> {
        require_transfer_count(transfers.len())?;
        let mut keyed = transfers
            .into_iter()
            .map(|transfer| Ok((transfer.canonical_id()?, transfer)))
            .collect::<Result<Vec<_>, ValueTransferErrorV2>>()?;
        keyed.sort_by_key(|(transfer_id, _)| *transfer_id);
        let transfers = keyed
            .into_iter()
            .map(|(_, transfer)| transfer)
            .collect::<Vec<_>>();
        let first = transfers
            .first()
            .ok_or(ValueTransferErrorV2::EmptyTransfers)?;
        let set = Self {
            set_version: VALUE_TRANSFER_SET_VERSION_V2,
            application_id: first.application_id(),
            chain_or_domain_id: first.chain_or_domain_id(),
            epoch_id: first.epoch_id(),
            transfers,
        };
        set.validate_self_consistency()?;
        Ok(set)
    }

    fn from_parts(
        set_version: u16,
        application_id: ApplicationIdV3,
        chain_or_domain_id: DomainIdV3,
        epoch_id: u64,
        transfers: Vec<ValueTransferV2>,
    ) -> Result<Self, ValueTransferErrorV2> {
        let set = Self {
            set_version,
            application_id,
            chain_or_domain_id,
            epoch_id,
            transfers,
        };
        set.validate_self_consistency()?;
        Ok(set)
    }

    pub fn validate_self_consistency(&self) -> Result<(), ValueTransferErrorV2> {
        if self.set_version != VALUE_TRANSFER_SET_VERSION_V2 {
            return Err(ValueTransferErrorV2::InvalidSetVersion(self.set_version));
        }
        require_transfer_count(self.transfers.len())?;
        let mut prior_id: Option<ValueTransferIdV2> = None;
        let mut action_bindings = BTreeSet::<(ValueTransferKindV2, u32, CommitmentV3)>::new();
        for transfer in &self.transfers {
            transfer.validate_self_consistency()?;
            if transfer.application_id() != self.application_id
                || transfer.chain_or_domain_id() != self.chain_or_domain_id
            {
                return Err(ValueTransferErrorV2::ScopeMismatch);
            }
            if transfer.epoch_id() != self.epoch_id {
                return Err(ValueTransferErrorV2::EpochMismatch);
            }
            let transfer_id = transfer.canonical_id()?;
            if prior_id.is_some_and(|prior| prior >= transfer_id) {
                return Err(if prior_id == Some(transfer_id) {
                    ValueTransferErrorV2::DuplicateTransfer
                } else {
                    ValueTransferErrorV2::NonCanonicalTransferOrder
                });
            }
            prior_id = Some(transfer_id);
            let action_binding = (
                transfer.kind(),
                transfer.action_index(),
                transfer.action_hash(),
            );
            if !action_bindings.insert(action_binding) {
                return Err(ValueTransferErrorV2::DuplicateActionBinding);
            }
        }
        Ok(())
    }

    pub fn canonical_root(&self) -> Result<CommitmentV3, ValueTransferErrorV2> {
        self.validate_self_consistency()?;
        transfer_set_root_v2(&self.transfers)
    }

    pub fn source_claims_root(&self) -> Result<CommitmentV3, ValueTransferErrorV2> {
        self.validate_self_consistency()?;
        source_claims_root_v2(&self.transfers)
    }

    pub fn source_transitions_root(&self) -> Result<CommitmentV3, ValueTransferErrorV2> {
        self.validate_self_consistency()?;
        source_transitions_root_v2(&self.transfers)
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

    pub fn transfers(&self) -> &[ValueTransferV2] {
        &self.transfers
    }
}

impl<'de> Deserialize<'de> for ValueTransferSetV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ValueTransferSetWireV2::deserialize(deserializer)?;
        Self::from_parts(
            wire.set_version,
            wire.application_id,
            wire.chain_or_domain_id,
            wire.epoch_id,
            wire.transfers,
        )
        .map_err(de::Error::custom)
    }
}

fn serialize_transfers<S>(transfers: &[ValueTransferV2], serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    transfers.serialize(serializer)
}

fn deserialize_transfers<'de, D>(deserializer: D) -> Result<Vec<ValueTransferV2>, D::Error>
where
    D: Deserializer<'de>,
{
    deserializer.deserialize_seq(TransferVisitor::<ValueTransferV2> {
        marker: PhantomData,
    })
}

struct TransferVisitor<T> {
    marker: PhantomData<T>,
}

impl<'de, T> Visitor<'de> for TransferVisitor<T>
where
    T: Deserialize<'de>,
{
    type Value = Vec<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "1..={MAX_VALUE_TRANSFERS_PER_SET_V2} value transfers"
        )
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let declared = sequence.size_hint().unwrap_or(0);
        if declared > MAX_VALUE_TRANSFERS_PER_SET_V2 {
            return Err(de::Error::custom(ValueTransferErrorV2::TooManyTransfers {
                actual: declared,
                maximum: MAX_VALUE_TRANSFERS_PER_SET_V2,
            }));
        }
        let mut transfers = Vec::with_capacity(declared.min(MAX_VALUE_TRANSFERS_PER_SET_V2));
        while let Some(transfer) = sequence.next_element()? {
            if transfers.len() == MAX_VALUE_TRANSFERS_PER_SET_V2 {
                return Err(de::Error::custom(ValueTransferErrorV2::TooManyTransfers {
                    actual: MAX_VALUE_TRANSFERS_PER_SET_V2 + 1,
                    maximum: MAX_VALUE_TRANSFERS_PER_SET_V2,
                }));
            }
            transfers.push(transfer);
        }
        if transfers.is_empty() {
            return Err(de::Error::custom(ValueTransferErrorV2::EmptyTransfers));
        }
        Ok(transfers)
    }
}

fn require_transfer_count(count: usize) -> Result<(), ValueTransferErrorV2> {
    if count == 0 {
        return Err(ValueTransferErrorV2::EmptyTransfers);
    }
    if count > MAX_VALUE_TRANSFERS_PER_SET_V2 {
        return Err(ValueTransferErrorV2::TooManyTransfers {
            actual: count,
            maximum: MAX_VALUE_TRANSFERS_PER_SET_V2,
        });
    }
    Ok(())
}
