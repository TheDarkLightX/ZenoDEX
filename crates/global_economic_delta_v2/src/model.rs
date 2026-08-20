use serde::{de::Error as _, Deserialize, Deserializer, Serialize};

use crate::{
    reject_v2, require_delta_atoms_v2, require_distinct_locations_v2, validate_liability_v2,
    validate_slash_v2, DeltaRejectCodeV2, DeltaResultV2,
};

const MAX_ID_BYTES_V2: usize = 128;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub(crate) struct CanonicalIdV2(String);

impl CanonicalIdV2 {
    fn parse(value: String) -> Result<Self, &'static str> {
        let bytes = value.as_bytes();
        if bytes.is_empty() || bytes.len() > MAX_ID_BYTES_V2 {
            return Err("canonical ID length is invalid");
        }
        if !bytes[0].is_ascii_lowercase() && !bytes[0].is_ascii_digit() {
            return Err("canonical ID prefix is invalid");
        }
        if !bytes.iter().all(|byte| {
            byte.is_ascii_lowercase()
                || byte.is_ascii_digit()
                || matches!(byte, b'.' | b'_' | b':' | b'-')
        }) {
            return Err("canonical ID alphabet is invalid");
        }
        Ok(Self(value))
    }
}

impl<'de> Deserialize<'de> for CanonicalIdV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        Self::parse(value).map_err(D::Error::custom)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub(crate) struct RootV2(String);

impl RootV2 {
    fn parse(value: String) -> Result<Self, &'static str> {
        let Some(payload) = value.strip_prefix("sha256:") else {
            return Err("root domain is invalid");
        };
        if payload.len() != 64
            || payload.bytes().all(|byte| byte == b'0')
            || !payload
                .as_bytes()
                .iter()
                .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
        {
            return Err("root encoding is invalid");
        }
        Ok(Self(value))
    }

    fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for RootV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = String::deserialize(deserializer)?;
        Self::parse(value).map_err(D::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum LiabilityDirectionV2 {
    Increase,
    Decrease,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SourceKindV2 {
    ExternalEffect,
    AncestorClaim,
    RefundableEvent,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub(crate) struct JsonAtomsV2(serde_json::Number);

impl<'de> Deserialize<'de> for JsonAtomsV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = serde_json::Number::deserialize(deserializer)?;
        if value.is_f64() {
            return Err(D::Error::custom("atom value must be a JSON integer"));
        }
        Ok(Self(value))
    }
}

impl JsonAtomsV2 {
    fn as_u128(&self) -> DeltaResultV2<u128> {
        self.0.as_u128().ok_or_else(|| {
            reject_v2(
                DeltaRejectCodeV2::AmountOutOfRange,
                "atom value must be one nonnegative JSON integer",
            )
        })
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct SourceBindingV2 {
    source_root: RootV2,
    source_kind: SourceKindV2,
    asset: CanonicalIdV2,
    amount_atoms: JsonAtomsV2,
}

impl SourceBindingV2 {
    pub(crate) fn root(&self) -> &str {
        self.source_root.as_str()
    }

    pub(crate) fn kind(&self) -> SourceKindV2 {
        self.source_kind
    }

    pub(crate) fn asset(&self) -> &CanonicalIdV2 {
        &self.asset
    }

    pub(crate) fn amount_atoms(&self) -> DeltaResultV2<u128> {
        self.amount_atoms.as_u128()
    }

    pub(crate) fn validate(&self) -> DeltaResultV2<()> {
        require_delta_atoms_v2(self.amount_atoms()?)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "delta_class", rename_all = "snake_case", deny_unknown_fields)]
pub(crate) enum EconomicDeltaV2 {
    InternalTransfer {
        economic_event: RootV2,
        asset: CanonicalIdV2,
        amount_atoms: JsonAtomsV2,
        source_owner: CanonicalIdV2,
        destination_owner: CanonicalIdV2,
        source_ledger_allocation: CanonicalIdV2,
        destination_ledger_allocation: CanonicalIdV2,
    },
    Mint {
        economic_event: RootV2,
        asset: CanonicalIdV2,
        amount_atoms: JsonAtomsV2,
        issuer_authority: CanonicalIdV2,
        recipient_owner: CanonicalIdV2,
        recipient_ledger_allocation: CanonicalIdV2,
    },
    Burn {
        economic_event: RootV2,
        asset: CanonicalIdV2,
        amount_atoms: JsonAtomsV2,
        burn_authority: CanonicalIdV2,
        source_owner: CanonicalIdV2,
        source_ledger_allocation: CanonicalIdV2,
    },
    Liability {
        economic_event: RootV2,
        asset: CanonicalIdV2,
        amount_atoms: JsonAtomsV2,
        liability_owner: CanonicalIdV2,
        liability_kind: CanonicalIdV2,
        direction: LiabilityDirectionV2,
        pre_atoms: JsonAtomsV2,
        post_atoms: JsonAtomsV2,
    },
    ExternalIn {
        economic_event: RootV2,
        asset: CanonicalIdV2,
        amount_atoms: JsonAtomsV2,
        source_effect: RootV2,
        destination_owner: CanonicalIdV2,
        destination_ledger_allocation: CanonicalIdV2,
    },
    ExternalOut {
        economic_event: RootV2,
        asset: CanonicalIdV2,
        amount_atoms: JsonAtomsV2,
        source_owner: CanonicalIdV2,
        source_ledger_allocation: CanonicalIdV2,
        ancestor_claim_event: RootV2,
        destination_effect: RootV2,
    },
    Refund {
        economic_event: RootV2,
        asset: CanonicalIdV2,
        amount_atoms: JsonAtomsV2,
        source_event: RootV2,
        source_owner: CanonicalIdV2,
        source_ledger_allocation: CanonicalIdV2,
        refund_owner: CanonicalIdV2,
        refund_ledger_allocation: CanonicalIdV2,
    },
    Slash {
        economic_event: RootV2,
        asset: CanonicalIdV2,
        amount_atoms: JsonAtomsV2,
        slashing_authority: CanonicalIdV2,
        slashed_owner: CanonicalIdV2,
        source_ledger_allocation: CanonicalIdV2,
        beneficiary_owner: CanonicalIdV2,
        beneficiary_ledger_allocation: CanonicalIdV2,
        beneficiary_atoms: JsonAtomsV2,
        residue_owner: CanonicalIdV2,
        residue_ledger_allocation: CanonicalIdV2,
        residue_atoms: JsonAtomsV2,
    },
}

impl EconomicDeltaV2 {
    pub(crate) fn event_id(&self) -> &str {
        match self {
            Self::InternalTransfer { economic_event, .. }
            | Self::Mint { economic_event, .. }
            | Self::Burn { economic_event, .. }
            | Self::Liability { economic_event, .. }
            | Self::ExternalIn { economic_event, .. }
            | Self::ExternalOut { economic_event, .. }
            | Self::Refund { economic_event, .. }
            | Self::Slash { economic_event, .. } => economic_event.as_str(),
        }
    }

    pub(crate) fn amount_atoms(&self) -> DeltaResultV2<u128> {
        match self {
            Self::InternalTransfer { amount_atoms, .. }
            | Self::Mint { amount_atoms, .. }
            | Self::Burn { amount_atoms, .. }
            | Self::Liability { amount_atoms, .. }
            | Self::ExternalIn { amount_atoms, .. }
            | Self::ExternalOut { amount_atoms, .. }
            | Self::Refund { amount_atoms, .. }
            | Self::Slash { amount_atoms, .. } => amount_atoms.as_u128(),
        }
    }

    pub(crate) fn class_name(&self) -> &'static str {
        match self {
            Self::InternalTransfer { .. } => "internal_transfer",
            Self::Mint { .. } => "mint",
            Self::Burn { .. } => "burn",
            Self::Liability { .. } => "liability",
            Self::ExternalIn { .. } => "external_in",
            Self::ExternalOut { .. } => "external_out",
            Self::Refund { .. } => "refund",
            Self::Slash { .. } => "slash",
        }
    }

    pub(crate) fn source_reference(&self) -> Option<(&str, SourceKindV2, &CanonicalIdV2)> {
        match self {
            Self::ExternalIn {
                source_effect,
                asset,
                ..
            } => Some((source_effect.as_str(), SourceKindV2::ExternalEffect, asset)),
            Self::ExternalOut {
                ancestor_claim_event,
                asset,
                ..
            } => Some((
                ancestor_claim_event.as_str(),
                SourceKindV2::AncestorClaim,
                asset,
            )),
            Self::Refund {
                source_event,
                asset,
                ..
            } => Some((source_event.as_str(), SourceKindV2::RefundableEvent, asset)),
            _ => None,
        }
    }

    pub(crate) fn destination_effect(&self) -> Option<&str> {
        match self {
            Self::ExternalOut {
                destination_effect, ..
            } => Some(destination_effect.as_str()),
            _ => None,
        }
    }

    pub(crate) fn validate(&self) -> DeltaResultV2<()> {
        let amount_atoms = self.amount_atoms()?;
        require_delta_atoms_v2(amount_atoms)?;
        match self {
            Self::InternalTransfer {
                source_owner,
                destination_owner,
                source_ledger_allocation,
                destination_ledger_allocation,
                ..
            } => require_distinct_locations_v2(
                source_owner,
                source_ledger_allocation,
                destination_owner,
                destination_ledger_allocation,
            ),
            Self::Liability {
                direction,
                pre_atoms,
                post_atoms,
                ..
            } => validate_liability_v2(
                amount_atoms,
                *direction,
                pre_atoms.as_u128()?,
                post_atoms.as_u128()?,
            ),
            Self::ExternalIn {
                economic_event,
                source_effect,
                ..
            } => require_distinct_roots_v2(
                &[economic_event, source_effect],
                "external ingress event cannot cite itself",
            ),
            Self::ExternalOut {
                economic_event,
                ancestor_claim_event,
                destination_effect,
                ..
            } => require_distinct_roots_v2(
                &[economic_event, ancestor_claim_event, destination_effect],
                "external egress event, ancestor, and destination must differ",
            ),
            Self::Refund {
                economic_event,
                source_event,
                source_owner,
                source_ledger_allocation,
                refund_owner,
                refund_ledger_allocation,
                ..
            } => {
                require_distinct_locations_v2(
                    source_owner,
                    source_ledger_allocation,
                    refund_owner,
                    refund_ledger_allocation,
                )?;
                require_distinct_roots_v2(
                    &[economic_event, source_event],
                    "refund event cannot cite itself",
                )
            }
            Self::Slash {
                beneficiary_atoms,
                residue_atoms,
                ..
            } => validate_slash_v2(
                amount_atoms,
                beneficiary_atoms.as_u128()?,
                residue_atoms.as_u128()?,
            ),
            _ => Ok(()),
        }
    }
}

fn require_distinct_roots_v2(roots: &[&RootV2], detail: &'static str) -> DeltaResultV2<()> {
    for (index, root) in roots.iter().enumerate() {
        if roots[..index].contains(root) {
            return Err(reject_v2(DeltaRejectCodeV2::SelfReferentialEvent, detail));
        }
    }
    Ok(())
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RawDeltaPlanV2 {
    pub(crate) schema: String,
    pub(crate) source_bindings: Vec<SourceBindingV2>,
    pub(crate) events: Vec<EconomicDeltaV2>,
}
