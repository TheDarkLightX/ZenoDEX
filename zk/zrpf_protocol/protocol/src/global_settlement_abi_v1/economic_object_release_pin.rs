use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};

use super::{
    EconomicLaneIdV1, GlobalEconomicStateErrorV1, LaneModuleReleaseIdV1,
    ECONOMIC_OBJECT_RELEASE_PIN_VERSION_V1,
};
use crate::{derive_sparse_merkle_root_v1, CommitmentV3, SparseMerkleSiblingPathV1, ValueHashV2};

const OBJECT_RELEASE_PIN_VALUE_DOMAIN_V1: &[u8] =
    b"zenodex.global_settlement.economic_object_release_pin_value.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[must_use = "the release pin must be committed into the object-release registry"]
pub struct EconomicObjectReleasePinV1 {
    pin_version: u16,
    object_id: CommitmentV3,
    lane_id: EconomicLaneIdV1,
    creating_release_id: LaneModuleReleaseIdV1,
}

impl EconomicObjectReleasePinV1 {
    pub const fn new(
        object_id: CommitmentV3,
        lane_id: EconomicLaneIdV1,
        creating_release_id: LaneModuleReleaseIdV1,
    ) -> Self {
        Self {
            pin_version: ECONOMIC_OBJECT_RELEASE_PIN_VERSION_V1,
            object_id,
            lane_id,
            creating_release_id,
        }
    }

    pub(super) fn from_parts(
        pin_version: u16,
        object_id: CommitmentV3,
        lane_id: EconomicLaneIdV1,
        creating_release_id: LaneModuleReleaseIdV1,
    ) -> Result<Self, GlobalEconomicStateErrorV1> {
        if pin_version != ECONOMIC_OBJECT_RELEASE_PIN_VERSION_V1 {
            return Err(GlobalEconomicStateErrorV1::InvalidObjectReleasePinVersion(
                pin_version,
            ));
        }
        Ok(Self {
            pin_version,
            object_id,
            lane_id,
            creating_release_id,
        })
    }

    pub const fn pin_version(self) -> u16 {
        self.pin_version
    }

    pub const fn object_id(self) -> CommitmentV3 {
        self.object_id
    }

    pub const fn lane_id(self) -> EconomicLaneIdV1 {
        self.lane_id
    }

    pub const fn creating_release_id(self) -> LaneModuleReleaseIdV1 {
        self.creating_release_id
    }

    pub fn value_hash(self) -> Result<ValueHashV2, GlobalEconomicStateErrorV1> {
        let domain_len = u16::try_from(OBJECT_RELEASE_PIN_VALUE_DOMAIN_V1.len()).map_err(|_| {
            GlobalEconomicStateErrorV1::ArithmeticOverflow("pin_hash_domain_length")
        })?;
        let mut hasher = Sha256::new();
        hasher.update(domain_len.to_be_bytes());
        hasher.update(OBJECT_RELEASE_PIN_VALUE_DOMAIN_V1);
        hasher.update(self.pin_version.to_be_bytes());
        hasher.update(self.object_id.as_bytes());
        hasher.update([self.lane_id.code()]);
        hasher.update(self.creating_release_id.as_bytes());
        Ok(ValueHashV2::new(hasher.finalize().into()))
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct EconomicObjectReleasePinWireV1 {
    pub pin_version: u16,
    pub object_id: CommitmentV3,
    pub lane_id: EconomicLaneIdV1,
    pub creating_release_id: LaneModuleReleaseIdV1,
}

impl<'de> Deserialize<'de> for EconomicObjectReleasePinV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = EconomicObjectReleasePinWireV1::deserialize(deserializer)?;
        Self::from_parts(
            wire.pin_version,
            wire.object_id,
            wire.lane_id,
            wire.creating_release_id,
        )
        .map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[must_use = "the release-pin proof must be checked against the committed registry root"]
pub struct EconomicObjectReleasePinProofV1 {
    pin: EconomicObjectReleasePinV1,
    sibling_commitments: SparseMerkleSiblingPathV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct EconomicObjectReleasePinProofWireV1 {
    pub pin: EconomicObjectReleasePinWireV1,
    pub sibling_commitments: SparseMerkleSiblingPathV1,
}

impl EconomicObjectReleasePinProofV1 {
    pub fn new(
        pin: EconomicObjectReleasePinV1,
        sibling_commitments: SparseMerkleSiblingPathV1,
    ) -> Result<Self, GlobalEconomicStateErrorV1> {
        let pin = EconomicObjectReleasePinV1::from_parts(
            pin.pin_version(),
            pin.object_id(),
            pin.lane_id(),
            pin.creating_release_id(),
        )?;
        Ok(Self {
            pin,
            sibling_commitments,
        })
    }

    pub const fn pin(&self) -> EconomicObjectReleasePinV1 {
        self.pin
    }

    pub const fn sibling_commitments(&self) -> &SparseMerkleSiblingPathV1 {
        &self.sibling_commitments
    }

    pub fn derive_registry_root(&self) -> Result<CommitmentV3, GlobalEconomicStateErrorV1> {
        derive_sparse_merkle_root_v1(
            self.pin.object_id(),
            self.pin.value_hash()?,
            &self.sibling_commitments,
        )
        .map_err(GlobalEconomicStateErrorV1::ObjectPinMerkle)
    }
}

impl<'de> Deserialize<'de> for EconomicObjectReleasePinProofV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = EconomicObjectReleasePinProofWireV1::deserialize(deserializer)?;
        let pin = EconomicObjectReleasePinV1::from_parts(
            wire.pin.pin_version,
            wire.pin.object_id,
            wire.pin.lane_id,
            wire.pin.creating_release_id,
        )
        .map_err(de::Error::custom)?;
        Self::new(pin, wire.sibling_commitments).map_err(de::Error::custom)
    }
}
