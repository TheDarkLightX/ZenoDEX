use alloc::vec::Vec;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::{
    EconomicLaneCommandStatusV1, EconomicLaneIdV1, GlobalSettlementAbiErrorV1,
    ECONOMIC_LANE_COUNT_V1, GLOBAL_ECONOMIC_LANE_REGISTRY_VERSION_V1,
};
use crate::CommitmentV3;

const REGISTRY_COMMITMENT_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.economic_lane_registry.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
pub struct EconomicLaneRegistryEntryV1 {
    lane_id: EconomicLaneIdV1,
    command_status: EconomicLaneCommandStatusV1,
    module_release_registry_root: CommitmentV3,
}

impl EconomicLaneRegistryEntryV1 {
    pub const fn new(
        lane_id: EconomicLaneIdV1,
        command_status: EconomicLaneCommandStatusV1,
        module_release_registry_root: CommitmentV3,
    ) -> Self {
        Self {
            lane_id,
            command_status,
            module_release_registry_root,
        }
    }

    pub const fn lane_id(self) -> EconomicLaneIdV1 {
        self.lane_id
    }

    pub const fn command_status(self) -> EconomicLaneCommandStatusV1 {
        self.command_status
    }

    pub const fn module_release_registry_root(self) -> CommitmentV3 {
        self.module_release_registry_root
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GlobalEconomicLaneRegistryV1 {
    registry_version: u16,
    entries: Vec<EconomicLaneRegistryEntryV1>,
}

impl GlobalEconomicLaneRegistryV1 {
    pub fn new(
        entries: Vec<EconomicLaneRegistryEntryV1>,
    ) -> Result<Self, GlobalSettlementAbiErrorV1> {
        Self::from_parts(GLOBAL_ECONOMIC_LANE_REGISTRY_VERSION_V1, entries)
    }

    pub(super) fn from_parts(
        registry_version: u16,
        entries: Vec<EconomicLaneRegistryEntryV1>,
    ) -> Result<Self, GlobalSettlementAbiErrorV1> {
        if registry_version != GLOBAL_ECONOMIC_LANE_REGISTRY_VERSION_V1 {
            return Err(GlobalSettlementAbiErrorV1::InvalidRegistryVersion(
                registry_version,
            ));
        }
        validate_entry_set(&entries)?;
        Ok(Self {
            registry_version,
            entries,
        })
    }

    pub const fn registry_version(&self) -> u16 {
        self.registry_version
    }

    pub fn entries(&self) -> &[EconomicLaneRegistryEntryV1] {
        &self.entries
    }

    pub fn resolve_new_command_lane(
        &self,
        lane_identifier: &str,
    ) -> Result<EconomicLaneIdV1, GlobalSettlementAbiErrorV1> {
        let lane_id = EconomicLaneIdV1::parse_exact(lane_identifier)?;
        let entry = self
            .entries
            .iter()
            .find(|entry| entry.lane_id == lane_id)
            .ok_or(GlobalSettlementAbiErrorV1::RegistryInvariantViolation)?;
        if entry.command_status == EconomicLaneCommandStatusV1::Disabled {
            return Err(GlobalSettlementAbiErrorV1::LaneDisabled(lane_id));
        }
        Ok(lane_id)
    }

    pub fn canonical_commitment(&self) -> Result<CommitmentV3, GlobalSettlementAbiErrorV1> {
        validate_entry_set(&self.entries)?;
        let entry_count = u16::try_from(self.entries.len()).map_err(|_| {
            GlobalSettlementAbiErrorV1::ArithmeticOverflow("economic_lane_entry_count")
        })?;
        let mut hasher = prefixed_domain_hasher(REGISTRY_COMMITMENT_DOMAIN_V1)?;
        hasher.update(self.registry_version.to_be_bytes());
        hasher.update(entry_count.to_be_bytes());
        for entry in &self.entries {
            hasher.update([entry.lane_id.code()]);
            hasher.update([entry.command_status.code()]);
            hasher.update(entry.module_release_registry_root.as_bytes());
        }
        CommitmentV3::new(hasher.finalize().into()).map_err(|_| {
            GlobalSettlementAbiErrorV1::InvalidDerivedCommitment("economic_lane_registry")
        })
    }
}

fn validate_entry_set(
    entries: &[EconomicLaneRegistryEntryV1],
) -> Result<(), GlobalSettlementAbiErrorV1> {
    if entries.len() != ECONOMIC_LANE_COUNT_V1 {
        return Err(GlobalSettlementAbiErrorV1::WrongLaneCount {
            actual: entries.len(),
            expected: ECONOMIC_LANE_COUNT_V1,
        });
    }
    for (position, entry) in entries.iter().enumerate() {
        if entries[..position]
            .iter()
            .any(|earlier| earlier.lane_id == entry.lane_id)
        {
            return Err(GlobalSettlementAbiErrorV1::DuplicateLane(entry.lane_id));
        }
    }
    for (position, (entry, expected)) in
        entries.iter().zip(EconomicLaneIdV1::ALL.iter()).enumerate()
    {
        if entry.lane_id != *expected {
            return Err(GlobalSettlementAbiErrorV1::NonCanonicalLaneOrder {
                position,
                expected: *expected,
                actual: entry.lane_id,
            });
        }
    }
    Ok(())
}

fn prefixed_domain_hasher(domain: &[u8]) -> Result<Sha256, GlobalSettlementAbiErrorV1> {
    let domain_len = u16::try_from(domain.len())
        .map_err(|_| GlobalSettlementAbiErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(domain_len.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}
