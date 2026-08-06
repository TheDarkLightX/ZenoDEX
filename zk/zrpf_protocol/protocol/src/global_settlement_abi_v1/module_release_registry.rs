use alloc::vec::Vec;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::{
    EconomicLaneIdV1, EconomicLaneRegistryEntryV1, LaneModuleReleaseIdV1,
    LaneModuleReleaseRegistryErrorV1, LaneModuleReleaseStatusV1, LaneModuleReleaseV1,
    LANE_MODULE_RELEASE_REGISTRY_VERSION_V1, MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1,
};
use crate::CommitmentV3;

const REGISTRY_ROOT_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.lane_module_release_registry.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaneModuleReleaseRegistryV1 {
    registry_version: u16,
    lane_id: EconomicLaneIdV1,
    releases: Vec<LaneModuleReleaseV1>,
}

impl LaneModuleReleaseRegistryV1 {
    pub fn new(
        lane_id: EconomicLaneIdV1,
        releases: Vec<LaneModuleReleaseV1>,
    ) -> Result<Self, LaneModuleReleaseRegistryErrorV1> {
        Self::from_parts(LANE_MODULE_RELEASE_REGISTRY_VERSION_V1, lane_id, releases)
    }

    pub(super) fn from_parts(
        registry_version: u16,
        lane_id: EconomicLaneIdV1,
        releases: Vec<LaneModuleReleaseV1>,
    ) -> Result<Self, LaneModuleReleaseRegistryErrorV1> {
        if registry_version != LANE_MODULE_RELEASE_REGISTRY_VERSION_V1 {
            return Err(LaneModuleReleaseRegistryErrorV1::InvalidRegistryVersion(
                registry_version,
            ));
        }
        validate_release_set(lane_id, &releases)?;
        Ok(Self {
            registry_version,
            lane_id,
            releases,
        })
    }

    pub const fn registry_version(&self) -> u16 {
        self.registry_version
    }

    pub const fn lane_id(&self) -> EconomicLaneIdV1 {
        self.lane_id
    }

    pub fn releases(&self) -> &[LaneModuleReleaseV1] {
        &self.releases
    }

    pub fn canonical_root(&self) -> Result<CommitmentV3, LaneModuleReleaseRegistryErrorV1> {
        validate_release_set(self.lane_id, &self.releases)?;
        let count = u16::try_from(self.releases.len())
            .map_err(|_| LaneModuleReleaseRegistryErrorV1::ArithmeticOverflow("release_count"))?;
        let domain_len = u16::try_from(REGISTRY_ROOT_DOMAIN_V1.len()).map_err(|_| {
            LaneModuleReleaseRegistryErrorV1::ArithmeticOverflow("hash_domain_length")
        })?;
        let mut hasher = Sha256::new();
        hasher.update(domain_len.to_be_bytes());
        hasher.update(REGISTRY_ROOT_DOMAIN_V1);
        hasher.update(self.registry_version.to_be_bytes());
        hasher.update([self.lane_id.code()]);
        hasher.update(count.to_be_bytes());
        for release in &self.releases {
            let commitment = release
                .canonical_record_commitment()
                .map_err(LaneModuleReleaseRegistryErrorV1::ReleaseAdmission)?;
            hasher.update(commitment.as_bytes());
        }
        CommitmentV3::new(hasher.finalize().into())
            .map_err(|_| LaneModuleReleaseRegistryErrorV1::InvalidDerivedCommitment)
    }

    pub fn resolve_new_object_release(
        &self,
    ) -> Result<&LaneModuleReleaseV1, LaneModuleReleaseRegistryErrorV1> {
        let release = self
            .releases
            .iter()
            .find(|release| release.status() == LaneModuleReleaseStatusV1::ActiveNew)
            .ok_or(LaneModuleReleaseRegistryErrorV1::NoActiveNewRelease)?;
        release
            .admit_new_object_creation()
            .map_err(LaneModuleReleaseRegistryErrorV1::ReleaseAdmission)?;
        Ok(release)
    }

    pub fn resolve_existing_object_release(
        &self,
        release_id: LaneModuleReleaseIdV1,
    ) -> Result<&LaneModuleReleaseV1, LaneModuleReleaseRegistryErrorV1> {
        let position = release_position(&self.releases, release_id)
            .ok_or(LaneModuleReleaseRegistryErrorV1::UnknownRelease(release_id))?;
        let release = &self.releases[position];
        release
            .admit_existing_object_transition()
            .map_err(LaneModuleReleaseRegistryErrorV1::ReleaseAdmission)?;
        Ok(release)
    }

    pub fn bind_global_lane_entry(
        &self,
        entry: &EconomicLaneRegistryEntryV1,
    ) -> Result<(), LaneModuleReleaseRegistryErrorV1> {
        if entry.lane_id() != self.lane_id {
            return Err(LaneModuleReleaseRegistryErrorV1::LaneEntryMismatch {
                expected: self.lane_id,
                actual: entry.lane_id(),
            });
        }
        if entry.module_release_registry_root() != self.canonical_root()? {
            return Err(LaneModuleReleaseRegistryErrorV1::RegistryRootMismatch);
        }
        Ok(())
    }
}

fn validate_release_set(
    lane_id: EconomicLaneIdV1,
    releases: &[LaneModuleReleaseV1],
) -> Result<(), LaneModuleReleaseRegistryErrorV1> {
    validate_count(releases.len())?;
    let mut active_new_count = 0usize;
    for (position, release) in releases.iter().enumerate() {
        let actual_lane = release.content().lane_id();
        if actual_lane != lane_id {
            return Err(LaneModuleReleaseRegistryErrorV1::MixedLane {
                position,
                expected: lane_id,
                actual: actual_lane,
            });
        }
        if releases[..position]
            .iter()
            .any(|earlier| earlier.release_id() == release.release_id())
        {
            return Err(LaneModuleReleaseRegistryErrorV1::DuplicateReleaseId(
                release.release_id(),
            ));
        }
        if position > 0 && releases[position - 1].release_id() > release.release_id() {
            return Err(LaneModuleReleaseRegistryErrorV1::NonCanonicalReleaseOrder { position });
        }
        if release.status() == LaneModuleReleaseStatusV1::ActiveNew {
            active_new_count += 1;
            if active_new_count > 1 {
                return Err(LaneModuleReleaseRegistryErrorV1::MultipleActiveNewReleases);
            }
        }
    }
    validate_predecessors(releases)
}

fn validate_count(count: usize) -> Result<(), LaneModuleReleaseRegistryErrorV1> {
    if count == 0 {
        return Err(LaneModuleReleaseRegistryErrorV1::EmptyRegistry);
    }
    if count > MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1 {
        return Err(LaneModuleReleaseRegistryErrorV1::TooManyReleases {
            actual: count,
            maximum: MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1,
        });
    }
    Ok(())
}

fn validate_predecessors(
    releases: &[LaneModuleReleaseV1],
) -> Result<(), LaneModuleReleaseRegistryErrorV1> {
    for release in releases {
        if let Some(predecessor_release_id) = release.content().migration().predecessor_release_id()
        {
            if release_position(releases, predecessor_release_id).is_none() {
                return Err(LaneModuleReleaseRegistryErrorV1::MissingPredecessor {
                    release_id: release.release_id(),
                    predecessor_release_id,
                });
            }
        }
    }
    for origin in 0..releases.len() {
        let mut visited = [false; MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1];
        let mut position = origin;
        loop {
            if visited[position] {
                return Err(LaneModuleReleaseRegistryErrorV1::PredecessorCycle(
                    releases[origin].release_id(),
                ));
            }
            visited[position] = true;
            let Some(predecessor_release_id) = releases[position]
                .content()
                .migration()
                .predecessor_release_id()
            else {
                break;
            };
            position = release_position(releases, predecessor_release_id).ok_or(
                LaneModuleReleaseRegistryErrorV1::MissingPredecessor {
                    release_id: releases[position].release_id(),
                    predecessor_release_id,
                },
            )?;
        }
    }
    Ok(())
}

fn release_position(
    releases: &[LaneModuleReleaseV1],
    release_id: LaneModuleReleaseIdV1,
) -> Option<usize> {
    releases
        .binary_search_by_key(&release_id, LaneModuleReleaseV1::release_id)
        .ok()
}
