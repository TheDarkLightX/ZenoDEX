use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};

use super::{EconomicProfileIdV1, EconomicProfileSnapshotErrorV1};
use crate::CommitmentV3;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EconomicProfileTransitionModeV1 {
    Genesis,
    GovernanceUpdate,
    ProvedMigration,
}

impl EconomicProfileTransitionModeV1 {
    pub const fn code(self) -> u8 {
        match self {
            Self::Genesis => 0,
            Self::GovernanceUpdate => 1,
            Self::ProvedMigration => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicProfileRegistryRootsV1 {
    economic_lane_registry_root: CommitmentV3,
    route_release_registry_root: CommitmentV3,
    proof_shape_registry_root: CommitmentV3,
    verifier_registry_root: CommitmentV3,
    migration_registry_root: CommitmentV3,
    policy_registry_root: CommitmentV3,
    terminal_registry_root: CommitmentV3,
}

impl EconomicProfileRegistryRootsV1 {
    pub const fn new(
        economic_lane_registry_root: CommitmentV3,
        route_release_registry_root: CommitmentV3,
        proof_shape_registry_root: CommitmentV3,
        verifier_registry_root: CommitmentV3,
        migration_registry_root: CommitmentV3,
        policy_registry_root: CommitmentV3,
        terminal_registry_root: CommitmentV3,
    ) -> Self {
        Self {
            economic_lane_registry_root,
            route_release_registry_root,
            proof_shape_registry_root,
            verifier_registry_root,
            migration_registry_root,
            policy_registry_root,
            terminal_registry_root,
        }
    }

    pub const fn economic_lane_registry_root(self) -> CommitmentV3 {
        self.economic_lane_registry_root
    }

    pub const fn route_release_registry_root(self) -> CommitmentV3 {
        self.route_release_registry_root
    }

    pub const fn proof_shape_registry_root(self) -> CommitmentV3 {
        self.proof_shape_registry_root
    }

    pub const fn verifier_registry_root(self) -> CommitmentV3 {
        self.verifier_registry_root
    }

    pub const fn migration_registry_root(self) -> CommitmentV3 {
        self.migration_registry_root
    }

    pub const fn policy_registry_root(self) -> CommitmentV3 {
        self.policy_registry_root
    }

    pub const fn terminal_registry_root(self) -> CommitmentV3 {
        self.terminal_registry_root
    }

    pub(super) fn update_hasher(self, hasher: &mut Sha256) {
        for root in [
            self.economic_lane_registry_root,
            self.route_release_registry_root,
            self.proof_shape_registry_root,
            self.verifier_registry_root,
            self.migration_registry_root,
            self.policy_registry_root,
            self.terminal_registry_root,
        ] {
            hasher.update(root.as_bytes());
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EconomicProfileSnapshotContentV1 {
    authority_epoch: u64,
    writer_epoch: u64,
    transition_mode: EconomicProfileTransitionModeV1,
    predecessor_profile_id: Option<EconomicProfileIdV1>,
    registry_roots: EconomicProfileRegistryRootsV1,
}

impl EconomicProfileSnapshotContentV1 {
    pub fn new(
        authority_epoch: u64,
        writer_epoch: u64,
        transition_mode: EconomicProfileTransitionModeV1,
        predecessor_profile_id: Option<EconomicProfileIdV1>,
        registry_roots: EconomicProfileRegistryRootsV1,
    ) -> Result<Self, EconomicProfileSnapshotErrorV1> {
        validate_predecessor(transition_mode, predecessor_profile_id)?;
        Ok(Self {
            authority_epoch,
            writer_epoch,
            transition_mode,
            predecessor_profile_id,
            registry_roots,
        })
    }

    pub const fn authority_epoch(&self) -> u64 {
        self.authority_epoch
    }

    pub const fn writer_epoch(&self) -> u64 {
        self.writer_epoch
    }

    pub const fn transition_mode(&self) -> EconomicProfileTransitionModeV1 {
        self.transition_mode
    }

    pub const fn predecessor_profile_id(&self) -> Option<EconomicProfileIdV1> {
        self.predecessor_profile_id
    }

    pub const fn registry_roots(&self) -> EconomicProfileRegistryRootsV1 {
        self.registry_roots
    }

    pub(super) fn update_hasher(&self, hasher: &mut Sha256) {
        hasher.update(self.authority_epoch.to_be_bytes());
        hasher.update(self.writer_epoch.to_be_bytes());
        hasher.update([self.transition_mode.code()]);
        match self.predecessor_profile_id {
            Some(predecessor) => {
                hasher.update([1]);
                hasher.update(predecessor.as_bytes());
            }
            None => hasher.update([0]),
        }
        self.registry_roots.update_hasher(hasher);
    }
}

impl<'de> Deserialize<'de> for EconomicProfileSnapshotContentV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            authority_epoch: u64,
            writer_epoch: u64,
            transition_mode: EconomicProfileTransitionModeV1,
            predecessor_profile_id: Option<EconomicProfileIdV1>,
            registry_roots: EconomicProfileRegistryRootsV1,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::new(
            wire.authority_epoch,
            wire.writer_epoch,
            wire.transition_mode,
            wire.predecessor_profile_id,
            wire.registry_roots,
        )
        .map_err(de::Error::custom)
    }
}

fn validate_predecessor(
    mode: EconomicProfileTransitionModeV1,
    predecessor: Option<EconomicProfileIdV1>,
) -> Result<(), EconomicProfileSnapshotErrorV1> {
    match (mode, predecessor) {
        (EconomicProfileTransitionModeV1::Genesis, Some(_)) => {
            Err(EconomicProfileSnapshotErrorV1::GenesisHasPredecessor)
        }
        (EconomicProfileTransitionModeV1::Genesis, None) => Ok(()),
        (_, Some(_)) => Ok(()),
        (transition_mode, None) => {
            Err(EconomicProfileSnapshotErrorV1::TransitionRequiresPredecessor(transition_mode))
        }
    }
}
