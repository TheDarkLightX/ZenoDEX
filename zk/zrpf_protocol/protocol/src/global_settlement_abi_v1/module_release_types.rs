use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};

use super::{EconomicLaneIdV1, LaneModuleReleaseErrorV1, LaneModuleReleaseIdV1};
use crate::{CommitmentV3, ProgramIdV3};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LaneModuleReleaseStatusV1 {
    Candidate,
    Shadow,
    ActiveNew,
    DrainOnly,
    VerifyOnly,
    Retired,
    Revoked,
}

impl LaneModuleReleaseStatusV1 {
    pub const fn code(self) -> u8 {
        match self {
            Self::Candidate => 0,
            Self::Shadow => 1,
            Self::ActiveNew => 2,
            Self::DrainOnly => 3,
            Self::VerifyOnly => 4,
            Self::Retired => 5,
            Self::Revoked => 6,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TerminalCoverageStatusV1 {
    Incomplete,
    Complete,
}

impl TerminalCoverageStatusV1 {
    const fn code(self) -> u8 {
        match self {
            Self::Incomplete => 0,
            Self::Complete => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LaneModuleMigrationModeV1 {
    Genesis,
    CoexistAndDrain,
    ProvedBulkMigration,
}

impl LaneModuleMigrationModeV1 {
    const fn code(self) -> u8 {
        match self {
            Self::Genesis => 0,
            Self::CoexistAndDrain => 1,
            Self::ProvedBulkMigration => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaneModuleSchemaRootsV1 {
    state_schema_root: CommitmentV3,
    command_schema_root: CommitmentV3,
    effect_schema_root: CommitmentV3,
    private_port_schema_root: CommitmentV3,
}

impl LaneModuleSchemaRootsV1 {
    pub const fn new(
        state_schema_root: CommitmentV3,
        command_schema_root: CommitmentV3,
        effect_schema_root: CommitmentV3,
        private_port_schema_root: CommitmentV3,
    ) -> Self {
        Self {
            state_schema_root,
            command_schema_root,
            effect_schema_root,
            private_port_schema_root,
        }
    }

    pub(super) fn update_hasher(self, hasher: &mut Sha256) {
        update_commitment(hasher, self.state_schema_root);
        update_commitment(hasher, self.command_schema_root);
        update_commitment(hasher, self.effect_schema_root);
        update_commitment(hasher, self.private_port_schema_root);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaneModuleProvenanceRootsV1 {
    guest_image_id: ProgramIdV3,
    spec_root: CommitmentV3,
    source_root: CommitmentV3,
    toolchain_root: CommitmentV3,
}

impl LaneModuleProvenanceRootsV1 {
    pub const fn new(
        guest_image_id: ProgramIdV3,
        spec_root: CommitmentV3,
        source_root: CommitmentV3,
        toolchain_root: CommitmentV3,
    ) -> Self {
        Self {
            guest_image_id,
            spec_root,
            source_root,
            toolchain_root,
        }
    }

    pub(super) fn update_hasher(self, hasher: &mut Sha256) {
        hasher.update(self.guest_image_id.as_bytes());
        update_commitment(hasher, self.spec_root);
        update_commitment(hasher, self.source_root);
        update_commitment(hasher, self.toolchain_root);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaneModuleTerminalCoverageV1 {
    status: TerminalCoverageStatusV1,
    terminal_coverage_root: CommitmentV3,
}

impl LaneModuleTerminalCoverageV1 {
    pub const fn new(
        status: TerminalCoverageStatusV1,
        terminal_coverage_root: CommitmentV3,
    ) -> Self {
        Self {
            status,
            terminal_coverage_root,
        }
    }

    pub const fn status(self) -> TerminalCoverageStatusV1 {
        self.status
    }

    pub(super) fn update_hasher(self, hasher: &mut Sha256) {
        hasher.update([self.status.code()]);
        update_commitment(hasher, self.terminal_coverage_root);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct LaneModuleMigrationCompatibilityV1 {
    mode: LaneModuleMigrationModeV1,
    predecessor_release_id: Option<LaneModuleReleaseIdV1>,
    compatibility_root: CommitmentV3,
}

impl LaneModuleMigrationCompatibilityV1 {
    pub fn new(
        mode: LaneModuleMigrationModeV1,
        predecessor_release_id: Option<LaneModuleReleaseIdV1>,
        compatibility_root: CommitmentV3,
    ) -> Result<Self, LaneModuleReleaseErrorV1> {
        validate_migration_predecessor(mode, predecessor_release_id)?;
        Ok(Self {
            mode,
            predecessor_release_id,
            compatibility_root,
        })
    }

    pub const fn predecessor_release_id(self) -> Option<LaneModuleReleaseIdV1> {
        self.predecessor_release_id
    }

    pub(super) fn update_hasher(self, hasher: &mut Sha256) {
        hasher.update([self.mode.code()]);
        match self.predecessor_release_id {
            None => hasher.update([0]),
            Some(release_id) => {
                hasher.update([1]);
                hasher.update(release_id.as_bytes());
            }
        }
        update_commitment(hasher, self.compatibility_root);
    }
}

impl<'de> Deserialize<'de> for LaneModuleMigrationCompatibilityV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct Wire {
            mode: LaneModuleMigrationModeV1,
            predecessor_release_id: Option<LaneModuleReleaseIdV1>,
            compatibility_root: CommitmentV3,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::new(
            wire.mode,
            wire.predecessor_release_id,
            wire.compatibility_root,
        )
        .map_err(de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct LaneModuleResourceLimitsV1 {
    max_command_bytes: u32,
    max_state_bytes: u32,
    max_journal_bytes: u32,
    max_cycles: u64,
}

impl LaneModuleResourceLimitsV1 {
    pub fn new(
        max_command_bytes: u32,
        max_state_bytes: u32,
        max_journal_bytes: u32,
        max_cycles: u64,
    ) -> Result<Self, LaneModuleReleaseErrorV1> {
        require_nonzero(max_command_bytes, "max_command_bytes")?;
        require_nonzero(max_state_bytes, "max_state_bytes")?;
        require_nonzero(max_journal_bytes, "max_journal_bytes")?;
        if max_cycles == 0 {
            return Err(LaneModuleReleaseErrorV1::ZeroResourceLimit("max_cycles"));
        }
        Ok(Self {
            max_command_bytes,
            max_state_bytes,
            max_journal_bytes,
            max_cycles,
        })
    }

    pub const fn max_command_bytes(self) -> u32 {
        self.max_command_bytes
    }

    pub const fn max_state_bytes(self) -> u32 {
        self.max_state_bytes
    }

    pub const fn max_journal_bytes(self) -> u32 {
        self.max_journal_bytes
    }

    pub const fn max_cycles(self) -> u64 {
        self.max_cycles
    }

    pub(super) fn update_hasher(self, hasher: &mut Sha256) {
        hasher.update(self.max_command_bytes.to_be_bytes());
        hasher.update(self.max_state_bytes.to_be_bytes());
        hasher.update(self.max_journal_bytes.to_be_bytes());
        hasher.update(self.max_cycles.to_be_bytes());
    }
}

impl<'de> Deserialize<'de> for LaneModuleResourceLimitsV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct Wire {
            max_command_bytes: u32,
            max_state_bytes: u32,
            max_journal_bytes: u32,
            max_cycles: u64,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::new(
            wire.max_command_bytes,
            wire.max_state_bytes,
            wire.max_journal_bytes,
            wire.max_cycles,
        )
        .map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaneModuleReleaseContentV1 {
    lane_id: EconomicLaneIdV1,
    schemas: LaneModuleSchemaRootsV1,
    command_variants_root: CommitmentV3,
    provenance: LaneModuleProvenanceRootsV1,
    terminal: LaneModuleTerminalCoverageV1,
    migration: LaneModuleMigrationCompatibilityV1,
    resource_limits: LaneModuleResourceLimitsV1,
}

impl LaneModuleReleaseContentV1 {
    pub const fn new(
        lane_id: EconomicLaneIdV1,
        schemas: LaneModuleSchemaRootsV1,
        command_variants_root: CommitmentV3,
        provenance: LaneModuleProvenanceRootsV1,
        terminal: LaneModuleTerminalCoverageV1,
        migration: LaneModuleMigrationCompatibilityV1,
        resource_limits: LaneModuleResourceLimitsV1,
    ) -> Self {
        Self {
            lane_id,
            schemas,
            command_variants_root,
            provenance,
            terminal,
            migration,
            resource_limits,
        }
    }

    pub const fn lane_id(&self) -> EconomicLaneIdV1 {
        self.lane_id
    }

    pub const fn terminal(&self) -> LaneModuleTerminalCoverageV1 {
        self.terminal
    }

    pub const fn resource_limits(&self) -> LaneModuleResourceLimitsV1 {
        self.resource_limits
    }

    pub(super) const fn migration(&self) -> LaneModuleMigrationCompatibilityV1 {
        self.migration
    }

    pub(super) fn update_hasher(&self, hasher: &mut Sha256) {
        hasher.update([self.lane_id.code()]);
        self.schemas.update_hasher(hasher);
        update_commitment(hasher, self.command_variants_root);
        self.provenance.update_hasher(hasher);
        self.terminal.update_hasher(hasher);
        self.migration.update_hasher(hasher);
        self.resource_limits.update_hasher(hasher);
    }
}

fn validate_migration_predecessor(
    mode: LaneModuleMigrationModeV1,
    predecessor_release_id: Option<LaneModuleReleaseIdV1>,
) -> Result<(), LaneModuleReleaseErrorV1> {
    match (mode, predecessor_release_id) {
        (LaneModuleMigrationModeV1::Genesis, None) => Ok(()),
        (LaneModuleMigrationModeV1::Genesis, Some(_)) => {
            Err(LaneModuleReleaseErrorV1::UnexpectedMigrationPredecessor)
        }
        (LaneModuleMigrationModeV1::CoexistAndDrain, Some(_))
        | (LaneModuleMigrationModeV1::ProvedBulkMigration, Some(_)) => Ok(()),
        (mode, None) => Err(LaneModuleReleaseErrorV1::MissingMigrationPredecessor(mode)),
    }
}

fn require_nonzero(value: u32, field: &'static str) -> Result<(), LaneModuleReleaseErrorV1> {
    if value == 0 {
        return Err(LaneModuleReleaseErrorV1::ZeroResourceLimit(field));
    }
    Ok(())
}

fn update_commitment(hasher: &mut Sha256, commitment: CommitmentV3) {
    hasher.update(commitment.as_bytes());
}
