use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};

use super::{
    LaneModuleReleaseContentV1, LaneModuleReleaseErrorV1, LaneModuleReleaseIdV1,
    LaneModuleReleaseStatusV1, TerminalCoverageStatusV1, LANE_MODULE_RELEASE_VERSION_V1,
};
use crate::CommitmentV3;

const RELEASE_ID_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.lane_module_release_id.v1";
const RELEASE_RECORD_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.lane_module_release_record.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaneModuleReleaseV1 {
    release_version: u16,
    release_id: LaneModuleReleaseIdV1,
    content: LaneModuleReleaseContentV1,
    status: LaneModuleReleaseStatusV1,
}

impl<'de> Deserialize<'de> for LaneModuleReleaseV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            release_version: u16,
            release_id: LaneModuleReleaseIdV1,
            content: LaneModuleReleaseContentV1,
            status: LaneModuleReleaseStatusV1,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::from_parts(
            wire.release_version,
            wire.release_id,
            wire.content,
            wire.status,
        )
        .map_err(de::Error::custom)
    }
}

impl LaneModuleReleaseV1 {
    pub fn new(
        content: LaneModuleReleaseContentV1,
        status: LaneModuleReleaseStatusV1,
    ) -> Result<Self, LaneModuleReleaseErrorV1> {
        let release_id = derive_release_id(&content)?;
        Self::from_parts(LANE_MODULE_RELEASE_VERSION_V1, release_id, content, status)
    }

    pub(super) fn from_parts(
        release_version: u16,
        release_id: LaneModuleReleaseIdV1,
        content: LaneModuleReleaseContentV1,
        status: LaneModuleReleaseStatusV1,
    ) -> Result<Self, LaneModuleReleaseErrorV1> {
        validate_release_version(release_version)?;
        if derive_release_id(&content)? != release_id {
            return Err(LaneModuleReleaseErrorV1::CounterfeitReleaseId);
        }
        if content.migration().predecessor_release_id() == Some(release_id) {
            return Err(LaneModuleReleaseErrorV1::SelfMigrationPredecessor);
        }
        require_terminal_coverage(&content, status)?;
        Ok(Self {
            release_version,
            release_id,
            content,
            status,
        })
    }

    pub const fn release_version(&self) -> u16 {
        self.release_version
    }

    pub const fn release_id(&self) -> LaneModuleReleaseIdV1 {
        self.release_id
    }

    pub const fn content(&self) -> &LaneModuleReleaseContentV1 {
        &self.content
    }

    pub const fn status(&self) -> LaneModuleReleaseStatusV1 {
        self.status
    }

    pub fn transition_status(
        &self,
        to: LaneModuleReleaseStatusV1,
    ) -> Result<Self, LaneModuleReleaseErrorV1> {
        if !status_transition_allowed(self.status, to) {
            return Err(LaneModuleReleaseErrorV1::InvalidStatusTransition {
                from: self.status,
                to,
            });
        }
        Self::from_parts(
            self.release_version,
            self.release_id,
            self.content.clone(),
            to,
        )
    }

    pub fn admit_new_object_creation(&self) -> Result<(), LaneModuleReleaseErrorV1> {
        if self.status == LaneModuleReleaseStatusV1::ActiveNew {
            return Ok(());
        }
        Err(LaneModuleReleaseErrorV1::StatusDisallowsNewObject(
            self.status,
        ))
    }

    pub fn admit_existing_object_transition(&self) -> Result<(), LaneModuleReleaseErrorV1> {
        if matches!(
            self.status,
            LaneModuleReleaseStatusV1::ActiveNew | LaneModuleReleaseStatusV1::DrainOnly
        ) {
            return Ok(());
        }
        Err(LaneModuleReleaseErrorV1::StatusDisallowsExistingObject(
            self.status,
        ))
    }

    pub fn canonical_record_commitment(&self) -> Result<CommitmentV3, LaneModuleReleaseErrorV1> {
        let mut hasher = prefixed_domain_hasher(RELEASE_RECORD_DOMAIN_V1)?;
        hasher.update(self.release_version.to_be_bytes());
        hasher.update(self.release_id.as_bytes());
        hasher.update([self.status.code()]);
        CommitmentV3::new(hasher.finalize().into()).map_err(|_| {
            LaneModuleReleaseErrorV1::InvalidDerivedCommitment("lane_module_release_record")
        })
    }
}

fn validate_release_version(release_version: u16) -> Result<(), LaneModuleReleaseErrorV1> {
    if release_version != LANE_MODULE_RELEASE_VERSION_V1 {
        return Err(LaneModuleReleaseErrorV1::InvalidReleaseVersion(
            release_version,
        ));
    }
    Ok(())
}

fn derive_release_id(
    content: &LaneModuleReleaseContentV1,
) -> Result<LaneModuleReleaseIdV1, LaneModuleReleaseErrorV1> {
    let mut hasher = prefixed_domain_hasher(RELEASE_ID_DOMAIN_V1)?;
    hasher.update(LANE_MODULE_RELEASE_VERSION_V1.to_be_bytes());
    content.update_hasher(&mut hasher);
    LaneModuleReleaseIdV1::new(hasher.finalize().into())
        .map_err(|_| LaneModuleReleaseErrorV1::InvalidDerivedCommitment("lane_module_release_id"))
}

fn prefixed_domain_hasher(domain: &[u8]) -> Result<Sha256, LaneModuleReleaseErrorV1> {
    let domain_len = u16::try_from(domain.len())
        .map_err(|_| LaneModuleReleaseErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(domain_len.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn require_terminal_coverage(
    content: &LaneModuleReleaseContentV1,
    status: LaneModuleReleaseStatusV1,
) -> Result<(), LaneModuleReleaseErrorV1> {
    let requires_complete = matches!(
        status,
        LaneModuleReleaseStatusV1::ActiveNew
            | LaneModuleReleaseStatusV1::DrainOnly
            | LaneModuleReleaseStatusV1::VerifyOnly
            | LaneModuleReleaseStatusV1::Retired
    );
    if requires_complete && content.terminal().status() != TerminalCoverageStatusV1::Complete {
        return Err(LaneModuleReleaseErrorV1::TerminalCoverageIncomplete(status));
    }
    Ok(())
}

fn status_transition_allowed(
    from: LaneModuleReleaseStatusV1,
    to: LaneModuleReleaseStatusV1,
) -> bool {
    if to == LaneModuleReleaseStatusV1::Revoked {
        return from != LaneModuleReleaseStatusV1::Revoked;
    }
    matches!(
        (from, to),
        (
            LaneModuleReleaseStatusV1::Candidate,
            LaneModuleReleaseStatusV1::Shadow
        ) | (
            LaneModuleReleaseStatusV1::Shadow,
            LaneModuleReleaseStatusV1::ActiveNew
        ) | (
            LaneModuleReleaseStatusV1::ActiveNew,
            LaneModuleReleaseStatusV1::DrainOnly
        ) | (
            LaneModuleReleaseStatusV1::DrainOnly,
            LaneModuleReleaseStatusV1::VerifyOnly
        ) | (
            LaneModuleReleaseStatusV1::VerifyOnly,
            LaneModuleReleaseStatusV1::Retired
        )
    )
}
