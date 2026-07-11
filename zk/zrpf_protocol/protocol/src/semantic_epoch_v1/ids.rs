use super::super::CommitmentV3;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceClaimIdV1(CommitmentV3);

impl SourceClaimIdV1 {
    pub(super) const fn from_profile_bound_proposal(value: CommitmentV3) -> Self {
        Self(value)
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        self.0.as_bytes()
    }

    pub const fn into_commitment(self) -> CommitmentV3 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SemanticSourceIdV1(CommitmentV3);

impl SemanticSourceIdV1 {
    pub(super) const fn from_profile_bound_proposal(value: CommitmentV3) -> Self {
        Self(value)
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        self.0.as_bytes()
    }

    pub const fn into_commitment(self) -> CommitmentV3 {
        self.0
    }
}
