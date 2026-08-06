use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::CommitmentV3;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RouteOraclePolicyV1 {
    Forbidden,
    Required { policy_root: CommitmentV3 },
}

impl RouteOraclePolicyV1 {
    pub(super) const fn requires_oracle(self) -> bool {
        matches!(self, Self::Required { .. })
    }

    pub(super) fn update_hasher(self, hasher: &mut Sha256) {
        match self {
            Self::Forbidden => hasher.update([0]),
            Self::Required { policy_root } => {
                hasher.update([1]);
                hasher.update(policy_root.as_bytes());
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RouteIssueBurnPolicyV1 {
    Forbidden,
    IssueOnly { policy_root: CommitmentV3 },
    BurnOnly { policy_root: CommitmentV3 },
    IssueAndBurn { policy_root: CommitmentV3 },
}

impl RouteIssueBurnPolicyV1 {
    pub(super) const fn authorizes_issue_or_burn(self) -> bool {
        !matches!(self, Self::Forbidden)
    }

    pub(super) fn update_hasher(self, hasher: &mut Sha256) {
        match self {
            Self::Forbidden => hasher.update([0]),
            Self::IssueOnly { policy_root } => {
                hasher.update([1]);
                hasher.update(policy_root.as_bytes());
            }
            Self::BurnOnly { policy_root } => {
                hasher.update([2]);
                hasher.update(policy_root.as_bytes());
            }
            Self::IssueAndBurn { policy_root } => {
                hasher.update([3]);
                hasher.update(policy_root.as_bytes());
            }
        }
    }
}
