use core::fmt;

use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::RestrictedSpotStateRootV5BridgeError;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpotStateRootV7SemanticErrorV1 {
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    InvalidVersion(u16),
    Truncated(&'static str),
    TrailingBytes,
    LengthOverflow(&'static str),
    CountTooLarge {
        section: &'static str,
        actual: usize,
        maximum: usize,
    },
    NonCanonicalIdentifier(&'static str),
    NonCanonicalOrder(&'static str),
    UnsupportedSnapshotVersion,
    UnsupportedPoolStatus,
    VaultStatePresent,
    OracleStatePresent,
    UnexpectedProfileId,
    UnexpectedStateRootSchemeId,
    IngressNonceZero,
    Bridge(RestrictedSpotStateRootV5BridgeError),
}

impl SpotStateRootV7SemanticErrorV1 {
    pub const fn code(&self) -> &'static str {
        match self {
            Self::EmptyInput => "empty_input",
            Self::InputTooLarge { .. } => "input_too_large",
            Self::InvalidVersion(_) => "invalid_version",
            Self::Truncated(_) => "truncated",
            Self::TrailingBytes => "trailing_bytes",
            Self::LengthOverflow(_) => "length_overflow",
            Self::CountTooLarge { .. } => "count_too_large",
            Self::NonCanonicalIdentifier(_) => "noncanonical_identifier",
            Self::NonCanonicalOrder(_) => "noncanonical_order",
            Self::UnsupportedSnapshotVersion => "unsupported_snapshot_version",
            Self::UnsupportedPoolStatus => "unsupported_pool_status",
            Self::VaultStatePresent => "vault_state_present",
            Self::OracleStatePresent => "oracle_state_present",
            Self::UnexpectedProfileId => "unexpected_profile_id",
            Self::UnexpectedStateRootSchemeId => "unexpected_state_root_scheme_id",
            Self::IngressNonceZero => "ingress_nonce_zero",
            Self::Bridge(error) => error.code(),
        }
    }
}

impl From<RestrictedSpotStateRootV5BridgeError> for SpotStateRootV7SemanticErrorV1 {
    fn from(error: RestrictedSpotStateRootV5BridgeError) -> Self {
        Self::Bridge(error)
    }
}

impl fmt::Display for SpotStateRootV7SemanticErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.code())
    }
}
