use core::fmt;

/// Typed fail-closed rejection from the restricted state-domain bridge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RestrictedSpotStateRootV5BridgeError {
    UnsupportedSnapshotVersion,
    VaultStatePresent,
    OracleStatePresent,
    TooManyEntries(&'static str),
    NonCanonicalIdentifier(&'static str),
    NativeAssetUnsupported,
    FeeBpsOutOfRange,
    ZeroAmount(&'static str),
    DuplicateKey(&'static str),
    NonCanonicalPoolAssets,
    UnsupportedPoolStatus,
    PoolIdentityMismatch,
    UnknownLpPool,
    IngressNonceZero,
    IngressNonceTooLarge,
    NonCanonicalNonceSet,
    SourcePreAppHashMismatch,
    SourcePostAppHashMismatch,
    SourcePreNonceRootMismatch,
    SourcePostNonceRootMismatch,
    PreStateRootMismatch {
        expected: [u8; 32],
        actual: [u8; 32],
    },
    PostStateRootMismatch {
        expected: [u8; 32],
        actual: [u8; 32],
    },
}

impl RestrictedSpotStateRootV5BridgeError {
    /// Stable machine-readable reject code.
    pub const fn code(&self) -> &'static str {
        match self {
            Self::UnsupportedSnapshotVersion => "unsupported_snapshot_version",
            Self::VaultStatePresent => "vault_state_present",
            Self::OracleStatePresent => "oracle_state_present",
            Self::TooManyEntries(_) => "too_many_entries",
            Self::NonCanonicalIdentifier(_) => "noncanonical_identifier",
            Self::NativeAssetUnsupported => "native_asset_unsupported",
            Self::FeeBpsOutOfRange => "fee_bps_out_of_range",
            Self::ZeroAmount(_) => "zero_amount",
            Self::DuplicateKey(_) => "duplicate_key",
            Self::NonCanonicalPoolAssets => "noncanonical_pool_assets",
            Self::UnsupportedPoolStatus => "unsupported_pool_status",
            Self::PoolIdentityMismatch => "pool_identity_mismatch",
            Self::UnknownLpPool => "unknown_lp_pool",
            Self::IngressNonceZero => "ingress_nonce_zero",
            Self::IngressNonceTooLarge => "ingress_nonce_too_large",
            Self::NonCanonicalNonceSet => "noncanonical_nonce_set",
            Self::SourcePreAppHashMismatch => "source_pre_app_hash_mismatch",
            Self::SourcePostAppHashMismatch => "source_post_app_hash_mismatch",
            Self::SourcePreNonceRootMismatch => "source_pre_nonce_root_mismatch",
            Self::SourcePostNonceRootMismatch => "source_post_nonce_root_mismatch",
            Self::PreStateRootMismatch { .. } => "pre_state_root_mismatch",
            Self::PostStateRootMismatch { .. } => "post_state_root_mismatch",
        }
    }
}

impl fmt::Display for RestrictedSpotStateRootV5BridgeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooManyEntries(section)
            | Self::ZeroAmount(section)
            | Self::DuplicateKey(section)
            | Self::NonCanonicalIdentifier(section) => {
                write!(formatter, "{}:{section}", self.code())
            }
            _ => formatter.write_str(self.code()),
        }
    }
}
