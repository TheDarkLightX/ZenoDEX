use sha2::{Digest, Sha256};

/// State-root encoder version committed by ZenoLedger Spot headers.
pub const ZENO_LEDGER_SPOT_STATE_ROOT_VERSION_V5: u32 = 5;

/// Bound inherited from the source-opening byte ceiling, with headroom.
pub const MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1: usize = 16_384;

/// Complete ordered acceptance-domain descriptor for the governed profile.
///
/// The profile ID is SHA-256 over each UTF-8 rule followed by one NUL byte.
/// Changing any accepted or rejected state family therefore changes the ID.
pub const RESTRICTED_SPOT_STATE_ROOT_V5_PROFILE_RULES_V1: &[&str] = &[
    "zenodex.zrpf.spot_state_root_v5_bridge.profile.v1",
    "legacy_snapshot_version=u32_exact_1",
    "source_app_hash=sha256_canonical_dex_snapshot_v1",
    "source_nonce_root=tau_state_proof_nonce_root_v1",
    "source_commitments=exact_pre_app_post_app_pre_nonce_post_nonce",
    "header_commitments=exact_pre_state_root_v5_post_state_root_v5",
    "pubkey_encoding=lowercase_0x_48_bytes",
    "asset_and_pool_encoding=lowercase_0x_32_bytes",
    "balance_amount=u128_positive",
    "balance_asset=nonnative",
    "balance_key=unique_decoded_pubkey_asset",
    "balance_order=decoded_pubkey_asset",
    "max_balance_entries=16384",
    "pool_reserves=u128",
    "pool_lp_supply=u128",
    "pool_created_at=u64",
    "pool_assets=nonnative_decoded_asset0_lt_asset1",
    "pool_fee_bps=u32_0_to_10000",
    "pool_curve=CPMM",
    "pool_curve_params=empty",
    "pool_status=ACTIVE",
    "pool_status_code=1",
    "pool_id=sha256(TauSwapPool||asset0_ascii||asset1_ascii||fee_bps_decimal||CPMM||empty)",
    "pool_key=unique_decoded_pool_id",
    "pool_order=decoded_pool_id",
    "max_pool_entries=16384",
    "lp_balance_amount=u128_positive",
    "lp_balance_pool_reference=required",
    "lp_balance_key=unique_decoded_pubkey_pool_id",
    "lp_balance_order=decoded_pubkey_pool_id",
    "max_lp_balance_entries=16384",
    "lp_duration_risk=empty",
    "vault=absent",
    "oracle=absent",
    "fee_accumulator_dust=u128",
    "legacy_pre_nonce_set=exact_single_sender_next_nonce_n",
    "ingress_nonce=u64_restricted_1_to_u32_max",
    "runtime_pre_nonce=omit_when_n_1_else_single_sender_last_nonce_n_minus_1",
    "runtime_post_nonce=single_sender_last_nonce_n",
    "other_runtime_nonces=absent",
    "state_root_version=5",
    "state_root_hash=sha256",
    "state_root_domain=zenodex:state_root:v5_nul",
    "state_root_sections=BAL_POL_LPB_LPA_NNC_FEE",
    "state_root_integer_encoding=unsigned_leb128",
    "state_root_section_framing=tag3_then_unsigned_leb128_byte_length_then_bytes",
    "settlement_authority=false",
];

const STATE_ROOT_SCHEME_DESCRIPTOR_V5: &[u8] = b"zenodex.state_root.v5\0\
sections=BAL,POL,LPB,LPA,NNC,FEE\0\
hash=sha256\0\
canonical_integer_encoding=unsigned_leb128";

/// Closed marker for the sole compatibility profile implemented by this crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RestrictedSpotStateRootV5ProfileV1 {
    _closed: (),
}

impl RestrictedSpotStateRootV5ProfileV1 {
    /// Select the governed, non-authoritative compatibility profile.
    pub const fn governed() -> Self {
        Self { _closed: () }
    }

    pub fn profile_id(self) -> [u8; 32] {
        compatibility_profile_id_v1()
    }

    pub fn state_root_scheme_id(self) -> [u8; 32] {
        state_root_scheme_id_v5()
    }
}

pub fn compatibility_profile_id_v1() -> [u8; 32] {
    let mut hasher = Sha256::new();
    for rule in RESTRICTED_SPOT_STATE_ROOT_V5_PROFILE_RULES_V1 {
        hasher.update(rule.as_bytes());
        hasher.update([0]);
    }
    hasher.finalize().into()
}

pub fn state_root_scheme_id_v5() -> [u8; 32] {
    Sha256::digest(STATE_ROOT_SCHEME_DESCRIPTOR_V5).into()
}
