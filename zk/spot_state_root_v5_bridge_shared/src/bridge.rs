use tau_state_proof_risc0_shared::{
    sha256_canonical_dex_snapshot_v1, DexSnapshotV1, NonceEntryV1, NonceStateV1,
};

use crate::root_v5::{compute_restricted_state_root_v5, RuntimeNonceProjectionV1};
use crate::{RestrictedSpotStateRootV5BridgeError, RestrictedSpotStateRootV5ProfileV1};

/// Header roots proposed to the pure bridge for exact comparison.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExpectedSpotStateRootsV5 {
    pre_state_root_v5: [u8; 32],
    post_state_root_v5: [u8; 32],
}

impl ExpectedSpotStateRootsV5 {
    pub const fn new(pre_state_root_v5: [u8; 32], post_state_root_v5: [u8; 32]) -> Self {
        Self {
            pre_state_root_v5,
            post_state_root_v5,
        }
    }
}

/// Expected commitments that a future V7 guest must take from an authenticated
/// legacy source journal. Construction by itself carries no authentication.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExpectedLegacySpotCommitmentsV1 {
    pre_app_hash: [u8; 32],
    post_app_hash: [u8; 32],
    pre_nonce_root: [u8; 32],
    post_nonce_root: [u8; 32],
}

impl ExpectedLegacySpotCommitmentsV1 {
    pub const fn new(
        pre_app_hash: [u8; 32],
        post_app_hash: [u8; 32],
        pre_nonce_root: [u8; 32],
        post_nonce_root: [u8; 32],
    ) -> Self {
        Self {
            pre_app_hash,
            post_app_hash,
            pre_nonce_root,
            post_nonce_root,
        }
    }
}

/// Untrusted proof-neutral proposal for the restricted bridge.
pub struct RestrictedSpotStateRootV5TransitionInputV1<'a> {
    pre_state: &'a DexSnapshotV1,
    post_state: &'a DexSnapshotV1,
    pre_nonces: &'a [NonceEntryV1],
    sender_pubkey: &'a str,
    ingress_nonce: u64,
    expected_source: ExpectedLegacySpotCommitmentsV1,
    expected_roots: ExpectedSpotStateRootsV5,
}

impl<'a> RestrictedSpotStateRootV5TransitionInputV1<'a> {
    pub const fn new(
        pre_state: &'a DexSnapshotV1,
        post_state: &'a DexSnapshotV1,
        pre_nonces: &'a [NonceEntryV1],
        sender_pubkey: &'a str,
        ingress_nonce: u64,
        expected_source: ExpectedLegacySpotCommitmentsV1,
        expected_roots: ExpectedSpotStateRootsV5,
    ) -> Self {
        Self {
            pre_state,
            post_state,
            pre_nonces,
            sender_pubkey,
            ingress_nonce,
            expected_source,
            expected_roots,
        }
    }
}

/// Derived compatibility facts. This type carries no settlement authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RestrictedSpotStateRootV5BridgeFactsV1 {
    compatibility_profile_id: [u8; 32],
    state_root_scheme_id: [u8; 32],
    pre_state_root_v5: [u8; 32],
    post_state_root_v5: [u8; 32],
    source_pre_app_hash: [u8; 32],
    source_post_app_hash: [u8; 32],
    source_pre_nonce_root: [u8; 32],
    source_post_nonce_root: [u8; 32],
    sender_pubkey: [u8; 48],
    ingress_nonce: u32,
}

impl RestrictedSpotStateRootV5BridgeFactsV1 {
    pub const fn compatibility_profile_id(&self) -> [u8; 32] {
        self.compatibility_profile_id
    }

    pub const fn state_root_scheme_id(&self) -> [u8; 32] {
        self.state_root_scheme_id
    }

    pub const fn pre_state_root_v5(&self) -> [u8; 32] {
        self.pre_state_root_v5
    }

    pub const fn post_state_root_v5(&self) -> [u8; 32] {
        self.post_state_root_v5
    }

    pub const fn source_pre_app_hash(&self) -> [u8; 32] {
        self.source_pre_app_hash
    }

    pub const fn source_post_app_hash(&self) -> [u8; 32] {
        self.source_post_app_hash
    }

    pub const fn source_pre_nonce_root(&self) -> [u8; 32] {
        self.source_pre_nonce_root
    }

    pub const fn source_post_nonce_root(&self) -> [u8; 32] {
        self.source_post_nonce_root
    }

    pub const fn sender_pubkey(&self) -> [u8; 48] {
        self.sender_pubkey
    }

    pub const fn ingress_nonce(&self) -> u32 {
        self.ingress_nonce
    }
}

/// Derive and compare exact v5 roots for the closed compatibility profile.
///
/// The caller must separately authenticate `expected_source`, constrain the
/// snapshots to that source, and bind the returned facts to a future guest
/// journal. Successful derivation alone never authorizes settlement.
pub fn verify_restricted_spot_state_root_v5_transition_v1(
    profile: RestrictedSpotStateRootV5ProfileV1,
    input: RestrictedSpotStateRootV5TransitionInputV1<'_>,
) -> Result<RestrictedSpotStateRootV5BridgeFactsV1, RestrictedSpotStateRootV5BridgeError> {
    let (ingress_nonce, sender_pubkey) = validate_nonce_domain(&input)?;
    let pre_last_nonce = ingress_nonce.checked_sub(1).filter(|nonce| *nonce > 0);
    let pre_state_root_v5 = compute_restricted_state_root_v5(
        input.pre_state,
        RuntimeNonceProjectionV1 {
            sender: input.sender_pubkey,
            last_nonce: pre_last_nonce,
        },
    )?;
    let post_state_root_v5 = compute_restricted_state_root_v5(
        input.post_state,
        RuntimeNonceProjectionV1 {
            sender: input.sender_pubkey,
            last_nonce: Some(ingress_nonce),
        },
    )?;
    let source_pre_app_hash = sha256_canonical_dex_snapshot_v1(input.pre_state);
    let source_post_app_hash = sha256_canonical_dex_snapshot_v1(input.post_state);
    let source_pre_nonce_root = legacy_nonce_root(input.sender_pubkey, u64::from(ingress_nonce))?;
    let source_post_nonce_root =
        legacy_nonce_root(input.sender_pubkey, u64::from(ingress_nonce) + 1)?;
    verify_source_commitments(
        &input.expected_source,
        source_pre_app_hash,
        source_post_app_hash,
        source_pre_nonce_root,
        source_post_nonce_root,
    )?;
    verify_header_roots(&input.expected_roots, pre_state_root_v5, post_state_root_v5)?;
    Ok(RestrictedSpotStateRootV5BridgeFactsV1 {
        compatibility_profile_id: profile.profile_id(),
        state_root_scheme_id: profile.state_root_scheme_id(),
        pre_state_root_v5,
        post_state_root_v5,
        source_pre_app_hash,
        source_post_app_hash,
        source_pre_nonce_root,
        source_post_nonce_root,
        sender_pubkey,
        ingress_nonce,
    })
}

fn verify_source_commitments(
    expected: &ExpectedLegacySpotCommitmentsV1,
    pre_app_hash: [u8; 32],
    post_app_hash: [u8; 32],
    pre_nonce_root: [u8; 32],
    post_nonce_root: [u8; 32],
) -> Result<(), RestrictedSpotStateRootV5BridgeError> {
    for (matches, error) in [
        (
            pre_app_hash == expected.pre_app_hash,
            RestrictedSpotStateRootV5BridgeError::SourcePreAppHashMismatch,
        ),
        (
            post_app_hash == expected.post_app_hash,
            RestrictedSpotStateRootV5BridgeError::SourcePostAppHashMismatch,
        ),
        (
            pre_nonce_root == expected.pre_nonce_root,
            RestrictedSpotStateRootV5BridgeError::SourcePreNonceRootMismatch,
        ),
        (
            post_nonce_root == expected.post_nonce_root,
            RestrictedSpotStateRootV5BridgeError::SourcePostNonceRootMismatch,
        ),
    ] {
        if !matches {
            return Err(error);
        }
    }
    Ok(())
}

fn verify_header_roots(
    expected: &ExpectedSpotStateRootsV5,
    pre_state_root_v5: [u8; 32],
    post_state_root_v5: [u8; 32],
) -> Result<(), RestrictedSpotStateRootV5BridgeError> {
    if pre_state_root_v5 != expected.pre_state_root_v5 {
        return Err(RestrictedSpotStateRootV5BridgeError::PreStateRootMismatch {
            expected: expected.pre_state_root_v5,
            actual: pre_state_root_v5,
        });
    }
    if post_state_root_v5 != expected.post_state_root_v5 {
        return Err(
            RestrictedSpotStateRootV5BridgeError::PostStateRootMismatch {
                expected: expected.post_state_root_v5,
                actual: post_state_root_v5,
            },
        );
    }
    Ok(())
}

fn validate_nonce_domain(
    input: &RestrictedSpotStateRootV5TransitionInputV1<'_>,
) -> Result<(u32, [u8; 48]), RestrictedSpotStateRootV5BridgeError> {
    if input.ingress_nonce == 0 {
        return Err(RestrictedSpotStateRootV5BridgeError::IngressNonceZero);
    }
    let ingress_nonce = u32::try_from(input.ingress_nonce)
        .map_err(|_| RestrictedSpotStateRootV5BridgeError::IngressNonceTooLarge)?;
    if input.pre_nonces.len() != 1
        || input.pre_nonces[0].pubkey != input.sender_pubkey
        || input.pre_nonces[0].next_nonce != input.ingress_nonce
    {
        return Err(RestrictedSpotStateRootV5BridgeError::NonCanonicalNonceSet);
    }
    let sender_pubkey = decode_sender(input.sender_pubkey)?;
    Ok((ingress_nonce, sender_pubkey))
}

fn decode_sender(value: &str) -> Result<[u8; 48], RestrictedSpotStateRootV5BridgeError> {
    let bytes = value.as_bytes();
    if bytes.len() != 98
        || !value.starts_with("0x")
        || !bytes[2..]
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
    {
        return Err(RestrictedSpotStateRootV5BridgeError::NonCanonicalIdentifier("sender_pubkey"));
    }
    let mut decoded = [0_u8; 48];
    for (index, pair) in bytes[2..].chunks_exact(2).enumerate() {
        decoded[index] = (nibble(pair[0]) << 4) | nibble(pair[1]);
    }
    Ok(decoded)
}

const fn nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => 0,
    }
}

fn legacy_nonce_root(
    sender_pubkey: &str,
    next_nonce: u64,
) -> Result<[u8; 32], RestrictedSpotStateRootV5BridgeError> {
    NonceStateV1::from_entries(alloc::vec![NonceEntryV1 {
        pubkey: sender_pubkey.into(),
        next_nonce,
    }])
    .map(|state| state.root())
    .map_err(|_| RestrictedSpotStateRootV5BridgeError::NonCanonicalNonceSet)
}
