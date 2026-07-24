use alloc::collections::BTreeSet;
use alloc::string::ToString;
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::DexSnapshotV1;

use crate::{RestrictedSpotStateRootV5BridgeError, MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1};

const PUBKEY_BYTES: usize = 48;
const IDENTIFIER_BYTES: usize = 32;
const STATE_ROOT_DOMAIN_SEPARATOR_V5: &[u8] = b"zenodex:state_root:v5\0";

pub(crate) struct RuntimeNonceProjectionV1<'a> {
    pub sender: &'a str,
    pub last_nonce: Option<u32>,
}

pub(crate) fn compute_restricted_state_root_v5(
    snapshot: &DexSnapshotV1,
    nonce: RuntimeNonceProjectionV1<'_>,
) -> Result<[u8; 32], RestrictedSpotStateRootV5BridgeError> {
    validate_snapshot_envelope(snapshot)?;
    let balances = encode_balances(snapshot)?;
    let (pools, pool_ids) = encode_pools(snapshot)?;
    let lp_balances = encode_lp_balances(snapshot, &pool_ids)?;
    let lp_duration_risk = encode_uvarint(0);
    let nonces = encode_runtime_nonce(nonce)?;
    let fee = encode_uvarint(snapshot.fee_accumulator.dust);

    let mut hasher = Sha256::new();
    hasher.update(STATE_ROOT_DOMAIN_SEPARATOR_V5);
    append_section(&mut hasher, b"BAL", &balances);
    append_section(&mut hasher, b"POL", &pools);
    append_section(&mut hasher, b"LPB", &lp_balances);
    append_section(&mut hasher, b"LPA", &lp_duration_risk);
    append_section(&mut hasher, b"NNC", &nonces);
    append_section(&mut hasher, b"FEE", &fee);
    Ok(hasher.finalize().into())
}

fn validate_snapshot_envelope(
    snapshot: &DexSnapshotV1,
) -> Result<(), RestrictedSpotStateRootV5BridgeError> {
    if snapshot.version != 1 {
        return Err(RestrictedSpotStateRootV5BridgeError::UnsupportedSnapshotVersion);
    }
    if snapshot.vault.is_some() {
        return Err(RestrictedSpotStateRootV5BridgeError::VaultStatePresent);
    }
    if snapshot.oracle.is_some() {
        return Err(RestrictedSpotStateRootV5BridgeError::OracleStatePresent);
    }
    for (section, count) in [
        ("balances", snapshot.balances.len()),
        ("pools", snapshot.pools.len()),
        ("lp_balances", snapshot.lp_balances.len()),
    ] {
        if count > MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1 {
            return Err(RestrictedSpotStateRootV5BridgeError::TooManyEntries(
                section,
            ));
        }
    }
    Ok(())
}

fn encode_balances(
    snapshot: &DexSnapshotV1,
) -> Result<Vec<u8>, RestrictedSpotStateRootV5BridgeError> {
    let mut entries = Vec::with_capacity(snapshot.balances.len());
    let mut seen = BTreeSet::new();
    for entry in &snapshot.balances {
        let pubkey = decode_canonical_hex::<PUBKEY_BYTES>(&entry.pubkey, "balance.pubkey")?;
        let asset = decode_canonical_hex::<IDENTIFIER_BYTES>(&entry.asset, "balance.asset")?;
        reject_native_asset(&asset)?;
        if entry.amount == 0 {
            return Err(RestrictedSpotStateRootV5BridgeError::ZeroAmount("balances"));
        }
        if !seen.insert((pubkey, asset)) {
            return Err(RestrictedSpotStateRootV5BridgeError::DuplicateKey(
                "balances",
            ));
        }
        entries.push((pubkey, asset, entry.amount));
    }
    entries.sort_by_key(|entry| (entry.0, entry.1));
    let mut output = encode_uvarint(entries.len() as u128);
    for (pubkey, asset, amount) in entries {
        output.extend_from_slice(&pubkey);
        output.extend_from_slice(&asset);
        output.extend_from_slice(&encode_uvarint(amount));
    }
    Ok(output)
}

type EncodedPoolsV1 = (Vec<u8>, BTreeSet<[u8; IDENTIFIER_BYTES]>);

fn encode_pools(
    snapshot: &DexSnapshotV1,
) -> Result<EncodedPoolsV1, RestrictedSpotStateRootV5BridgeError> {
    let mut entries = Vec::with_capacity(snapshot.pools.len());
    let mut seen = BTreeSet::new();
    for pool in &snapshot.pools {
        let pool_id = decode_canonical_hex::<IDENTIFIER_BYTES>(&pool.pool_id, "pool.pool_id")?;
        let asset0 = decode_canonical_hex::<IDENTIFIER_BYTES>(&pool.asset0, "pool.asset0")?;
        let asset1 = decode_canonical_hex::<IDENTIFIER_BYTES>(&pool.asset1, "pool.asset1")?;
        reject_native_asset(&asset0)?;
        reject_native_asset(&asset1)?;
        if asset0 >= asset1 {
            return Err(RestrictedSpotStateRootV5BridgeError::NonCanonicalPoolAssets);
        }
        if pool.fee_bps > 10_000 {
            return Err(RestrictedSpotStateRootV5BridgeError::FeeBpsOutOfRange);
        }
        if pool.status != "ACTIVE" {
            return Err(RestrictedSpotStateRootV5BridgeError::UnsupportedPoolStatus);
        }
        if pool_id != cpmm_pool_identity(&pool.asset0, &pool.asset1, pool.fee_bps) {
            return Err(RestrictedSpotStateRootV5BridgeError::PoolIdentityMismatch);
        }
        if !seen.insert(pool_id) {
            return Err(RestrictedSpotStateRootV5BridgeError::DuplicateKey("pools"));
        }
        entries.push((pool_id, asset0, asset1, pool));
    }
    entries.sort_by_key(|entry| entry.0);
    let mut output = encode_uvarint(entries.len() as u128);
    for (pool_id, asset0, asset1, pool) in entries {
        output.extend_from_slice(&pool_id);
        output.extend_from_slice(&asset0);
        output.extend_from_slice(&asset1);
        output.extend_from_slice(&encode_uvarint(pool.reserve0));
        output.extend_from_slice(&encode_uvarint(pool.reserve1));
        output.extend_from_slice(&encode_uvarint(u128::from(pool.fee_bps)));
        output.extend_from_slice(&encode_uvarint(pool.lp_supply));
        output.extend_from_slice(&encode_uvarint(1));
        output.extend_from_slice(&encode_uvarint(u128::from(pool.created_at)));
        output.extend_from_slice(&encode_bytes(b"CPMM"));
        output.extend_from_slice(&encode_bytes(b""));
    }
    Ok((output, seen))
}

fn encode_lp_balances(
    snapshot: &DexSnapshotV1,
    pool_ids: &BTreeSet<[u8; IDENTIFIER_BYTES]>,
) -> Result<Vec<u8>, RestrictedSpotStateRootV5BridgeError> {
    let mut entries = Vec::with_capacity(snapshot.lp_balances.len());
    let mut seen = BTreeSet::new();
    for entry in &snapshot.lp_balances {
        let pubkey = decode_canonical_hex::<PUBKEY_BYTES>(&entry.pubkey, "lp.pubkey")?;
        let pool_id = decode_canonical_hex::<IDENTIFIER_BYTES>(&entry.pool_id, "lp.pool_id")?;
        if !pool_ids.contains(&pool_id) {
            return Err(RestrictedSpotStateRootV5BridgeError::UnknownLpPool);
        }
        if entry.amount == 0 {
            return Err(RestrictedSpotStateRootV5BridgeError::ZeroAmount(
                "lp_balances",
            ));
        }
        if !seen.insert((pubkey, pool_id)) {
            return Err(RestrictedSpotStateRootV5BridgeError::DuplicateKey(
                "lp_balances",
            ));
        }
        entries.push((pubkey, pool_id, entry.amount));
    }
    entries.sort_by_key(|entry| (entry.0, entry.1));
    let mut output = encode_uvarint(entries.len() as u128);
    for (pubkey, pool_id, amount) in entries {
        output.extend_from_slice(&pubkey);
        output.extend_from_slice(&pool_id);
        output.extend_from_slice(&encode_uvarint(amount));
    }
    Ok(output)
}

fn encode_runtime_nonce(
    nonce: RuntimeNonceProjectionV1<'_>,
) -> Result<Vec<u8>, RestrictedSpotStateRootV5BridgeError> {
    let sender = decode_canonical_hex::<PUBKEY_BYTES>(nonce.sender, "nonce.pubkey")?;
    let Some(last_nonce) = nonce.last_nonce else {
        return Ok(encode_uvarint(0));
    };
    let mut output = encode_uvarint(1);
    output.extend_from_slice(&sender);
    output.extend_from_slice(&encode_uvarint(u128::from(last_nonce)));
    Ok(output)
}

fn cpmm_pool_identity(asset0: &str, asset1: &str, fee_bps: u32) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"TauSwapPool");
    hasher.update(asset0.as_bytes());
    hasher.update(asset1.as_bytes());
    hasher.update(fee_bps.to_string().as_bytes());
    hasher.update(b"CPMM");
    hasher.update(b"");
    hasher.finalize().into()
}

fn reject_native_asset(
    asset: &[u8; IDENTIFIER_BYTES],
) -> Result<(), RestrictedSpotStateRootV5BridgeError> {
    if asset.iter().all(|byte| *byte == 0) {
        return Err(RestrictedSpotStateRootV5BridgeError::NativeAssetUnsupported);
    }
    Ok(())
}

fn decode_canonical_hex<const N: usize>(
    value: &str,
    field: &'static str,
) -> Result<[u8; N], RestrictedSpotStateRootV5BridgeError> {
    let bytes = value.as_bytes();
    if bytes.len() != 2 + 2 * N
        || !value.starts_with("0x")
        || !bytes[2..]
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
    {
        return Err(RestrictedSpotStateRootV5BridgeError::NonCanonicalIdentifier(field));
    }
    let mut decoded = [0_u8; N];
    for (index, pair) in bytes[2..].chunks_exact(2).enumerate() {
        decoded[index] = (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1]);
    }
    Ok(decoded)
}

const fn hex_nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => 0,
    }
}

fn append_section(hasher: &mut Sha256, tag: &[u8; 3], section: &[u8]) {
    hasher.update(tag);
    hasher.update(encode_bytes(section));
}

fn encode_bytes(bytes: &[u8]) -> Vec<u8> {
    let mut output = encode_uvarint(bytes.len() as u128);
    output.extend_from_slice(bytes);
    output
}

fn encode_uvarint(mut value: u128) -> Vec<u8> {
    let mut output = Vec::new();
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        output.push(byte);
        if value == 0 {
            return output;
        }
    }
}
