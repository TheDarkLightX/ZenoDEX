use alloc::string::String;
use alloc::vec::Vec;

use tau_state_proof_risc0_shared::{
    DexBalanceEntryV1, DexLpBalanceEntryV1, DexPoolEntryV1, DexSnapshotV1, FeeAccumulatorV1,
};
use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1;

use crate::SpotStateRootV7SemanticErrorV1;

pub const SPOT_STATE_ROOT_V7_HOST_INPUT_VERSION_V1: u16 = 1;

const PUBKEY_BYTES: usize = 48;
const IDENTIFIER_BYTES: usize = 32;
const BALANCE_ROW_BYTES: usize = PUBKEY_BYTES + IDENTIFIER_BYTES + 16;
const POOL_ROW_BYTES: usize = IDENTIFIER_BYTES * 3 + 16 * 3 + 4 + 8;
const LP_BALANCE_ROW_BYTES: usize = PUBKEY_BYTES + IDENTIFIER_BYTES + 16;
const SNAPSHOT_FIXED_BYTES: usize = 4 + 4 + 4 + 16;

/// Exact byte ceiling for the versioned post-snapshot plus two header roots.
pub const MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1: usize = 2
    + SNAPSHOT_FIXED_BYTES
    + MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1 * BALANCE_ROW_BYTES
    + MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1 * POOL_ROW_BYTES
    + MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1 * LP_BALANCE_ROW_BYTES
    + 32
    + 32;

/// Bounded canonical host proposal for the proof-neutral V7 kernel.
///
/// Curve tag `CPMM`, empty curve parameters, active status, snapshot version 1,
/// and absent vault/oracle fields are implicit in this ABI and cannot be
/// supplied by the host.
#[derive(Clone, Debug)]
pub struct BoundedSpotStateRootV7HostInputV1 {
    post_state: DexSnapshotV1,
    expected_pre_state_root_v5: [u8; 32],
    expected_post_state_root_v5: [u8; 32],
}

impl BoundedSpotStateRootV7HostInputV1 {
    pub fn new(
        post_state: DexSnapshotV1,
        expected_pre_state_root_v5: [u8; 32],
        expected_post_state_root_v5: [u8; 32],
    ) -> Result<Self, SpotStateRootV7SemanticErrorV1> {
        Ok(Self {
            post_state: canonicalize_snapshot(post_state)?,
            expected_pre_state_root_v5,
            expected_post_state_root_v5,
        })
    }

    pub const fn post_state(&self) -> &DexSnapshotV1 {
        &self.post_state
    }

    pub const fn expected_pre_state_root_v5(&self) -> [u8; 32] {
        self.expected_pre_state_root_v5
    }

    pub const fn expected_post_state_root_v5(&self) -> [u8; 32] {
        self.expected_post_state_root_v5
    }
}

pub fn encode_bounded_spot_state_root_v7_host_input_v1(
    input: &BoundedSpotStateRootV7HostInputV1,
) -> Result<Vec<u8>, SpotStateRootV7SemanticErrorV1> {
    let snapshot = input.post_state();
    let capacity = encoded_host_input_length(snapshot)?;
    let mut output = Vec::with_capacity(capacity);
    output.extend_from_slice(&SPOT_STATE_ROOT_V7_HOST_INPUT_VERSION_V1.to_be_bytes());
    write_snapshot(&mut output, snapshot)?;
    output.extend_from_slice(&input.expected_pre_state_root_v5);
    output.extend_from_slice(&input.expected_post_state_root_v5);
    Ok(output)
}

pub fn decode_exact_bounded_spot_state_root_v7_host_input_v1(
    bytes: &[u8],
) -> Result<BoundedSpotStateRootV7HostInputV1, SpotStateRootV7SemanticErrorV1> {
    if bytes.is_empty() {
        return Err(SpotStateRootV7SemanticErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1 {
        return Err(SpotStateRootV7SemanticErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1,
        });
    }
    let mut cursor = CursorV1::new(bytes);
    let version = cursor.read_u16("version")?;
    if version != SPOT_STATE_ROOT_V7_HOST_INPUT_VERSION_V1 {
        return Err(SpotStateRootV7SemanticErrorV1::InvalidVersion(version));
    }
    let post_state = read_snapshot(&mut cursor)?;
    let expected_pre_state_root_v5 = cursor.read_array("expected pre state root v5")?;
    let expected_post_state_root_v5 = cursor.read_array("expected post state root v5")?;
    if !cursor.is_finished() {
        return Err(SpotStateRootV7SemanticErrorV1::TrailingBytes);
    }
    BoundedSpotStateRootV7HostInputV1::new(
        post_state,
        expected_pre_state_root_v5,
        expected_post_state_root_v5,
    )
}

fn canonicalize_snapshot(
    snapshot: DexSnapshotV1,
) -> Result<DexSnapshotV1, SpotStateRootV7SemanticErrorV1> {
    if snapshot.version != 1 {
        return Err(SpotStateRootV7SemanticErrorV1::UnsupportedSnapshotVersion);
    }
    if snapshot.vault.is_some() {
        return Err(SpotStateRootV7SemanticErrorV1::VaultStatePresent);
    }
    if snapshot.oracle.is_some() {
        return Err(SpotStateRootV7SemanticErrorV1::OracleStatePresent);
    }
    require_count("balances", snapshot.balances.len())?;
    require_count("pools", snapshot.pools.len())?;
    require_count("lp_balances", snapshot.lp_balances.len())?;

    Ok(DexSnapshotV1 {
        version: 1,
        balances: canonicalize_balances(snapshot.balances)?,
        pools: canonicalize_pools(snapshot.pools)?,
        lp_balances: canonicalize_lp_balances(snapshot.lp_balances)?,
        fee_accumulator: snapshot.fee_accumulator,
        vault: None,
        oracle: None,
    })
}

fn canonicalize_balances(
    entries: Vec<DexBalanceEntryV1>,
) -> Result<Vec<DexBalanceEntryV1>, SpotStateRootV7SemanticErrorV1> {
    let mut balances = Vec::with_capacity(entries.len());
    for entry in entries {
        let key = (
            decode_canonical_hex::<PUBKEY_BYTES>(&entry.pubkey, "balance.pubkey")?,
            decode_canonical_hex::<IDENTIFIER_BYTES>(&entry.asset, "balance.asset")?,
        );
        balances.push((key, entry));
    }
    balances.sort_by_key(|entry| entry.0);
    require_strict_keys("balances", balances.iter().map(|entry| entry.0))?;
    Ok(balances.into_iter().map(|entry| entry.1).collect())
}

fn canonicalize_pools(
    entries: Vec<DexPoolEntryV1>,
) -> Result<Vec<DexPoolEntryV1>, SpotStateRootV7SemanticErrorV1> {
    let mut pools = Vec::with_capacity(entries.len());
    for entry in entries {
        if entry.status != "ACTIVE" {
            return Err(SpotStateRootV7SemanticErrorV1::UnsupportedPoolStatus);
        }
        let key = decode_canonical_hex::<IDENTIFIER_BYTES>(&entry.pool_id, "pool.pool_id")?;
        decode_canonical_hex::<IDENTIFIER_BYTES>(&entry.asset0, "pool.asset0")?;
        decode_canonical_hex::<IDENTIFIER_BYTES>(&entry.asset1, "pool.asset1")?;
        pools.push((key, entry));
    }
    pools.sort_by_key(|entry| entry.0);
    require_strict_keys("pools", pools.iter().map(|entry| entry.0))?;
    Ok(pools.into_iter().map(|entry| entry.1).collect())
}

fn canonicalize_lp_balances(
    entries: Vec<DexLpBalanceEntryV1>,
) -> Result<Vec<DexLpBalanceEntryV1>, SpotStateRootV7SemanticErrorV1> {
    let mut lp_balances = Vec::with_capacity(entries.len());
    for entry in entries {
        let key = (
            decode_canonical_hex::<PUBKEY_BYTES>(&entry.pubkey, "lp.pubkey")?,
            decode_canonical_hex::<IDENTIFIER_BYTES>(&entry.pool_id, "lp.pool_id")?,
        );
        lp_balances.push((key, entry));
    }
    lp_balances.sort_by_key(|entry| entry.0);
    require_strict_keys("lp_balances", lp_balances.iter().map(|entry| entry.0))?;
    Ok(lp_balances.into_iter().map(|entry| entry.1).collect())
}

fn require_strict_keys<T: Copy + Ord>(
    section: &'static str,
    keys: impl Iterator<Item = T>,
) -> Result<(), SpotStateRootV7SemanticErrorV1> {
    let mut previous = None;
    for key in keys {
        if previous.is_some_and(|value| value >= key) {
            return Err(SpotStateRootV7SemanticErrorV1::NonCanonicalOrder(section));
        }
        previous = Some(key);
    }
    Ok(())
}

fn encoded_host_input_length(
    snapshot: &DexSnapshotV1,
) -> Result<usize, SpotStateRootV7SemanticErrorV1> {
    let balance_bytes = snapshot
        .balances
        .len()
        .checked_mul(BALANCE_ROW_BYTES)
        .ok_or(SpotStateRootV7SemanticErrorV1::LengthOverflow("balances"))?;
    let pool_bytes = snapshot
        .pools
        .len()
        .checked_mul(POOL_ROW_BYTES)
        .ok_or(SpotStateRootV7SemanticErrorV1::LengthOverflow("pools"))?;
    let lp_bytes = snapshot
        .lp_balances
        .len()
        .checked_mul(LP_BALANCE_ROW_BYTES)
        .ok_or(SpotStateRootV7SemanticErrorV1::LengthOverflow(
            "lp_balances",
        ))?;
    2_usize
        .checked_add(SNAPSHOT_FIXED_BYTES)
        .and_then(|length| length.checked_add(balance_bytes))
        .and_then(|length| length.checked_add(pool_bytes))
        .and_then(|length| length.checked_add(lp_bytes))
        .and_then(|length| length.checked_add(64))
        .filter(|length| *length <= MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1)
        .ok_or(SpotStateRootV7SemanticErrorV1::LengthOverflow("host input"))
}

fn write_snapshot(
    output: &mut Vec<u8>,
    snapshot: &DexSnapshotV1,
) -> Result<(), SpotStateRootV7SemanticErrorV1> {
    write_balances(output, &snapshot.balances)?;
    write_pools(output, &snapshot.pools)?;
    write_lp_balances(output, &snapshot.lp_balances)?;
    output.extend_from_slice(&snapshot.fee_accumulator.dust.to_be_bytes());
    Ok(())
}

fn write_balances(
    output: &mut Vec<u8>,
    entries: &[DexBalanceEntryV1],
) -> Result<(), SpotStateRootV7SemanticErrorV1> {
    write_count(output, "balances", entries.len())?;
    for entry in entries {
        output.extend_from_slice(&decode_canonical_hex::<PUBKEY_BYTES>(
            &entry.pubkey,
            "balance.pubkey",
        )?);
        output.extend_from_slice(&decode_canonical_hex::<IDENTIFIER_BYTES>(
            &entry.asset,
            "balance.asset",
        )?);
        output.extend_from_slice(&entry.amount.to_be_bytes());
    }
    Ok(())
}

fn write_pools(
    output: &mut Vec<u8>,
    entries: &[DexPoolEntryV1],
) -> Result<(), SpotStateRootV7SemanticErrorV1> {
    write_count(output, "pools", entries.len())?;
    for entry in entries {
        for (value, field) in [
            (&entry.pool_id, "pool.pool_id"),
            (&entry.asset0, "pool.asset0"),
            (&entry.asset1, "pool.asset1"),
        ] {
            output.extend_from_slice(&decode_canonical_hex::<IDENTIFIER_BYTES>(value, field)?);
        }
        output.extend_from_slice(&entry.reserve0.to_be_bytes());
        output.extend_from_slice(&entry.reserve1.to_be_bytes());
        output.extend_from_slice(&entry.fee_bps.to_be_bytes());
        output.extend_from_slice(&entry.lp_supply.to_be_bytes());
        output.extend_from_slice(&entry.created_at.to_be_bytes());
    }
    Ok(())
}

fn write_lp_balances(
    output: &mut Vec<u8>,
    entries: &[DexLpBalanceEntryV1],
) -> Result<(), SpotStateRootV7SemanticErrorV1> {
    write_count(output, "lp_balances", entries.len())?;
    for entry in entries {
        output.extend_from_slice(&decode_canonical_hex::<PUBKEY_BYTES>(
            &entry.pubkey,
            "lp.pubkey",
        )?);
        output.extend_from_slice(&decode_canonical_hex::<IDENTIFIER_BYTES>(
            &entry.pool_id,
            "lp.pool_id",
        )?);
        output.extend_from_slice(&entry.amount.to_be_bytes());
    }
    Ok(())
}

fn read_snapshot(
    cursor: &mut CursorV1<'_>,
) -> Result<DexSnapshotV1, SpotStateRootV7SemanticErrorV1> {
    let balances = read_balances(cursor)?;
    let pools = read_pools(cursor)?;
    let lp_balances = read_lp_balances(cursor)?;
    Ok(DexSnapshotV1 {
        version: 1,
        balances,
        pools,
        lp_balances,
        fee_accumulator: FeeAccumulatorV1 {
            dust: cursor.read_u128("fee_accumulator.dust")?,
        },
        vault: None,
        oracle: None,
    })
}

fn read_balances(
    cursor: &mut CursorV1<'_>,
) -> Result<Vec<DexBalanceEntryV1>, SpotStateRootV7SemanticErrorV1> {
    let balance_count = cursor.read_count("balances")?;
    let mut balances = Vec::with_capacity(balance_count);
    let mut previous_balance = None;
    for _ in 0..balance_count {
        let pubkey = cursor.read_array::<PUBKEY_BYTES>("balance.pubkey")?;
        let asset = cursor.read_array::<IDENTIFIER_BYTES>("balance.asset")?;
        require_next_key("balances", &mut previous_balance, (pubkey, asset))?;
        balances.push(DexBalanceEntryV1 {
            pubkey: encode_canonical_hex(&pubkey),
            asset: encode_canonical_hex(&asset),
            amount: cursor.read_u128("balance.amount")?,
        });
    }
    Ok(balances)
}

fn read_pools(
    cursor: &mut CursorV1<'_>,
) -> Result<Vec<DexPoolEntryV1>, SpotStateRootV7SemanticErrorV1> {
    let pool_count = cursor.read_count("pools")?;
    let mut pools = Vec::with_capacity(pool_count);
    let mut previous_pool = None;
    for _ in 0..pool_count {
        let pool_id = cursor.read_array::<IDENTIFIER_BYTES>("pool.pool_id")?;
        require_next_key("pools", &mut previous_pool, pool_id)?;
        let asset0 = cursor.read_array::<IDENTIFIER_BYTES>("pool.asset0")?;
        let asset1 = cursor.read_array::<IDENTIFIER_BYTES>("pool.asset1")?;
        pools.push(DexPoolEntryV1 {
            pool_id: encode_canonical_hex(&pool_id),
            asset0: encode_canonical_hex(&asset0),
            asset1: encode_canonical_hex(&asset1),
            reserve0: cursor.read_u128("pool.reserve0")?,
            reserve1: cursor.read_u128("pool.reserve1")?,
            fee_bps: cursor.read_u32("pool.fee_bps")?,
            lp_supply: cursor.read_u128("pool.lp_supply")?,
            status: String::from("ACTIVE"),
            created_at: cursor.read_u64("pool.created_at")?,
        });
    }
    Ok(pools)
}

fn read_lp_balances(
    cursor: &mut CursorV1<'_>,
) -> Result<Vec<DexLpBalanceEntryV1>, SpotStateRootV7SemanticErrorV1> {
    let lp_count = cursor.read_count("lp_balances")?;
    let mut lp_balances = Vec::with_capacity(lp_count);
    let mut previous_lp = None;
    for _ in 0..lp_count {
        let pubkey = cursor.read_array::<PUBKEY_BYTES>("lp.pubkey")?;
        let pool_id = cursor.read_array::<IDENTIFIER_BYTES>("lp.pool_id")?;
        require_next_key("lp_balances", &mut previous_lp, (pubkey, pool_id))?;
        lp_balances.push(DexLpBalanceEntryV1 {
            pubkey: encode_canonical_hex(&pubkey),
            pool_id: encode_canonical_hex(&pool_id),
            amount: cursor.read_u128("lp.amount")?,
        });
    }
    Ok(lp_balances)
}

fn require_next_key<T: Copy + Ord>(
    section: &'static str,
    previous: &mut Option<T>,
    key: T,
) -> Result<(), SpotStateRootV7SemanticErrorV1> {
    if previous.is_some_and(|value| value >= key) {
        return Err(SpotStateRootV7SemanticErrorV1::NonCanonicalOrder(section));
    }
    *previous = Some(key);
    Ok(())
}

fn write_count(
    output: &mut Vec<u8>,
    section: &'static str,
    count: usize,
) -> Result<(), SpotStateRootV7SemanticErrorV1> {
    require_count(section, count)?;
    let count = u32::try_from(count)
        .map_err(|_| SpotStateRootV7SemanticErrorV1::LengthOverflow(section))?;
    output.extend_from_slice(&count.to_be_bytes());
    Ok(())
}

fn require_count(
    section: &'static str,
    count: usize,
) -> Result<(), SpotStateRootV7SemanticErrorV1> {
    if count > MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1 {
        return Err(SpotStateRootV7SemanticErrorV1::CountTooLarge {
            section,
            actual: count,
            maximum: MAX_RESTRICTED_STATE_SECTION_ENTRIES_V1,
        });
    }
    Ok(())
}

fn decode_canonical_hex<const N: usize>(
    value: &str,
    field: &'static str,
) -> Result<[u8; N], SpotStateRootV7SemanticErrorV1> {
    let bytes = value.as_bytes();
    if bytes.len() != 2 + 2 * N
        || !value.starts_with("0x")
        || !bytes[2..]
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
    {
        return Err(SpotStateRootV7SemanticErrorV1::NonCanonicalIdentifier(
            field,
        ));
    }
    let mut decoded = [0_u8; N];
    for (index, pair) in bytes[2..].chunks_exact(2).enumerate() {
        decoded[index] = (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1]);
    }
    Ok(decoded)
}

fn encode_canonical_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(2 + bytes.len() * 2);
    output.push_str("0x");
    for byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

const fn hex_nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => 0,
    }
}

struct CursorV1<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> CursorV1<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn read_u16(&mut self, field: &'static str) -> Result<u16, SpotStateRootV7SemanticErrorV1> {
        Ok(u16::from_be_bytes(self.read_array(field)?))
    }

    fn read_u32(&mut self, field: &'static str) -> Result<u32, SpotStateRootV7SemanticErrorV1> {
        Ok(u32::from_be_bytes(self.read_array(field)?))
    }

    fn read_u64(&mut self, field: &'static str) -> Result<u64, SpotStateRootV7SemanticErrorV1> {
        Ok(u64::from_be_bytes(self.read_array(field)?))
    }

    fn read_u128(&mut self, field: &'static str) -> Result<u128, SpotStateRootV7SemanticErrorV1> {
        Ok(u128::from_be_bytes(self.read_array(field)?))
    }

    fn read_count(
        &mut self,
        section: &'static str,
    ) -> Result<usize, SpotStateRootV7SemanticErrorV1> {
        let count = usize::try_from(self.read_u32(section)?)
            .map_err(|_| SpotStateRootV7SemanticErrorV1::LengthOverflow(section))?;
        require_count(section, count)?;
        Ok(count)
    }

    fn read_array<const N: usize>(
        &mut self,
        field: &'static str,
    ) -> Result<[u8; N], SpotStateRootV7SemanticErrorV1> {
        let end = self
            .offset
            .checked_add(N)
            .ok_or(SpotStateRootV7SemanticErrorV1::LengthOverflow(field))?;
        let bytes = self
            .bytes
            .get(self.offset..end)
            .ok_or(SpotStateRootV7SemanticErrorV1::Truncated(field))?;
        self.offset = end;
        bytes
            .try_into()
            .map_err(|_| SpotStateRootV7SemanticErrorV1::Truncated(field))
    }

    const fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}
