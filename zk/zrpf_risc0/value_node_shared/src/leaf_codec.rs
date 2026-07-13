use alloc::string::String;
use alloc::vec::Vec;

use tau_state_proof_risc0_shared::RecursiveAssetDeltaRowV1;
use zenodex_zrpf_protocol_v3::MAX_NODE_JOURNAL_BYTES_V3;
use zenodex_zrpf_risc0_semantic_shared::{
    SpotMintAuthorityGrantV1, SpotRepresentedValuePolicyV1, SpotValueLeafOpeningV1,
    CANONICAL_SPOT_ASSET_NAME_BYTES_V1, MAX_SPOT_ASSET_ROWS_PER_LEAF_V1, MAX_SPOT_LANE_ID_BYTES_V1,
    MAX_SPOT_MINT_GRANTS_V1,
};

use crate::cursor::Cursor;
use crate::SpotValueLeafInputErrorV4;

pub const SPOT_VALUE_LEAF_INPUT_SCHEMA_V4: u16 = 4;
pub const SPOT_VALUE_LEAF_WITNESS_SCHEMA_V4: u16 = 4;

const ROW_FIXED_BYTES_V4: usize = 2 + CANONICAL_SPOT_ASSET_NAME_BYTES_V1 + (4 * 16) + 32;
const GRANT_FIXED_BYTES_V4: usize = 32 + 32 + 16;
pub const MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4: usize = 2
    + 32
    + 2
    + MAX_SPOT_LANE_ID_BYTES_V1
    + 64
    + 1
    + MAX_SPOT_ASSET_ROWS_PER_LEAF_V1 * ROW_FIXED_BYTES_V4
    + 32
    + 1
    + MAX_SPOT_MINT_GRANTS_V1 * GRANT_FIXED_BYTES_V4;
pub const MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4: usize =
    2 + 32 + 2 + MAX_NODE_JOURNAL_BYTES_V3 + 2 + MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4;

const _: () = assert!(MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4 == 13_126);
const _: () = assert!(MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4 == 17_260);

#[derive(Clone, Debug, PartialEq, Eq)]
/// Opaque bounded framing decoded before adapter-receipt verification.
pub struct RawSpotValueLeafInputV4 {
    expected_self_image_id: [u32; 8],
    adapter_journal_bytes: Vec<u8>,
    witness_bytes: Vec<u8>,
}

impl RawSpotValueLeafInputV4 {
    pub fn new(
        expected_self_image_id: [u32; 8],
        adapter_journal_bytes: Vec<u8>,
        witness_bytes: Vec<u8>,
    ) -> Result<Self, SpotValueLeafInputErrorV4> {
        let input = Self {
            expected_self_image_id,
            adapter_journal_bytes,
            witness_bytes,
        };
        input.validate()?;
        Ok(input)
    }

    pub const fn expected_self_image_id(&self) -> [u32; 8] {
        self.expected_self_image_id
    }

    pub fn adapter_journal_bytes(&self) -> &[u8] {
        &self.adapter_journal_bytes
    }

    pub fn witness_bytes(&self) -> &[u8] {
        &self.witness_bytes
    }

    fn validate(&self) -> Result<(), SpotValueLeafInputErrorV4> {
        if self.expected_self_image_id.iter().all(|word| *word == 0) {
            return Err(SpotValueLeafInputErrorV4::ZeroSelfImageId);
        }
        validate_journal_length(self.adapter_journal_bytes.len())?;
        validate_witness_length(self.witness_bytes.len())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Semantic witness intended for decoding after the exact adapter claim is verified.
pub struct SpotValueLeafWitnessV4 {
    semantic_opening: [u8; 32],
    value_opening: SpotValueLeafOpeningV1,
    policy: SpotRepresentedValuePolicyV1,
}

impl SpotValueLeafWitnessV4 {
    pub fn new(
        semantic_opening: [u8; 32],
        value_opening: SpotValueLeafOpeningV1,
        policy: SpotRepresentedValuePolicyV1,
    ) -> Result<Self, SpotValueLeafInputErrorV4> {
        if semantic_opening == [0; 32] {
            return Err(SpotValueLeafInputErrorV4::InvalidSemanticOpening);
        }
        Ok(Self {
            semantic_opening,
            value_opening,
            policy,
        })
    }

    pub const fn semantic_opening(&self) -> [u8; 32] {
        self.semantic_opening
    }

    pub const fn value_opening(&self) -> &SpotValueLeafOpeningV1 {
        &self.value_opening
    }

    pub const fn policy(&self) -> &SpotRepresentedValuePolicyV1 {
        &self.policy
    }
}

pub fn encode_raw_spot_value_leaf_input_v4(
    input: &RawSpotValueLeafInputV4,
) -> Result<Vec<u8>, SpotValueLeafInputErrorV4> {
    input.validate()?;
    let total = 2usize
        .checked_add(32)
        .and_then(|value| value.checked_add(2 + input.adapter_journal_bytes.len()))
        .and_then(|value| value.checked_add(2 + input.witness_bytes.len()))
        .ok_or(SpotValueLeafInputErrorV4::LengthOverflow)?;
    if total > MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4 {
        return Err(SpotValueLeafInputErrorV4::InputTooLarge {
            actual: total,
            maximum: MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4,
        });
    }
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&SPOT_VALUE_LEAF_INPUT_SCHEMA_V4.to_be_bytes());
    for word in input.expected_self_image_id {
        bytes.extend_from_slice(&word.to_be_bytes());
    }
    write_sized_bytes(&mut bytes, &input.adapter_journal_bytes)?;
    write_sized_bytes(&mut bytes, &input.witness_bytes)?;
    Ok(bytes)
}

pub fn decode_exact_raw_spot_value_leaf_input_v4(
    bytes: &[u8],
) -> Result<RawSpotValueLeafInputV4, SpotValueLeafInputErrorV4> {
    validate_total_input(bytes, MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4)?;
    let mut cursor = Cursor::new(bytes);
    let schema = cursor.read_u16()?;
    if schema != SPOT_VALUE_LEAF_INPUT_SCHEMA_V4 {
        return Err(SpotValueLeafInputErrorV4::InvalidSchema(schema));
    }
    let mut expected_self_image_id = [0u32; 8];
    for word in &mut expected_self_image_id {
        *word = cursor.read_u32()?;
    }
    let journal_length = usize::from(cursor.read_u16()?);
    validate_journal_length(journal_length)?;
    let adapter_journal_bytes = cursor.read(journal_length)?.to_vec();
    let witness_length = usize::from(cursor.read_u16()?);
    validate_witness_length(witness_length)?;
    let witness_bytes = cursor.read(witness_length)?.to_vec();
    cursor.finish()?;
    let input =
        RawSpotValueLeafInputV4::new(expected_self_image_id, adapter_journal_bytes, witness_bytes)?;
    if encode_raw_spot_value_leaf_input_v4(&input)? != bytes {
        return Err(SpotValueLeafInputErrorV4::NonCanonicalEncoding);
    }
    Ok(input)
}

pub fn encode_spot_value_leaf_witness_v4(
    witness: &SpotValueLeafWitnessV4,
) -> Result<Vec<u8>, SpotValueLeafInputErrorV4> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&SPOT_VALUE_LEAF_WITNESS_SCHEMA_V4.to_be_bytes());
    bytes.extend_from_slice(&witness.semantic_opening);
    write_string(&mut bytes, witness.value_opening.lane_id())?;
    bytes.extend_from_slice(&witness.value_opening.raw_pre_state_root());
    bytes.extend_from_slice(&witness.value_opening.raw_post_state_root());
    write_rows(&mut bytes, witness.value_opening.asset_rows())?;
    bytes.extend_from_slice(&witness.policy.public_policy_hash());
    write_grants(&mut bytes, witness.policy.grants())?;
    if bytes.len() > MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4 {
        return Err(SpotValueLeafInputErrorV4::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_spot_value_leaf_witness_v4(
    bytes: &[u8],
) -> Result<SpotValueLeafWitnessV4, SpotValueLeafInputErrorV4> {
    validate_total_input(bytes, MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4)?;
    let mut cursor = Cursor::new(bytes);
    let schema = cursor.read_u16()?;
    if schema != SPOT_VALUE_LEAF_WITNESS_SCHEMA_V4 {
        return Err(SpotValueLeafInputErrorV4::InvalidSchema(schema));
    }
    let semantic_opening = cursor.read_array()?;
    if semantic_opening == [0; 32] {
        return Err(SpotValueLeafInputErrorV4::InvalidSemanticOpening);
    }
    let lane_id = read_lane_id(&mut cursor)?;
    let raw_pre_state_root = cursor.read_array()?;
    let raw_post_state_root = cursor.read_array()?;
    let rows = read_rows(&mut cursor)?;
    let public_policy_hash = cursor.read_array()?;
    let grants = read_grants(&mut cursor)?;
    cursor.finish()?;
    let opening =
        SpotValueLeafOpeningV1::new(lane_id, raw_pre_state_root, raw_post_state_root, rows)
            .map_err(|_| SpotValueLeafInputErrorV4::WitnessRejected)?;
    let policy = SpotRepresentedValuePolicyV1::new(public_policy_hash, grants)
        .map_err(|_| SpotValueLeafInputErrorV4::WitnessRejected)?;
    let witness = SpotValueLeafWitnessV4::new(semantic_opening, opening, policy)?;
    if encode_spot_value_leaf_witness_v4(&witness)? != bytes {
        return Err(SpotValueLeafInputErrorV4::NonCanonicalEncoding);
    }
    Ok(witness)
}

fn write_rows(
    output: &mut Vec<u8>,
    rows: &[RecursiveAssetDeltaRowV1],
) -> Result<(), SpotValueLeafInputErrorV4> {
    let count = u8::try_from(rows.len()).map_err(|_| SpotValueLeafInputErrorV4::LengthOverflow)?;
    if rows.len() > MAX_SPOT_ASSET_ROWS_PER_LEAF_V1 {
        return Err(SpotValueLeafInputErrorV4::InvalidRowCount(rows.len()));
    }
    output.push(count);
    for (index, row) in rows.iter().enumerate() {
        if row.asset_id.is_empty() || row.asset_id.len() > CANONICAL_SPOT_ASSET_NAME_BYTES_V1 {
            return Err(SpotValueLeafInputErrorV4::InvalidAssetIdLength {
                row: index,
                length: row.asset_id.len(),
            });
        }
        write_string(output, &row.asset_id)?;
        for value in [
            row.debit_atoms,
            row.credit_atoms,
            row.authorized_mint_atoms,
            row.authorized_burn_atoms,
        ] {
            output.extend_from_slice(&value.to_be_bytes());
        }
        output.extend_from_slice(&row.authority_root);
    }
    Ok(())
}

fn read_rows(
    cursor: &mut Cursor<'_>,
) -> Result<Vec<RecursiveAssetDeltaRowV1>, SpotValueLeafInputErrorV4> {
    let count = usize::from(cursor.read_u8()?);
    if count > MAX_SPOT_ASSET_ROWS_PER_LEAF_V1 {
        return Err(SpotValueLeafInputErrorV4::InvalidRowCount(count));
    }
    let mut rows = Vec::with_capacity(count);
    for row in 0..count {
        let asset_id = read_asset_id(cursor, row)?;
        rows.push(RecursiveAssetDeltaRowV1 {
            asset_id,
            debit_atoms: cursor.read_u128()?,
            credit_atoms: cursor.read_u128()?,
            authorized_mint_atoms: cursor.read_u128()?,
            authorized_burn_atoms: cursor.read_u128()?,
            authority_root: cursor.read_array()?,
        });
    }
    Ok(rows)
}

fn write_grants(
    output: &mut Vec<u8>,
    grants: &[SpotMintAuthorityGrantV1],
) -> Result<(), SpotValueLeafInputErrorV4> {
    if grants.len() > MAX_SPOT_MINT_GRANTS_V1 {
        return Err(SpotValueLeafInputErrorV4::InvalidGrantCount(grants.len()));
    }
    output.push(u8::try_from(grants.len()).map_err(|_| SpotValueLeafInputErrorV4::LengthOverflow)?);
    for grant in grants {
        output.extend_from_slice(&grant.asset_id());
        output.extend_from_slice(&grant.legacy_authority_root());
        output.extend_from_slice(&grant.max_atoms_per_value_root().to_be_bytes());
    }
    Ok(())
}

fn read_grants(
    cursor: &mut Cursor<'_>,
) -> Result<Vec<SpotMintAuthorityGrantV1>, SpotValueLeafInputErrorV4> {
    let count = usize::from(cursor.read_u8()?);
    if count > MAX_SPOT_MINT_GRANTS_V1 {
        return Err(SpotValueLeafInputErrorV4::InvalidGrantCount(count));
    }
    let mut grants = Vec::with_capacity(count);
    for _ in 0..count {
        grants.push(
            SpotMintAuthorityGrantV1::new(
                cursor.read_array()?,
                cursor.read_array()?,
                cursor.read_u128()?,
            )
            .map_err(|_| SpotValueLeafInputErrorV4::WitnessRejected)?,
        );
    }
    Ok(grants)
}

fn write_string(output: &mut Vec<u8>, value: &str) -> Result<(), SpotValueLeafInputErrorV4> {
    write_sized_bytes(output, value.as_bytes())
}

fn read_lane_id(cursor: &mut Cursor<'_>) -> Result<String, SpotValueLeafInputErrorV4> {
    let length = usize::from(cursor.read_u16()?);
    if length == 0 || length > MAX_SPOT_LANE_ID_BYTES_V1 {
        return Err(SpotValueLeafInputErrorV4::InvalidLaneLength(length));
    }
    read_utf8(cursor, length)
}

fn read_asset_id(cursor: &mut Cursor<'_>, row: usize) -> Result<String, SpotValueLeafInputErrorV4> {
    let length = usize::from(cursor.read_u16()?);
    if length == 0 || length > CANONICAL_SPOT_ASSET_NAME_BYTES_V1 {
        return Err(SpotValueLeafInputErrorV4::InvalidAssetIdLength { row, length });
    }
    read_utf8(cursor, length)
}

fn read_utf8(cursor: &mut Cursor<'_>, length: usize) -> Result<String, SpotValueLeafInputErrorV4> {
    String::from_utf8(cursor.read(length)?.to_vec())
        .map_err(|_| SpotValueLeafInputErrorV4::InvalidUtf8)
}

fn write_sized_bytes(output: &mut Vec<u8>, value: &[u8]) -> Result<(), SpotValueLeafInputErrorV4> {
    let length =
        u16::try_from(value.len()).map_err(|_| SpotValueLeafInputErrorV4::LengthOverflow)?;
    output.extend_from_slice(&length.to_be_bytes());
    output.extend_from_slice(value);
    Ok(())
}

fn validate_total_input(bytes: &[u8], maximum: usize) -> Result<(), SpotValueLeafInputErrorV4> {
    if bytes.is_empty() {
        return Err(SpotValueLeafInputErrorV4::EmptyInput);
    }
    if bytes.len() > maximum {
        return Err(SpotValueLeafInputErrorV4::InputTooLarge {
            actual: bytes.len(),
            maximum,
        });
    }
    Ok(())
}

fn validate_journal_length(length: usize) -> Result<(), SpotValueLeafInputErrorV4> {
    if length == 0 || length > MAX_NODE_JOURNAL_BYTES_V3 {
        Err(SpotValueLeafInputErrorV4::InvalidAdapterJournalLength(
            length,
        ))
    } else {
        Ok(())
    }
}

fn validate_witness_length(length: usize) -> Result<(), SpotValueLeafInputErrorV4> {
    if length == 0 || length > MAX_SPOT_VALUE_LEAF_WITNESS_BYTES_V4 {
        Err(SpotValueLeafInputErrorV4::InvalidWitnessLength(length))
    } else {
        Ok(())
    }
}
