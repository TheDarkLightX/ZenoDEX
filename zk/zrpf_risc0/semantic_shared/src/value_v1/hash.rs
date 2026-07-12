use super::*;

pub(super) fn validate_grants(
    public_policy_hash: [u8; 32],
    grants: &[SpotMintAuthorityGrantV1],
) -> Result<(), SpotSemanticValueErrorV1> {
    if grants
        .windows(2)
        .any(|pair| pair[0].asset_id >= pair[1].asset_id)
    {
        return Err(SpotSemanticValueErrorV1::NonCanonicalGrantOrder);
    }
    for grant in grants {
        let asset_name = canonical_asset_name(grant.asset_id);
        let expected = recursive_authority_scope_root_v1(
            public_policy_hash,
            "spot",
            &asset_name,
            RECURSIVE_AUTHORITY_EFFECT_MINT_V1,
        )
        .map_err(|_| SpotSemanticValueErrorV1::LegacyDerivation("mint_authority_root"))?;
        if grant.legacy_authority_root != expected {
            return Err(SpotSemanticValueErrorV1::InvalidGrant);
        }
    }
    Ok(())
}

pub(super) fn authority_grants_root(
    grants: &[SpotMintAuthorityGrantV1],
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(AUTHORITY_GRANTS_ROOT_DOMAIN_V1)?;
    write_u32(&mut hasher, checked_len_u32(grants.len(), "grant_count")?);
    for grant in grants {
        write_bytes32(&mut hasher, &grant.asset_id);
        write_bytes32(&mut hasher, &grant.legacy_authority_root);
        write_u128(&mut hasher, grant.max_atoms_per_value_root);
    }
    commitment(hasher.finalize().into())
}

pub(super) fn asset_flows_root(
    flows: &[SpotCanonicalAssetFlowV1],
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(ASSET_FLOWS_ROOT_DOMAIN_V1)?;
    write_u32(
        &mut hasher,
        checked_len_u32(flows.len(), "asset_flow_count")?,
    );
    for flow in flows {
        write_bytes32(&mut hasher, &flow.asset_id);
        write_u128(&mut hasher, flow.outflow_atoms);
        write_u128(&mut hasher, flow.inflow_atoms);
        write_u128(&mut hasher, flow.issued_atoms);
        write_u128(&mut hasher, flow.destroyed_atoms);
    }
    commitment(hasher.finalize().into())
}

pub(super) fn authority_uses_root(
    uses: &[SpotMintAuthorityUseV1],
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(AUTHORITY_USES_ROOT_DOMAIN_V1)?;
    write_u32(
        &mut hasher,
        checked_len_u32(uses.len(), "authority_use_count")?,
    );
    for use_record in uses {
        write_bytes32(&mut hasher, &use_record.source_claim_id);
        write_u64(&mut hasher, use_record.leaf_ordinal);
        write_bytes32(&mut hasher, &use_record.asset_id);
        write_u128(&mut hasher, use_record.atoms);
        write_bytes32(&mut hasher, &use_record.legacy_authority_root);
    }
    commitment(hasher.finalize().into())
}

pub(super) fn state_chain_root(
    records: &[StateRecordV1],
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(STATE_CHAIN_ROOT_DOMAIN_V1)?;
    write_u32(
        &mut hasher,
        checked_len_u32(records.len(), "state_record_count")?,
    );
    for record in records {
        write_bytes32(&mut hasher, &record.source_claim_id);
        write_u64(&mut hasher, record.leaf_ordinal);
        write_bytes32(&mut hasher, &record.transaction_root);
        write_bytes32(&mut hasher, &record.raw_pre_state_root);
        write_bytes32(&mut hasher, &record.raw_post_state_root);
    }
    commitment(hasher.finalize().into())
}

pub(super) fn semantic_leaf_records_root(
    leaves: &[ProposedSemanticLeafV1],
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(SEMANTIC_LEAF_RECORDS_ROOT_DOMAIN_V2)?;
    write_u32(
        &mut hasher,
        checked_len_u32(leaves.len(), "semantic_leaf_record_count")?,
    );
    for leaf in leaves {
        let leaf_hash = leaf
            .canonical_hash()
            .map_err(SpotSemanticValueErrorV1::Protocol)?;
        write_bytes32(&mut hasher, leaf_hash.as_bytes());
    }
    commitment(hasher.finalize().into())
}

pub(super) fn ordered_transaction_roots_root(
    records: &[StateRecordV1],
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(ORDERED_TRANSACTION_ROOTS_DOMAIN_V1)?;
    write_u32(
        &mut hasher,
        checked_len_u32(records.len(), "ordered_transaction_root_count")?,
    );
    for record in records {
        write_bytes32(&mut hasher, &record.transaction_root);
    }
    commitment(hasher.finalize().into())
}

pub(super) fn value_subtree_root(
    input: ValueSubtreeRootInputV2,
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(VALUE_SUBTREE_ROOT_DOMAIN_V2)?;
    for value in [
        spot_represented_value_profile_id_v1()?,
        spot_accounting_domain_id_v1()?,
        spot_atoms_unit_id_v1()?,
        spot_state_root_scheme_id_v1()?,
        input.scope_hash,
        input.lane_id_hash,
    ] {
        write_bytes32(&mut hasher, value.as_bytes());
    }
    write_u64(&mut hasher, input.partition_start);
    write_u64(&mut hasher, input.partition_end_exclusive);
    write_bytes32(&mut hasher, &input.raw_pre);
    write_bytes32(&mut hasher, &input.raw_post);
    write_u64(&mut hasher, input.leaf_count);
    write_u64(&mut hasher, input.row_count);
    for value in [
        input.semantic_leaf_records_root,
        input.ordered_transaction_roots_root,
        input.state_chain_root,
        input.authority_grants_root,
        input.asset_flows_root,
        input.authority_uses_root,
    ] {
        write_bytes32(&mut hasher, value.as_bytes());
    }
    commitment(hasher.finalize().into())
}

pub(super) fn semantic_value_root(
    base_proposal: &ProposedSemanticEpochV1,
    lane_id_hash: CommitmentV3,
    raw_pre: [u8; 32],
    raw_post: [u8; 32],
    leaf_count: u64,
    row_count: u64,
    commitments: &SpotSemanticValueCommitmentsV1,
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(SEMANTIC_VALUE_ROOT_DOMAIN_V1)?;
    write_bytes32(
        &mut hasher,
        base_proposal
            .scope()
            .canonical_hash()
            .map_err(SpotSemanticValueErrorV1::Structural)?
            .as_bytes(),
    );
    write_bytes32(&mut hasher, lane_id_hash.as_bytes());
    write_bytes32(&mut hasher, &raw_pre);
    write_bytes32(&mut hasher, &raw_post);
    write_u64(&mut hasher, leaf_count);
    write_u64(&mut hasher, row_count);
    write_bytes32(&mut hasher, commitments.canonical_hash()?.as_bytes());
    commitment(hasher.finalize().into())
}

pub(super) fn semantic_value_proposal_hash(
    base_proposal: &ProposedSemanticEpochV1,
    semantic_value_root: CommitmentV3,
    authority_grants_root: CommitmentV3,
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(SEMANTIC_VALUE_PROPOSAL_DOMAIN_V1)?;
    write_bytes32(
        &mut hasher,
        base_proposal
            .proposal_hash()
            .map_err(SpotSemanticValueErrorV1::Protocol)?
            .as_bytes(),
    );
    write_bytes32(&mut hasher, semantic_value_root.as_bytes());
    write_bytes32(&mut hasher, authority_grants_root.as_bytes());
    commitment(hasher.finalize().into())
}

/// Return the fixed identifier for raw Spot `u128` atoms.
pub fn spot_atoms_unit_id_v1() -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    hash_label(ATOMS_UNIT_DOMAIN_V1, b"spot_raw_u128_atoms")
}

/// Return the identifier for authenticated represented external-effect accounting.
pub fn spot_accounting_domain_id_v1() -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    hash_label(
        ACCOUNTING_DOMAIN_ID_V1,
        b"authenticated_represented_external_effect_rows",
    )
}

/// Bind the raw-root interpretation to the pinned Spot image and leaf profile.
pub fn spot_state_root_scheme_id_v1() -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(STATE_ROOT_SCHEME_DOMAIN_V1)?;
    for word in PINNED_SPOT_LEAF_IMAGE_ID_V1 {
        hasher.update(word.to_le_bytes());
    }
    write_str(&mut hasher, RECURSIVE_SPOT_LEAF_PROFILE_V1)?;
    hash_to_commitment(hasher)
}

/// Bind every active Spot represented-value rule and bound into one profile ID.
pub fn spot_represented_value_profile_id_v1() -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(VALUE_PROFILE_DOMAIN_V1)?;
    write_bytes32(&mut hasher, spot_atoms_unit_id_v1()?.as_bytes());
    write_bytes32(&mut hasher, spot_accounting_domain_id_v1()?.as_bytes());
    write_bytes32(&mut hasher, spot_state_root_scheme_id_v1()?.as_bytes());
    for bound in [
        MAX_SPOT_VALUE_LEAVES_V1,
        MAX_SPOT_VALUE_SUBTREE_LEAVES_V2,
        MAX_SPOT_ASSET_ROWS_PER_LEAF_V1,
        MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2,
        MAX_SPOT_MINT_GRANTS_V1,
        MAX_SPOT_LANE_ID_BYTES_V1,
        CANONICAL_SPOT_ASSET_NAME_BYTES_V1,
    ] {
        write_u64(
            &mut hasher,
            u64::try_from(bound)
                .map_err(|_| SpotSemanticValueErrorV1::ArithmeticOverflow("profile_bound"))?,
        );
    }
    for rule in [
        "asset_codec=lowercase_0x_plus_64_hex",
        "state=single_lane_raw_post_equals_next_raw_pre",
        "flow=outflow_plus_issued_equals_inflow_plus_destroyed",
        "supply=spot_pure_mint_only",
        "grant_cap=per_closed_value_root",
        "transactions=ordered_unique_leaf_transaction_root_commitments",
        "arithmetic=checked_u128",
    ] {
        write_str(&mut hasher, rule)?;
    }
    hash_to_commitment(hasher)
}

/// Encode a 32-byte Spot asset identity as lowercase `0x` plus 64 hex digits.
pub fn canonical_spot_asset_name_v1(asset_id: [u8; 32]) -> String {
    canonical_asset_name(asset_id)
}

pub(super) fn hash_lane_id(lane_id: &str) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(LANE_ID_HASH_DOMAIN_V1)?;
    write_str(&mut hasher, lane_id)?;
    hash_to_commitment(hasher)
}

pub(super) fn hash_label(
    domain: &[u8],
    label: &[u8],
) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    let mut hasher = domain_hasher(domain)?;
    write_u32(&mut hasher, checked_len_u32(label.len(), "label_length")?);
    hasher.update(label);
    hash_to_commitment(hasher)
}

pub(super) fn domain_hasher(domain: &[u8]) -> Result<Sha256, SpotSemanticValueErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| SpotSemanticValueErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

pub(super) fn hash_to_commitment(hasher: Sha256) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    commitment(hasher.finalize().into())
}

pub(super) fn commitment(bytes: [u8; 32]) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
    CommitmentV3::new(bytes).map_err(SpotSemanticValueErrorV1::Structural)
}

pub(super) fn checked_len_u32(
    length: usize,
    field: &'static str,
) -> Result<u32, SpotSemanticValueErrorV1> {
    u32::try_from(length).map_err(|_| SpotSemanticValueErrorV1::ArithmeticOverflow(field))
}

pub(super) fn checked_add(
    left: u128,
    right: u128,
    field: &'static str,
) -> Result<u128, SpotSemanticValueErrorV1> {
    left.checked_add(right)
        .ok_or(SpotSemanticValueErrorV1::ArithmeticOverflow(field))
}

pub(super) fn valid_lane_id(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= MAX_SPOT_LANE_ID_BYTES_V1
        && value.bytes().all(|byte| {
            byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b':' | b'/' | b'-')
        })
}

pub(super) fn decode_canonical_asset_id(value: &str) -> Option<[u8; 32]> {
    let bytes = value.as_bytes();
    if bytes.len() != 66 || &bytes[..2] != b"0x" {
        return None;
    }
    let mut decoded = [0u8; 32];
    for (index, pair) in bytes[2..].chunks_exact(2).enumerate() {
        let high = decode_lower_hex(pair[0])?;
        let low = decode_lower_hex(pair[1])?;
        decoded[index] = (high << 4) | low;
    }
    Some(decoded)
}

pub(super) fn decode_lower_hex(value: u8) -> Option<u8> {
    match value {
        b'0'..=b'9' => Some(value - b'0'),
        b'a'..=b'f' => Some(value - b'a' + 10),
        _ => None,
    }
}

pub(super) fn canonical_asset_name(asset_id: [u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(66);
    result.push_str("0x");
    for byte in asset_id {
        result.push(char::from(HEX[usize::from(byte >> 4)]));
        result.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    result
}

pub(super) fn write_bytes32(hasher: &mut Sha256, value: &[u8; 32]) {
    hasher.update(value);
}

pub(super) fn write_u32(hasher: &mut Sha256, value: u32) {
    hasher.update(value.to_be_bytes());
}

pub(super) fn write_u64(hasher: &mut Sha256, value: u64) {
    hasher.update(value.to_be_bytes());
}

pub(super) fn write_u128(hasher: &mut Sha256, value: u128) {
    hasher.update(value.to_be_bytes());
}

pub(super) fn write_str(hasher: &mut Sha256, value: &str) -> Result<(), SpotSemanticValueErrorV1> {
    write_u32(hasher, checked_len_u32(value.len(), "string_length")?);
    hasher.update(value.as_bytes());
    Ok(())
}
