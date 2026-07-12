use zenodex_zrpf_risc0_semantic_shared::{
    SpotSettlementAuthorizationInputV1, ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V2,
};

pub fn independent_frame(
    proposal_bytes: &[u8],
    authorization: SpotSettlementAuthorizationInputV1,
    witness_bytes: &[u8],
    certificate_bytes: &[u8],
) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V2.to_be_bytes());
    bytes.extend_from_slice(&u32::try_from(proposal_bytes.len()).unwrap().to_be_bytes());
    bytes.extend_from_slice(proposal_bytes);
    bytes.extend_from_slice(authorization.authorization_subject_id.as_bytes());
    bytes.extend_from_slice(authorization.authorization_scope_id.as_bytes());
    bytes.extend_from_slice(&authorization.authorization_nonce.to_be_bytes());
    bytes.extend_from_slice(authorization.authorization_grant_id.as_bytes());
    bytes.extend_from_slice(&u32::try_from(witness_bytes.len()).unwrap().to_be_bytes());
    bytes.extend_from_slice(witness_bytes);
    bytes.extend_from_slice(
        &u32::try_from(certificate_bytes.len())
            .unwrap()
            .to_be_bytes(),
    );
    bytes.extend_from_slice(certificate_bytes);
    bytes
}

pub fn read_length(bytes: &[u8], offset: usize) -> usize {
    usize::try_from(u32::from_be_bytes(
        bytes[offset..offset + 4].try_into().unwrap(),
    ))
    .unwrap()
}
