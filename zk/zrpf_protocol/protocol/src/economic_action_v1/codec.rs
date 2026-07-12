use alloc::vec::Vec;

use super::{
    AuthorizationConsumptionNullifierV1, AuthorizationGrantSpendNullifierV1, EconomicActionErrorV1,
    EconomicActionRecordV1, MAX_AUTHORIZATION_CONSUMPTION_NULLIFIER_BYTES_V1,
    MAX_AUTHORIZATION_GRANT_SPEND_NULLIFIER_BYTES_V1, MAX_ECONOMIC_ACTION_RECORD_BYTES_V1,
};

pub fn encode_economic_action_record_v1(
    record: &EconomicActionRecordV1,
) -> Result<Vec<u8>, EconomicActionErrorV1> {
    record.validate_self_consistency()?;
    let bytes = postcard::to_allocvec(record).map_err(|_| EconomicActionErrorV1::PostcardDecode)?;
    if bytes.len() > MAX_ECONOMIC_ACTION_RECORD_BYTES_V1 {
        return Err(EconomicActionErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_ECONOMIC_ACTION_RECORD_BYTES_V1,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_economic_action_record_v1(
    bytes: &[u8],
) -> Result<EconomicActionRecordV1, EconomicActionErrorV1> {
    require_bounded_input(bytes, MAX_ECONOMIC_ACTION_RECORD_BYTES_V1)?;
    let (record, remainder): (EconomicActionRecordV1, &[u8]) =
        postcard::take_from_bytes(bytes).map_err(|_| EconomicActionErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(EconomicActionErrorV1::TrailingBytes);
    }
    if encode_economic_action_record_v1(&record)?.as_slice() != bytes {
        return Err(EconomicActionErrorV1::NonCanonicalEncoding);
    }
    Ok(record)
}

pub fn encode_authorization_consumption_nullifier_v1(
    nullifier: AuthorizationConsumptionNullifierV1,
) -> Result<Vec<u8>, EconomicActionErrorV1> {
    let bytes =
        postcard::to_allocvec(&nullifier).map_err(|_| EconomicActionErrorV1::PostcardDecode)?;
    if bytes.len() > MAX_AUTHORIZATION_CONSUMPTION_NULLIFIER_BYTES_V1 {
        return Err(EconomicActionErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_AUTHORIZATION_CONSUMPTION_NULLIFIER_BYTES_V1,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_authorization_consumption_nullifier_v1(
    bytes: &[u8],
) -> Result<AuthorizationConsumptionNullifierV1, EconomicActionErrorV1> {
    require_bounded_input(bytes, MAX_AUTHORIZATION_CONSUMPTION_NULLIFIER_BYTES_V1)?;
    let (nullifier, remainder): (AuthorizationConsumptionNullifierV1, &[u8]) =
        postcard::take_from_bytes(bytes).map_err(|_| EconomicActionErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(EconomicActionErrorV1::TrailingBytes);
    }
    if encode_authorization_consumption_nullifier_v1(nullifier)?.as_slice() != bytes {
        return Err(EconomicActionErrorV1::NonCanonicalEncoding);
    }
    Ok(nullifier)
}

pub fn encode_authorization_grant_spend_nullifier_v1(
    nullifier: AuthorizationGrantSpendNullifierV1,
) -> Result<Vec<u8>, EconomicActionErrorV1> {
    let bytes =
        postcard::to_allocvec(&nullifier).map_err(|_| EconomicActionErrorV1::PostcardDecode)?;
    if bytes.len() > MAX_AUTHORIZATION_GRANT_SPEND_NULLIFIER_BYTES_V1 {
        return Err(EconomicActionErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_AUTHORIZATION_GRANT_SPEND_NULLIFIER_BYTES_V1,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_authorization_grant_spend_nullifier_v1(
    bytes: &[u8],
) -> Result<AuthorizationGrantSpendNullifierV1, EconomicActionErrorV1> {
    require_bounded_input(bytes, MAX_AUTHORIZATION_GRANT_SPEND_NULLIFIER_BYTES_V1)?;
    let (nullifier, remainder): (AuthorizationGrantSpendNullifierV1, &[u8]) =
        postcard::take_from_bytes(bytes).map_err(|_| EconomicActionErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(EconomicActionErrorV1::TrailingBytes);
    }
    if encode_authorization_grant_spend_nullifier_v1(nullifier)?.as_slice() != bytes {
        return Err(EconomicActionErrorV1::NonCanonicalEncoding);
    }
    Ok(nullifier)
}

fn require_bounded_input(bytes: &[u8], maximum: usize) -> Result<(), EconomicActionErrorV1> {
    if bytes.is_empty() {
        return Err(EconomicActionErrorV1::EmptyInput);
    }
    if bytes.len() > maximum {
        return Err(EconomicActionErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum,
        });
    }
    Ok(())
}
