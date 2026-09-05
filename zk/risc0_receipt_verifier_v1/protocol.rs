//! Bounded frame decoding for the verification-only subprocess endpoint.
//! This module deliberately contains no cryptographic acceptance operation.

pub const REQUEST_MAGIC: &[u8; 8] = b"ZDXRV1RQ";
pub const RESPONSE_MAGIC: &[u8; 8] = b"ZDXRV1OK";
pub const HEADER_BYTES: usize = 48;
pub const MAX_RECEIPT_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_JOURNAL_BYTES: usize = 1024 * 1024;
pub const MAX_REQUEST_BYTES: usize = HEADER_BYTES + MAX_RECEIPT_BYTES + MAX_JOURNAL_BYTES;

#[derive(Debug, Eq, PartialEq)]
pub enum RejectV1 {
    Arguments,
    InputIo,
    InputBounds,
    Frame,
    PlaceholderMethod,
    ImageBinding,
    ReceiptEncoding,
    ReceiptKind,
    JournalBinding,
    ReceiptVerification,
    OutputIo,
}

pub struct RequestV1<'a> {
    pub image_id: [u8; 32],
    pub journal: &'a [u8],
    pub receipt: &'a [u8],
}

pub fn parse_request_v1(input: &[u8]) -> Result<RequestV1<'_>, RejectV1> {
    if input.len() < HEADER_BYTES || input.len() > MAX_REQUEST_BYTES {
        return Err(RejectV1::InputBounds);
    }
    if input.get(..8) != Some(REQUEST_MAGIC) {
        return Err(RejectV1::Frame);
    }
    let image_id = input[8..40].try_into().map_err(|_| RejectV1::Frame)?;
    let journal_len = u32::from_le_bytes(input[40..44].try_into().map_err(|_| RejectV1::Frame)?);
    let receipt_len = u32::from_le_bytes(input[44..48].try_into().map_err(|_| RejectV1::Frame)?);
    let journal_len = usize::try_from(journal_len).map_err(|_| RejectV1::InputBounds)?;
    let receipt_len = usize::try_from(receipt_len).map_err(|_| RejectV1::InputBounds)?;
    if !(1..=MAX_JOURNAL_BYTES).contains(&journal_len)
        || !(1..=MAX_RECEIPT_BYTES).contains(&receipt_len)
    {
        return Err(RejectV1::InputBounds);
    }
    // The checked maxima keep both additions below MAX_REQUEST_BYTES.
    let receipt_start = HEADER_BYTES + journal_len;
    if input.len() != receipt_start + receipt_len {
        return Err(RejectV1::Frame);
    }
    Ok(RequestV1 {
        image_id,
        journal: &input[HEADER_BYTES..receipt_start],
        receipt: &input[receipt_start..],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame() -> Vec<u8> {
        let mut input = b"ZDXRV1RQ".to_vec();
        input.extend_from_slice(&[1; 32]);
        input.extend_from_slice(&7u32.to_le_bytes());
        input.extend_from_slice(&7u32.to_le_bytes());
        input.extend_from_slice(b"journalreceipt");
        input
    }

    #[test]
    fn fixed_vector_matches_python_frame() {
        let input = frame();
        let request = parse_request_v1(&input).unwrap();
        assert_eq!(request.image_id, [1; 32]);
        assert_eq!(request.journal, b"journal");
        assert_eq!(request.receipt, b"receipt");
    }

    #[test]
    fn every_truncation_and_trailing_data_reject() {
        let input = frame();
        for length in 0..input.len() {
            assert!(parse_request_v1(&input[..length]).is_err());
        }
        let mut extended = input;
        extended.push(0);
        assert!(matches!(parse_request_v1(&extended), Err(RejectV1::Frame)));
    }

    #[test]
    fn bad_magic_and_empty_or_overflow_lengths_reject() {
        let mut input = frame();
        input[0] ^= 1;
        assert!(matches!(parse_request_v1(&input), Err(RejectV1::Frame)));
        for offset in [40, 44] {
            for length in [0, u32::MAX] {
                let mut input = frame();
                input[offset..offset + 4].copy_from_slice(&length.to_le_bytes());
                assert!(matches!(
                    parse_request_v1(&input),
                    Err(RejectV1::InputBounds)
                ));
            }
        }
    }

    #[test]
    fn exact_maximum_fields_fit_and_each_next_length_rejects() {
        let mut input = frame();
        input[40..44].copy_from_slice(&(MAX_JOURNAL_BYTES as u32).to_le_bytes());
        input[44..48].copy_from_slice(&(MAX_RECEIPT_BYTES as u32).to_le_bytes());
        input.resize(MAX_REQUEST_BYTES, 1);
        let parsed = parse_request_v1(&input).unwrap();
        assert_eq!(parsed.journal.len(), MAX_JOURNAL_BYTES);
        assert_eq!(parsed.receipt.len(), MAX_RECEIPT_BYTES);
        for (offset, maximum) in [(40, MAX_JOURNAL_BYTES), (44, MAX_RECEIPT_BYTES)] {
            input[offset..offset + 4].copy_from_slice(&((maximum + 1) as u32).to_le_bytes());
            assert!(matches!(
                parse_request_v1(&input),
                Err(RejectV1::InputBounds)
            ));
            input[offset..offset + 4].copy_from_slice(&(maximum as u32).to_le_bytes());
        }
        input.push(1);
        assert!(matches!(
            parse_request_v1(&input),
            Err(RejectV1::InputBounds)
        ));
    }
}
