//! Bounded guest stdin transport. Semantic decoding remains in the pure ABI core.

use std::io::{self, Read};
use zenodex_global_settlement_abi_v2::MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2;

pub fn read_custody_guest_frame_v2(input: &mut impl Read) -> io::Result<Vec<u8>> {
    let mut length_bytes = [0_u8; 4];
    input.read_exact(&mut length_bytes)?;
    let length = usize::try_from(u32::from_le_bytes(length_bytes))
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "input length conversion"))?;
    if length == 0 || length > MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2 {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "input length"));
    }
    let mut frame = vec![0_u8; length];
    input.read_exact(&mut frame)?;
    if input.read(&mut [0_u8; 1])? != 0 {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "trailing input"));
    }
    Ok(frame)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn framed(payload: &[u8]) -> Vec<u8> {
        let mut input = u32::try_from(payload.len()).unwrap().to_le_bytes().to_vec();
        input.extend_from_slice(payload);
        input
    }

    #[test]
    fn exact_little_endian_frame_is_returned_without_interpretation() {
        let payload = [0x17; 258];
        let input = framed(&payload);
        assert_eq!(&input[..4], &[2, 1, 0, 0]);
        assert_eq!(
            read_custody_guest_frame_v2(&mut input.as_slice()).unwrap(),
            payload
        );
    }

    #[test]
    fn every_outer_prefix_and_body_truncation_rejects() {
        let input = framed(&[1, 2, 3, 4, 5]);
        for end in 0..input.len() {
            let error = read_custody_guest_frame_v2(&mut &input[..end]).unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::UnexpectedEof, "{end}");
        }
    }

    #[test]
    fn unsupported_length_rejects_before_reading_a_body() {
        for length in [
            0,
            MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2 as u32 + 1,
            u32::MAX,
        ] {
            let prefix = length.to_le_bytes();
            let error = read_custody_guest_frame_v2(&mut prefix.as_slice()).unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::InvalidData);
            assert_eq!(error.to_string(), "input length");
        }
    }

    #[test]
    fn exact_outer_size_ceiling_is_admitted() {
        let payload = vec![0x31; MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2];
        let input = framed(&payload);
        assert_eq!(
            read_custody_guest_frame_v2(&mut input.as_slice()).unwrap(),
            payload
        );
    }

    #[test]
    fn trailing_stdin_cannot_hide_beyond_a_valid_frame() {
        let mut input = framed(&[1, 2, 3]);
        input.push(0);
        let error = read_custody_guest_frame_v2(&mut input.as_slice()).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert_eq!(error.to_string(), "trailing input");
    }
}
