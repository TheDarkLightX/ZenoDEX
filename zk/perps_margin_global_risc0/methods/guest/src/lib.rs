//! Bounded stdin transport; semantic decoding remains in the pure margin core.

use std::io::{self, Read};
use zenodex_perps_margin_global_v2::MAX_PERPS_MARGIN_FRAME_BYTES_V2;

/// Requires one u32LE length, that exact frame, and EOF. Both the host and guest
/// use this transport; Python/Rust tests separately check the contained ZDPM2.
pub fn read_margin_guest_frame_v2(input: &mut impl Read) -> io::Result<Vec<u8>> {
    let mut prefix = [0_u8; 4];
    input.read_exact(&mut prefix)?;
    let size = usize::try_from(u32::from_le_bytes(prefix))
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "frame length conversion"))?;
    if !(1..=MAX_PERPS_MARGIN_FRAME_BYTES_V2).contains(&size) {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "frame length"));
    }
    let mut frame = vec![0_u8; size];
    input.read_exact(&mut frame)?;
    if input.read(&mut [0_u8; 1])? != 0 {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "trailing input"));
    }
    Ok(frame)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_length_and_all_truncations_have_distinct_outcomes() {
        let mut input = 258_u32.to_le_bytes().to_vec();
        input.extend_from_slice(&[7; 258]);
        assert_eq!(&input[..4], &[2, 1, 0, 0]);
        assert_eq!(
            read_margin_guest_frame_v2(&mut input.as_slice()).unwrap(),
            [7; 258]
        );
        for end in 0..input.len() {
            assert_eq!(
                read_margin_guest_frame_v2(&mut &input[..end])
                    .unwrap_err()
                    .kind(),
                io::ErrorKind::UnexpectedEof
            );
        }
        input.push(0);
        assert_eq!(
            read_margin_guest_frame_v2(&mut input.as_slice())
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidData
        );
    }

    #[test]
    fn maximum_input_is_representable_and_out_of_bounds_rejects_before_body_read() {
        let maximum = u32::try_from(MAX_PERPS_MARGIN_FRAME_BYTES_V2).unwrap();
        for size in [0, maximum + 1, u32::MAX] {
            assert_eq!(
                read_margin_guest_frame_v2(&mut size.to_le_bytes().as_slice())
                    .unwrap_err()
                    .kind(),
                io::ErrorKind::InvalidData
            );
        }
        for size in [1, maximum] {
            let mut input = size.to_le_bytes().to_vec();
            input.resize(4 + usize::try_from(size).unwrap(), 1);
            assert_eq!(
                read_margin_guest_frame_v2(&mut input.as_slice()).unwrap(),
                input[4..]
            );
        }
    }
}
