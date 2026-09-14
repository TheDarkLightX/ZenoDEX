//! Bounded transport shared by the guest entrypoint and native host replay.

use std::io::{self, Read};
use zenodex_spot_swap_global_v2::MAX_SPOT_SWAP_FRAME_BYTES_V2;

/// One u32LE length, that exact bounded frame, and EOF. Semantic checks belong
/// to the pure core. The surrounding host owns execution deadlines.
pub fn read_spot_guest_frame_v2(input: &mut impl Read) -> io::Result<Vec<u8>> {
    let mut prefix = [0_u8; 4];
    input.read_exact(&mut prefix)?;
    let size = usize::try_from(u32::from_le_bytes(prefix))
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "frame length conversion"))?;
    if !(1..=MAX_SPOT_SWAP_FRAME_BYTES_V2).contains(&size) {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "frame length"));
    }
    let mut frame = vec![0; size];
    input.read_exact(&mut frame)?;
    if input.read(&mut [0; 1])? != 0 {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "trailing input"));
    }
    Ok(frame)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transport_covers_boundaries_truncation_and_trailing_input() {
        for size in [1, MAX_SPOT_SWAP_FRAME_BYTES_V2] {
            let mut input = u32::try_from(size).unwrap().to_le_bytes().to_vec();
            input.resize(size + 4, 7);
            assert_eq!(
                read_spot_guest_frame_v2(&mut input.as_slice())
                    .unwrap()
                    .len(),
                size
            );
            input.pop();
            assert_eq!(
                read_spot_guest_frame_v2(&mut input.as_slice())
                    .unwrap_err()
                    .kind(),
                io::ErrorKind::UnexpectedEof
            );
        }
        for size in [
            0,
            u32::try_from(MAX_SPOT_SWAP_FRAME_BYTES_V2).unwrap() + 1,
            u32::MAX,
        ] {
            assert_eq!(
                read_spot_guest_frame_v2(&mut size.to_le_bytes().as_slice())
                    .unwrap_err()
                    .kind(),
                io::ErrorKind::InvalidData
            );
        }
        let input = [1, 0, 0, 0, 7];
        for end in 0..input.len() {
            assert_eq!(
                read_spot_guest_frame_v2(&mut &input[..end])
                    .unwrap_err()
                    .kind(),
                io::ErrorKind::UnexpectedEof
            );
        }
        assert_eq!(
            read_spot_guest_frame_v2(&mut [1, 0, 0, 0, 7, 8].as_slice())
                .unwrap_err()
                .kind(),
            io::ErrorKind::InvalidData
        );
    }
}
