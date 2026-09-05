//! Measured-binary receipt endpoint with a statically selected method and codec.
//!
//! Each wrapper supplies its compiled ELF, image ID, and exact receipt decoder.
//! The V1 frame carries opaque encoded receipt bytes, with no codec negotiation.
//! This module grants no profile, state, or publication authority.

use std::io::{self, Read, Write};
use std::process::ExitCode;

use risc0_zkvm::sha::{Impl, Sha256};
use risc0_zkvm::{compute_image_id, InnerReceipt, Receipt};

mod protocol;
use protocol::{parse_request_v1, RejectV1, MAX_REQUEST_BYTES, RESPONSE_MAGIC};

type ReceiptDecoderV1 = fn(&[u8]) -> Result<Receipt, ()>;

fn bound_method_image_v1(
    expected: &[u8; 32],
    compiled_elf: &[u8],
    compiled_image: [u32; 8],
) -> Result<(), RejectV1> {
    if compiled_elf.is_empty() || compiled_image == [0; 8] {
        return Err(RejectV1::PlaceholderMethod);
    }
    let rebuilt_image = compute_image_id(compiled_elf).map_err(|_| RejectV1::PlaceholderMethod)?;
    if rebuilt_image.as_words() != compiled_image {
        return Err(RejectV1::ImageBinding);
    }
    let mut image_bytes = [0u8; 32];
    for (chunk, word) in image_bytes.chunks_exact_mut(4).zip(compiled_image) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    if &image_bytes != expected {
        return Err(RejectV1::ImageBinding);
    }
    Ok(())
}

fn verify_receipt_v1(
    receipt: &Receipt,
    expected_journal: &[u8],
    compiled_image: [u32; 8],
) -> Result<(), RejectV1> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(RejectV1::ReceiptKind);
    }
    if receipt.journal.bytes != expected_journal {
        return Err(RejectV1::JournalBinding);
    }
    // verify also requires successful execution and empty assumptions.
    receipt
        .verify(compiled_image)
        .map_err(|_| RejectV1::ReceiptVerification)
}

fn execute_v1(
    input: &[u8],
    compiled_elf: &[u8],
    compiled_image: [u32; 8],
    decode_receipt: ReceiptDecoderV1,
) -> Result<Vec<u8>, RejectV1> {
    let request = parse_request_v1(input)?;
    bound_method_image_v1(&request.image_id, compiled_elf, compiled_image)?;
    let receipt = decode_receipt(request.receipt).map_err(|()| RejectV1::ReceiptEncoding)?;
    verify_receipt_v1(&receipt, request.journal, compiled_image)?;
    let mut output = Vec::with_capacity(72);
    output.extend_from_slice(RESPONSE_MAGIC);
    output.extend_from_slice(Impl::hash_bytes(input).as_bytes());
    output.extend_from_slice(&request.image_id);
    Ok(output)
}

fn read_verify_write_v1(
    compiled_elf: &[u8],
    compiled_image: [u32; 8],
    decode_receipt: ReceiptDecoderV1,
) -> Result<(), RejectV1> {
    if std::env::args_os().len() != 1 {
        return Err(RejectV1::Arguments);
    }
    let input_limit = u64::try_from(MAX_REQUEST_BYTES + 1).map_err(|_| RejectV1::InputBounds)?;
    let mut input = Vec::new();
    io::stdin()
        .lock()
        .take(input_limit)
        .read_to_end(&mut input)
        .map_err(|_| RejectV1::InputIo)?;
    let output = execute_v1(&input, compiled_elf, compiled_image, decode_receipt)?;
    io::stdout()
        .lock()
        .write_all(&output)
        .map_err(|_| RejectV1::OutputIo)
}

/// Called only with constants and a decoder selected by the measured wrapper.
pub fn run_v1(
    compiled_elf: &[u8],
    compiled_image: [u32; 8],
    decode_receipt: ReceiptDecoderV1,
) -> ExitCode {
    match read_verify_write_v1(compiled_elf, compiled_image, decode_receipt) {
        Ok(()) => ExitCode::SUCCESS,
        Err(reason) => {
            let _ = writeln!(io::stderr().lock(), "receipt verifier rejected: {reason:?}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{FakeReceipt, ReceiptClaim};

    #[test]
    fn placeholder_or_non_elf_method_rejects() {
        for (elf, image) in [(b"".as_slice(), [1; 8]), (b"bad ELF".as_slice(), [0; 8])] {
            assert_eq!(
                bound_method_image_v1(&[0; 32], elf, image),
                Err(RejectV1::PlaceholderMethod)
            );
        }
        assert_eq!(
            bound_method_image_v1(&[1; 32], b"bad ELF", [1; 8]),
            Err(RejectV1::PlaceholderMethod)
        );
    }

    #[test]
    fn fake_receipt_never_reaches_cryptographic_success() {
        let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok([1; 8], b"journal".to_vec()))
            .try_into()
            .unwrap();
        assert_eq!(
            verify_receipt_v1(&fake, b"journal", [1; 8]),
            Err(RejectV1::ReceiptKind)
        );
    }
}
