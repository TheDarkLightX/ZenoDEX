use std::io::{Read, Write};
use std::process::ExitCode;

use blst::min_pk::{PublicKey, Signature};
use blst::BLST_ERROR;
use sha2::{Digest, Sha256};

const REQUEST_MAGIC_V1: &[u8; 8] = b"ZDXBLSV1";
const ACCEPT_MAGIC_V1: &[u8; 8] = b"ZDXBOKV1";
const REJECT_MAGIC_V1: &[u8; 8] = b"ZDXBNOV1";
const PUBLIC_KEY_BYTES_V1: usize = 48;
const SIGNATURE_BYTES_V1: usize = 96;
const MESSAGE_LENGTH_BYTES_V1: usize = 4;
const MAX_MESSAGE_BYTES_V1: usize = 1_048_576;
const REQUEST_HEADER_BYTES_V1: usize =
    REQUEST_MAGIC_V1.len() + PUBLIC_KEY_BYTES_V1 + SIGNATURE_BYTES_V1 + MESSAGE_LENGTH_BYTES_V1;
const MAX_REQUEST_BYTES_V1: usize = REQUEST_HEADER_BYTES_V1 + MAX_MESSAGE_BYTES_V1;
const RESPONSE_BYTES_V1: usize = 8 + 32;
const G2_BASIC_DST_V1: &[u8] = b"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_";

struct RequestV1<'a> {
    public_key: &'a [u8],
    signature: &'a [u8],
    message: &'a [u8],
}

fn read_request_v1() -> Result<Vec<u8>, ()> {
    let mut request = Vec::with_capacity(MAX_REQUEST_BYTES_V1);
    let read_ceiling = u64::try_from(MAX_REQUEST_BYTES_V1)
        .map_err(|_| ())?
        .checked_add(1)
        .ok_or(())?;
    let mut bounded_stdin = std::io::stdin().lock().take(read_ceiling);
    bounded_stdin.read_to_end(&mut request).map_err(|_| ())?;
    if request.len() > MAX_REQUEST_BYTES_V1 {
        return Err(());
    }
    Ok(request)
}

fn parse_request_v1(request: &[u8]) -> Result<RequestV1<'_>, ()> {
    if request.len() < REQUEST_HEADER_BYTES_V1
        || request.get(..REQUEST_MAGIC_V1.len()) != Some(REQUEST_MAGIC_V1.as_slice())
    {
        return Err(());
    }

    let public_key_start = REQUEST_MAGIC_V1.len();
    let signature_start = public_key_start + PUBLIC_KEY_BYTES_V1;
    let message_length_start = signature_start + SIGNATURE_BYTES_V1;
    let message_start = message_length_start + MESSAGE_LENGTH_BYTES_V1;
    let message_len = usize::try_from(u32::from_le_bytes([
        request[message_length_start],
        request[message_length_start + 1],
        request[message_length_start + 2],
        request[message_length_start + 3],
    ]))
    .map_err(|_| ())?;
    if !(1..=MAX_MESSAGE_BYTES_V1).contains(&message_len)
        || message_start.checked_add(message_len) != Some(request.len())
    {
        return Err(());
    }

    Ok(RequestV1 {
        public_key: &request[public_key_start..signature_start],
        signature: &request[signature_start..message_length_start],
        message: &request[message_start..],
    })
}

fn verify_request_v1(request: RequestV1<'_>) -> bool {
    let public_key = match PublicKey::key_validate(request.public_key) {
        Ok(public_key) => public_key,
        Err(_) => return false,
    };
    if public_key.to_bytes().as_slice() != request.public_key {
        return false;
    }
    let signature = match Signature::sig_validate(request.signature, true) {
        Ok(signature) => signature,
        Err(_) => return false,
    };
    if signature.to_bytes().as_slice() != request.signature {
        return false;
    }
    signature.verify(
        true,
        request.message,
        G2_BASIC_DST_V1,
        &[],
        &public_key,
        true,
    ) == BLST_ERROR::BLST_SUCCESS
}

fn response_v1(accepted: bool, request_bytes: &[u8]) -> [u8; RESPONSE_BYTES_V1] {
    let mut response = [0u8; RESPONSE_BYTES_V1];
    let magic = if accepted {
        ACCEPT_MAGIC_V1
    } else {
        REJECT_MAGIC_V1
    };
    response[..magic.len()].copy_from_slice(magic);
    response[magic.len()..].copy_from_slice(&Sha256::digest(request_bytes));
    response
}

fn run_v1() -> Result<(), ()> {
    if std::env::args_os().len() != 1 {
        return Err(());
    }
    let request_bytes = read_request_v1()?;
    let request = parse_request_v1(&request_bytes)?;
    let response = response_v1(verify_request_v1(request), &request_bytes);
    let mut stdout = std::io::stdout().lock();
    stdout.write_all(&response).map_err(|_| ())?;
    stdout.flush().map_err(|_| ())
}

fn main() -> ExitCode {
    match run_v1() {
        Ok(()) => ExitCode::SUCCESS,
        Err(()) => ExitCode::from(2),
    }
}
