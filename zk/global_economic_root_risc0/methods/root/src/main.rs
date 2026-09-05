#![no_main]

use risc0_zkvm::guest::{abort, env};
use zenodex_global_economic_root_risc0_shared::{
    prepare_root_input_v1, MAX_ROOT_GUEST_INPUT_BYTES_V1,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut length = 0u32;
    env::read_slice(core::slice::from_mut(&mut length));
    let length = match usize::try_from(length) {
        Ok(value) => value,
        Err(_) => abort("economic root input length conversion rejected"),
    };
    if length == 0 || length > MAX_ROOT_GUEST_INPUT_BYTES_V1 {
        abort("economic root input length rejected");
    }
    let mut bytes = vec![0u8; length];
    env::read_slice(&mut bytes);
    let prepared = match prepare_root_input_v1(&bytes) {
        Ok(value) => value,
        Err(_) => abort("economic root input preflight rejected"),
    };
    for claim in prepared.child_claims() {
        match env::verify(claim.image_id(), claim.journal_bytes()) {
            Ok(()) => {}
            Err(never) => match never {},
        }
    }
    env::commit_slice(prepared.journal_bytes());
}
