#![no_main]
#![no_std]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};

const MAX_TEST_JOURNAL_BYTES: u32 = 1_048_576;

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut journal_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut journal_len));
    if journal_len == 0 || journal_len > MAX_TEST_JOURNAL_BYTES {
        abort("structural test leaf journal length unsupported");
    }
    let journal_len = match usize::try_from(journal_len) {
        Ok(value) => value,
        Err(_) => abort("structural test leaf length conversion failed"),
    };
    let mut journal_bytes = vec![0u8; journal_len];
    env::read_slice(&mut journal_bytes);
    env::commit_slice(&journal_bytes);
}
