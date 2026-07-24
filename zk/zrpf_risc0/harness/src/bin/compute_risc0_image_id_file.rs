use std::{env, fs, io::Read, path::Path};

use risc0_zkvm::compute_image_id;
use sha2::{Digest, Sha256};

const MAX_GUEST_ELF_BYTES: u64 = 16 * 1_024 * 1_024;

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let [path] = arguments.as_slice() else {
        return Err("usage: compute_risc0_image_id_file <guest.elf>".to_owned());
    };
    let bytes = read_bounded_regular_file(Path::new(path))?;
    let image_id =
        compute_image_id(&bytes).map_err(|error| format!("compute image ID: {error}"))?;
    println!(
        "{}",
        serde_json::json!({
            "elf_bytes": bytes.len(),
            "elf_sha256": hex::encode(Sha256::digest(&bytes)),
            "image_id": image_id.to_string(),
            "ok": true,
            "schema": "zenodex/risc0_image_id_file/v1",
        })
    );
    Ok(())
}

fn read_bounded_regular_file(path: &Path) -> Result<Vec<u8>, String> {
    let before = fs::symlink_metadata(path).map_err(|error| format!("ELF metadata: {error}"))?;
    if !before.is_file() || before.file_type().is_symlink() || before.len() > MAX_GUEST_ELF_BYTES {
        return Err("ELF must be a bounded non-symlink regular file".to_owned());
    }
    let mut file = fs::File::open(path).map_err(|error| format!("open ELF: {error}"))?;
    let opened = file
        .metadata()
        .map_err(|error| format!("opened ELF metadata: {error}"))?;
    if opened.len() != before.len() || !opened.is_file() {
        return Err("ELF changed while opening".to_owned());
    }
    let mut bytes = Vec::new();
    (&mut file)
        .take(MAX_GUEST_ELF_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read ELF: {error}"))?;
    let after = file
        .metadata()
        .map_err(|error| format!("final ELF metadata: {error}"))?;
    let byte_length =
        u64::try_from(bytes.len()).map_err(|_| "ELF length exceeds u64".to_owned())?;
    if bytes.is_empty() || byte_length > MAX_GUEST_ELF_BYTES || after.len() != opened.len() {
        return Err("ELF length is unsupported or changed during read".to_owned());
    }
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::MAX_GUEST_ELF_BYTES;

    #[test]
    fn evidence_bound_is_explicit() {
        assert_eq!(MAX_GUEST_ELF_BYTES, 16 * 1_024 * 1_024);
    }
}
