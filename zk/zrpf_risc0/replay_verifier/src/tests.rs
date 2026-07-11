use std::collections::BTreeSet;
use std::error::Error;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use risc0_zkvm::Digest;

use super::{
    parse_bundle_directory, read_bounded_regular_file, require_exact_seal_word_mutation,
    require_retained_artifact_binding, BundlePaths, ReplayError,
};
#[cfg(unix)]
use crate::bundle::open_bundle_directory;
use crate::profile::{
    ADAPTER_ID, LEVEL_ONE_ID, LEVEL_TWO_ID, MAX_RECEIPT_READ_BYTES_U64, RETAINED_ARTIFACTS,
};

#[test]
fn retained_image_ids_are_exact() {
    assert_eq!(
        Digest::from(ADAPTER_ID).to_string(),
        "71f282b5517fc6108988c1cc9b4601807a40ae331c0e0f0f5505d12b241e5574"
    );
    assert_eq!(
        Digest::from(LEVEL_ONE_ID).to_string(),
        "4272be5165f65e29cb134f815d6c6fc40d7f492979f596082cac10c3f0d43c2b"
    );
    assert_eq!(
        Digest::from(LEVEL_TWO_ID).to_string(),
        "3b858d113cb155b2946e1c733fdf5fe5592b6bf46c903d0a3cfb322099845736"
    );
}

#[test]
fn receipt_inventory_is_fixed_relative_and_unique() {
    let unique: BTreeSet<&str> = RETAINED_ARTIFACTS
        .iter()
        .map(|artifact| artifact.name)
        .collect();
    assert_eq!(unique.len(), RETAINED_ARTIFACTS.len());
    for artifact in RETAINED_ARTIFACTS {
        let path = PathBuf::from(artifact.name);
        assert!(!path.is_absolute());
        assert_eq!(path.components().count(), 1);
        assert!(!artifact.name.is_empty());
        assert!(artifact.size_bytes > 0);
        assert!(artifact.size_bytes <= super::MAX_CANONICAL_RECEIPT_BYTES_V3);
        assert_eq!(artifact.sha256.len(), 64);
        assert!(artifact.sha256.bytes().all(|byte| byte.is_ascii_hexdigit()));
    }
}

#[test]
fn retained_artifact_binding_rejects_wrong_or_unknown_bytes() {
    assert_eq!(
        require_retained_artifact_binding(RETAINED_ARTIFACTS[0].name, b"wrong"),
        Err(ReplayError::ReceiptArtifactBinding(
            RETAINED_ARTIFACTS[0].name
        ))
    );
    assert_eq!(
        require_retained_artifact_binding("unknown.receipt.json", b"wrong"),
        Err(ReplayError::ReceiptArtifactBinding("unknown.receipt.json"))
    );
}

#[test]
fn exact_seal_mutation_accepts_only_word_one_low_bit() -> Result<(), ReplayError> {
    let source = [10, 20, 30];
    let accepted = require_exact_seal_word_mutation(&source, &[10, 21, 30])?;
    assert_eq!(accepted.word_index, 1);
    assert_eq!(accepted.original_word, 20);
    assert_eq!(accepted.mutated_word, 21);
    for candidate in [
        vec![10, 20, 30],
        vec![11, 20, 30],
        vec![10, 22, 30],
        vec![10, 21, 31],
        vec![10, 21],
        Vec::new(),
    ] {
        assert_eq!(
            require_exact_seal_word_mutation(&source, &candidate),
            Err(ReplayError::MutationShape)
        );
    }
    Ok(())
}

#[test]
fn bundle_cli_rejects_wrong_arity_and_inventory() -> Result<(), Box<dyn Error>> {
    assert!(matches!(
        parse_bundle_directory(Vec::<String>::new()),
        Err(ReplayError::Usage)
    ));
    let directory = isolated_test_directory("inventory");
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir(&directory)?;
    assert!(matches!(
        parse_bundle_directory([directory.to_string_lossy().into_owned()]),
        Err(ReplayError::BundleInventory)
    ));
    fs::remove_dir_all(&directory)?;
    Ok(())
}

#[cfg(unix)]
#[test]
fn bundle_cli_rejects_symlink_directory() -> Result<(), Box<dyn Error>> {
    use std::os::unix::fs::symlink;

    let directory = isolated_test_directory("directory-symlink-target");
    let link = isolated_test_directory("directory-symlink");
    let _ = fs::remove_dir_all(&directory);
    let _ = fs::remove_file(&link);
    fs::create_dir(&directory)?;
    symlink(&directory, &link)?;
    assert!(matches!(
        parse_bundle_directory([link.to_string_lossy().into_owned()]),
        Err(ReplayError::BundleDirectory)
    ));
    fs::remove_file(&link)?;
    fs::remove_dir_all(&directory)?;
    Ok(())
}

#[cfg(unix)]
#[test]
fn receipt_file_rejects_empty_and_oversized() -> Result<(), Box<dyn Error>> {
    let directory = isolated_test_directory("bounds");
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir(&directory)?;
    let path = directory.join("receipt.json");
    fs::write(&path, b"")?;
    let paths = open_test_bundle(&directory)?;
    assert_eq!(
        read_bounded_regular_file(&paths, "receipt.json"),
        Err(ReplayError::ReceiptArtifact("receipt.json"))
    );
    fs::File::create(&path)?.set_len(MAX_RECEIPT_READ_BYTES_U64)?;
    assert_eq!(
        read_bounded_regular_file(&paths, "receipt.json"),
        Err(ReplayError::ReceiptArtifact("receipt.json"))
    );
    fs::remove_dir_all(&directory)?;
    Ok(())
}

#[cfg(unix)]
#[test]
fn receipt_file_rejects_symlink() -> Result<(), Box<dyn Error>> {
    use std::os::unix::fs::symlink;

    let directory = isolated_test_directory("symlink");
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir(&directory)?;
    let target = directory.join("target.json");
    let link = directory.join("receipt.json");
    fs::write(&target, b"{}")?;
    symlink(&target, &link)?;
    let paths = open_test_bundle(&directory)?;
    assert_eq!(
        read_bounded_regular_file(&paths, "receipt.json"),
        Err(ReplayError::ReceiptArtifact("receipt.json"))
    );
    fs::remove_dir_all(&directory)?;
    Ok(())
}

#[cfg(unix)]
#[test]
fn receipt_file_rejects_fifo_without_blocking() -> Result<(), Box<dyn Error>> {
    let directory = isolated_test_directory("fifo");
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir(&directory)?;
    let paths = open_test_bundle(&directory)?;
    rustix::fs::mkfifoat(
        &paths.directory,
        "receipt.json",
        rustix::fs::Mode::from_raw_mode(0o600),
    )?;
    assert_eq!(
        read_bounded_regular_file(&paths, "receipt.json"),
        Err(ReplayError::ReceiptArtifact("receipt.json"))
    );
    fs::remove_dir_all(&directory)?;
    Ok(())
}

#[cfg(unix)]
fn open_test_bundle(path: &Path) -> Result<BundlePaths, Box<dyn Error>> {
    let directory = open_bundle_directory(path)
        .map_err(|error| io::Error::other(format!("test directory failed to open: {error:?}")))?;
    Ok(BundlePaths { directory })
}

fn isolated_test_directory(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "zenodex-zrpf-replay-verifier-{label}-{}",
        std::process::id()
    ))
}
