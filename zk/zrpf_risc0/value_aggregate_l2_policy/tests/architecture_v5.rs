use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const POLICY_PACKAGE: &str = "zenodex-zrpf-risc0-value-aggregate-l2-policy";
const PINNED_IMAGE_SYMBOL: &str = "PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5";
const PINNED_IMAGE_HEX: &str = "99027bd4ff71de02c86b10309a923d37c38d273c01049f08bccfa11412bdf97d";
const PINNED_FIRST_WORD: &str = "3_564_831_385";

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("policy crate must remain below the ZRPF workspace")
        .to_path_buf()
}

fn rust_sources(root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![root.to_path_buf()];
    let mut sources = Vec::new();
    while let Some(directory) = pending.pop() {
        let mut entries = fs::read_dir(&directory)
            .unwrap_or_else(|error| panic!("read {}: {error}", directory.display()))
            .map(|entry| entry.expect("source directory entry"))
            .collect::<Vec<_>>();
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let path = entry.path();
            let file_type = entry.file_type().expect("source file type");
            assert!(
                !file_type.is_symlink(),
                "source symlink: {}",
                path.display()
            );
            if file_type.is_dir() {
                pending.push(path);
            } else if file_type.is_file() && path.extension() == Some(OsStr::new("rs")) {
                sources.push(path);
            }
        }
    }
    sources.sort();
    sources
}

fn assert_sources_exclude_identity(root: &Path) {
    for path in rust_sources(root) {
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        for forbidden in [
            PINNED_IMAGE_SYMBOL,
            PINNED_IMAGE_HEX,
            PINNED_FIRST_WORD,
            "pinned_value_aggregate_level_one_identity_v5",
            "value_aggregate_level_one_manifest_root_v5",
            "value_aggregate_level_one_profile_id_v5",
        ] {
            assert!(
                !source.contains(forbidden),
                "{} contains L1 self-identity material: {forbidden}",
                path.display()
            );
        }
    }
}

#[test]
fn l1_normal_build_and_dev_dependency_closure_excludes_l2_policy() {
    let root = workspace_root();
    let l1_manifest = root.join("methods/value_aggregate_l1/Cargo.toml");
    let manifest = fs::read_to_string(&l1_manifest).expect("read L1 manifest");
    assert!(!manifest.contains(POLICY_PACKAGE));
    assert!(!manifest.contains("value_aggregate_l2_policy"));

    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let output = Command::new(cargo)
        .current_dir(&root)
        .args([
            "tree",
            "--locked",
            "--offline",
            "-p",
            "zenodex-zrpf-risc0-value-aggregate-l1",
            "--edges",
            "normal,build,dev",
            "--prefix",
            "none",
            "--no-dedupe",
        ])
        .output()
        .expect("run cargo tree for L1 closure");
    assert!(
        output.status.success(),
        "cargo tree failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let closure = String::from_utf8(output.stdout).expect("cargo tree output must be UTF-8");
    assert!(!closure.contains(POLICY_PACKAGE));
}

#[test]
fn l1_and_shared_compiler_sources_exclude_l1_self_identity() {
    let root = workspace_root();
    assert_sources_exclude_identity(&root.join("methods/value_aggregate_l1/src"));
    assert_sources_exclude_identity(&root.join("value_aggregate_shared"));
}

#[test]
fn l2_policy_alone_owns_the_pinned_l1_identity() {
    let root = workspace_root();
    let policy_source = fs::read_to_string(root.join("value_aggregate_l2_policy/src/lib.rs"))
        .expect("read L2 policy source");
    let l2_manifest = fs::read_to_string(root.join("methods/value_aggregate_l2/Cargo.toml"))
        .expect("read L2 manifest");

    assert!(policy_source.contains(PINNED_IMAGE_SYMBOL));
    assert!(policy_source.contains(PINNED_FIRST_WORD));
    assert!(l2_manifest.contains(POLICY_PACKAGE));
}
