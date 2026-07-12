use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const ROOT_POLICY_PACKAGE: &str = "zenodex-zrpf-risc0-value-aggregate-root-policy";
const PINNED_IMAGE_SYMBOL: &str = "PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5";
const PINNED_IMAGE_HEX: &str = "49c94dc5618c5e82372265cc75ee77d0985d9ab1b7b223f036e513870d6742f8";
const PINNED_FIRST_WORD: &str = "3_310_209_353";

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("root policy must remain below the ZRPF workspace")
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

fn assert_sources_exclude_root_identity(root: &Path) {
    for path in rust_sources(root) {
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        for forbidden in [
            PINNED_IMAGE_SYMBOL,
            PINNED_IMAGE_HEX,
            PINNED_FIRST_WORD,
            "pinned_value_aggregate_level_two_root_identity_v5",
            "value_aggregate_level_two_root_manifest_root_v5",
            "value_aggregate_level_two_root_profile_id_v5",
        ] {
            assert!(
                !source.contains(forbidden),
                "{} contains L2 self-identity material: {forbidden}",
                path.display()
            );
        }
    }
}

#[test]
fn l2_normal_build_and_dev_dependency_closure_excludes_root_policy() {
    let root = workspace_root();
    let l2_manifest = root.join("methods/value_aggregate_l2/Cargo.toml");
    let manifest = fs::read_to_string(&l2_manifest).expect("read L2 manifest");
    assert!(!manifest.contains(ROOT_POLICY_PACKAGE));
    assert!(!manifest.contains("value_aggregate_root_policy"));

    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let output = Command::new(cargo)
        .current_dir(&root)
        .args([
            "tree",
            "--locked",
            "--offline",
            "-p",
            "zenodex-zrpf-risc0-value-aggregate-l2",
            "--edges",
            "normal,build,dev",
            "--prefix",
            "none",
            "--no-dedupe",
        ])
        .output()
        .expect("run cargo tree for L2 closure");
    assert!(
        output.status.success(),
        "cargo tree failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let closure = String::from_utf8(output.stdout).expect("cargo tree output must be UTF-8");
    assert!(!closure.contains(ROOT_POLICY_PACKAGE));
}

#[test]
fn l2_and_compiler_sources_exclude_l2_self_identity() {
    let root = workspace_root();
    assert_sources_exclude_root_identity(&root.join("methods/value_aggregate_l2/src"));
    assert_sources_exclude_root_identity(&root.join("value_aggregate_l2_policy"));
    assert_sources_exclude_root_identity(&root.join("value_aggregate_shared"));
}

#[test]
fn root_policy_alone_owns_the_pinned_l2_identity() {
    let root = workspace_root();
    let policy_source = fs::read_to_string(root.join("value_aggregate_root_policy/src/lib.rs"))
        .expect("read root policy source");
    let workspace_manifest =
        fs::read_to_string(root.join("Cargo.toml")).expect("read workspace manifest");
    let harness_manifest =
        fs::read_to_string(root.join("harness/Cargo.toml")).expect("read harness manifest");

    assert!(policy_source.contains(PINNED_IMAGE_SYMBOL));
    assert!(policy_source.contains(PINNED_FIRST_WORD));
    assert!(workspace_manifest.contains("\"value_aggregate_root_policy\""));
    assert!(harness_manifest.contains(ROOT_POLICY_PACKAGE));
}
