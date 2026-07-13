use std::{
    env, fs,
    io::Write,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const PREBUILT_ENV: &str = "ZRPF_SPOT_V6_PREBUILT_METHODS_MANIFEST";
const PREBUILT_SCHEMA: &str = "zenodex/zrpf_spot_v6_prebuilt_methods/v1";
const MAX_MANIFEST_BYTES: usize = 64 * 1024;
const MAX_PROGRAM_BYTES: u64 = 16 * 1024 * 1024;
const R0BF_MAGIC: &[u8] = b"R0BF";

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct PrebuiltManifest {
    profile: String,
    programs: Vec<PrebuiltProgram>,
    schema: String,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct PrebuiltProgram {
    file: String,
    image_id: String,
    role: String,
    sha256: String,
    size_bytes: u64,
}

fn main() {
    println!("cargo:rerun-if-env-changed=RISC0_SKIP_BUILD");
    println!("cargo:rerun-if-env-changed={PREBUILT_ENV}");
    println!("cargo:rerun-if-env-changed=CLIPPY_ARGS");
    println!("cargo:rerun-if-env-changed=CARGO_CFG_CLIPPY");
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR must be set"));
    let methods_rs = out_dir.join("methods.rs");
    if env::var_os("RISC0_SKIP_BUILD").is_some() || is_clippy_build() {
        if env::var_os(PREBUILT_ENV).is_some() {
            panic!("{PREBUILT_ENV} cannot be combined with a skipped or Clippy guest build");
        }
        fs::write(
            methods_rs,
            r#"
pub const ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF: &[u8] = &[];
pub const ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID: [u32; 8] = [0; 8];
pub const ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ELF: &[u8] = &[];
pub const ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ID: [u32; 8] = [0; 8];
pub const ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ELF: &[u8] = &[];
pub const ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ID: [u32; 8] = [0; 8];
pub const ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ELF: &[u8] = &[];
pub const ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ID: [u32; 8] = [0; 8];
"#,
        )
        .expect("write Spot V6 placeholder methods.rs");
        return;
    }
    if let Some(manifest_path) = env::var_os(PREBUILT_ENV) {
        embed_prebuilt_methods(&out_dir, &methods_rs, Path::new(&manifest_path));
        return;
    }
    risc0_build::embed_methods();
}

fn embed_prebuilt_methods(out_dir: &Path, methods_rs: &Path, manifest_path: &Path) {
    let unresolved_metadata = fs::symlink_metadata(manifest_path)
        .expect("read unresolved Spot V6 prebuilt manifest metadata");
    assert!(
        unresolved_metadata.file_type().is_file(),
        "prebuilt manifest must be a regular file rather than a link or special file"
    );
    let manifest_path = manifest_path
        .canonicalize()
        .expect("canonicalize Spot V6 prebuilt manifest");
    let metadata =
        fs::symlink_metadata(&manifest_path).expect("read Spot V6 prebuilt manifest metadata");
    assert!(
        metadata.file_type().is_file(),
        "prebuilt manifest must be a regular file"
    );
    assert!(
        0 < metadata.len() && metadata.len() <= MAX_MANIFEST_BYTES as u64,
        "prebuilt manifest has an unsupported size"
    );
    let raw = fs::read(&manifest_path).expect("read Spot V6 prebuilt manifest");
    let manifest: PrebuiltManifest =
        serde_json::from_slice(&raw).expect("decode Spot V6 prebuilt manifest");
    let canonical_value =
        serde_json::to_value(&manifest).expect("convert prebuilt manifest to canonical value");
    let mut canonical =
        serde_json::to_vec(&canonical_value).expect("encode canonical prebuilt manifest");
    canonical.push(b'\n');
    assert_eq!(raw, canonical, "prebuilt manifest must be canonical JSON");
    assert_eq!(
        manifest.schema, PREBUILT_SCHEMA,
        "prebuilt manifest schema mismatch"
    );
    let expected_roles: &[&str] = match manifest.profile.as_str() {
        "settlement_only_v1" => &["level_two", "settlement"],
        "full_chain_v1" => &["leaf", "level_one", "level_two", "settlement"],
        _ => panic!("unsupported prebuilt-method profile"),
    };
    assert_eq!(
        manifest.programs.len(),
        expected_roles.len(),
        "prebuilt program count mismatch"
    );
    let parent = manifest_path
        .parent()
        .expect("prebuilt manifest must have a parent");
    let mut generated = placeholder_constants_for_unbound_roles(expected_roles);
    for (program, expected_role) in manifest.programs.iter().zip(expected_roles) {
        assert_eq!(
            program.role, *expected_role,
            "prebuilt program order mismatch"
        );
        let expected_file = program_filename(expected_role);
        assert_eq!(
            program.file, expected_file,
            "prebuilt program filename mismatch"
        );
        require_lower_hex(&program.sha256, "prebuilt program SHA-256");
        require_lower_hex(&program.image_id, "prebuilt program image ID");
        assert_ne!(
            program.image_id,
            "0".repeat(64),
            "prebuilt image ID cannot be zero"
        );
        assert!(
            0 < program.size_bytes && program.size_bytes <= MAX_PROGRAM_BYTES,
            "prebuilt program size is unsupported"
        );
        let source = parent.join(&program.file);
        let source_metadata =
            fs::symlink_metadata(&source).expect("read prebuilt program metadata");
        assert!(
            source_metadata.file_type().is_file(),
            "prebuilt program must be a regular file"
        );
        assert_eq!(
            source_metadata.len(),
            program.size_bytes,
            "prebuilt program size mismatch"
        );
        let bytes = fs::read(&source).expect("read prebuilt program");
        assert!(
            bytes.starts_with(R0BF_MAGIC),
            "prebuilt program lacks R0BF magic"
        );
        assert_eq!(
            hex_sha256(&bytes),
            program.sha256,
            "prebuilt program SHA-256 mismatch"
        );
        let destination = out_dir.join(expected_file);
        persist_prebuilt_program(&destination, &bytes);
        generated.push_str(&generated_constant(
            expected_role,
            expected_file,
            &program.image_id,
        ));
        println!("cargo:rerun-if-changed={}", source.display());
    }
    fs::write(methods_rs, generated).expect("write prebuilt Spot V6 methods.rs");
    println!("cargo:rerun-if-changed={}", manifest_path.display());
}

fn persist_prebuilt_program(destination: &Path, bytes: &[u8]) {
    match fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(destination)
    {
        Ok(mut output) => {
            output
                .write_all(bytes)
                .expect("write copied prebuilt program");
            output.sync_all().expect("sync copied prebuilt program");
        }
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            let metadata = fs::symlink_metadata(destination)
                .expect("read existing copied prebuilt program metadata");
            assert!(
                metadata.file_type().is_file(),
                "existing copied prebuilt program must be a regular file"
            );
            let existing =
                fs::read(destination).expect("read existing copied prebuilt program bytes");
            assert_eq!(
                existing, bytes,
                "existing copied prebuilt program differs from the governed bytes"
            );
        }
        Err(error) => panic!("create copied prebuilt program: {error}"),
    }
}

fn placeholder_constants_for_unbound_roles(bound_roles: &[&str]) -> String {
    let mut generated = String::new();
    for role in ["leaf", "level_one", "level_two", "settlement"] {
        if !bound_roles.contains(&role) {
            let (elf_name, id_name) = constant_names(role);
            generated.push_str(&format!(
                "\npub const {elf_name}: &[u8] = &[];\npub const {id_name}: [u32; 8] = [0; 8];\n"
            ));
        }
    }
    generated
}

fn generated_constant(role: &str, file: &str, image_id: &str) -> String {
    let (elf_name, id_name) = constant_names(role);
    let words = image_id
        .as_bytes()
        .chunks_exact(8)
        .map(|chunk| {
            let text = std::str::from_utf8(chunk).expect("image word must be UTF-8");
            let bytes = u32::from_str_radix(text, 16).expect("image word must be hex");
            bytes.swap_bytes()
        })
        .map(|word| format!("0x{word:08x}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "\npub const {elf_name}: &[u8] = include_bytes!(concat!(env!(\"OUT_DIR\"), \"/{file}\"));\npub const {id_name}: [u32; 8] = [{words}];\n"
    )
}

fn constant_names(role: &str) -> (&'static str, &'static str) {
    match role {
        "leaf" => (
            "ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF",
            "ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID",
        ),
        "level_one" => (
            "ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ELF",
            "ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L1_V6_ID",
        ),
        "level_two" => (
            "ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ELF",
            "ZENODEX_ZRPF_RISC0_SPOT_VALUE_AGGREGATE_L2_V6_ID",
        ),
        "settlement" => (
            "ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ELF",
            "ZENODEX_ZRPF_RISC0_SOURCE_OPENED_SPOT_SETTLEMENT_V6_ID",
        ),
        _ => panic!("unsupported prebuilt role"),
    }
}

fn program_filename(role: &str) -> &'static str {
    match role {
        "leaf" => "spot_value_leaf_v6.bin",
        "level_one" => "spot_value_aggregate_l1_v6.bin",
        "level_two" => "spot_value_aggregate_l2_v6.bin",
        "settlement" => "source_opened_spot_settlement_v6.bin",
        _ => panic!("unsupported prebuilt role"),
    }
}

fn require_lower_hex(value: &str, label: &str) {
    assert!(
        value.len() == 64
            && value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "{label} must be 64 lowercase hex characters"
    );
}

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn is_clippy_build() -> bool {
    env::var_os("CARGO_CFG_CLIPPY").is_some()
        || env::var_os("CLIPPY_ARGS").is_some()
        || env::var("RUSTC_WORKSPACE_WRAPPER")
            .ok()
            .is_some_and(|value| value.contains("clippy"))
}
