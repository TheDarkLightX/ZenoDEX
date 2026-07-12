use std::{env, fs, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-env-changed=RISC0_SKIP_BUILD");
    println!("cargo:rerun-if-env-changed=CLIPPY_ARGS");
    println!("cargo:rerun-if-env-changed=CARGO_CFG_CLIPPY");

    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR must be set"));
    let methods_rs = out_dir.join("methods.rs");
    if env::var_os("RISC0_SKIP_BUILD").is_some() || is_clippy_build() {
        write_placeholder(&methods_rs);
        return;
    }

    risc0_build::embed_methods();
}

fn write_placeholder(methods_rs: &std::path::Path) {
    let stub = r#"
// Placeholder for host-only tests and linting. Evidence and production callers
// must reject the empty ELF and all-zero image ID.
pub const ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF: &[u8] = &[];
pub const ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID: [u32; 8] = [0; 8];
pub const ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF: &[u8] = &[];
pub const ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID: [u32; 8] = [0; 8];
pub const ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ELF: &[u8] = &[];
pub const ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID: [u32; 8] = [0; 8];
pub const ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ELF: &[u8] = &[];
pub const ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID: [u32; 8] = [0; 8];
pub const ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ELF: &[u8] = &[];
pub const ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V4_ID: [u32; 8] = [0; 8];
"#;
    fs::write(methods_rs, stub).expect("write placeholder methods.rs");
}

fn is_clippy_build() -> bool {
    env::var_os("CARGO_CFG_CLIPPY").is_some()
        || env::var_os("CLIPPY_ARGS").is_some()
        || env::var("RUSTC_WORKSPACE_WRAPPER")
            .ok()
            .is_some_and(|value| value.contains("clippy"))
}
