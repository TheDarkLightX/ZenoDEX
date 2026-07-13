use std::{env, fs, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-env-changed=RISC0_SKIP_BUILD");
    println!("cargo:rerun-if-env-changed=CLIPPY_ARGS");
    println!("cargo:rerun-if-env-changed=CARGO_CFG_CLIPPY");
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR must be set"));
    let methods_rs = out_dir.join("methods.rs");
    if env::var_os("RISC0_SKIP_BUILD").is_some() || is_clippy_build() {
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
    risc0_build::embed_methods();
}

fn is_clippy_build() -> bool {
    env::var_os("CARGO_CFG_CLIPPY").is_some()
        || env::var_os("CLIPPY_ARGS").is_some()
        || env::var("RUSTC_WORKSPACE_WRAPPER")
            .ok()
            .is_some_and(|value| value.contains("clippy"))
}
