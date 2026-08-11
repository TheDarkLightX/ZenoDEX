use std::{env, fs, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-env-changed=RISC0_SKIP_BUILD");
    println!("cargo:rerun-if-env-changed=CARGO_CFG_CLIPPY");
    println!("cargo:rerun-if-env-changed=CLIPPY_ARGS");

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
// Host-only placeholder. Verification and proving callers reject both values.
pub const ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF: &[u8] = &[];
pub const ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID: [u32; 8] = [0; 8];
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
