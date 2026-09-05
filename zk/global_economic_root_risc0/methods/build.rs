use std::{env, fs, path::PathBuf};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("cargo:rerun-if-env-changed=RISC0_SKIP_BUILD");
    println!("cargo:rerun-if-env-changed=CARGO_CFG_CLIPPY");
    println!("cargo:rerun-if-env-changed=CLIPPY_ARGS");
    let clippy = env::var_os("CARGO_CFG_CLIPPY").is_some()
        || env::var_os("CLIPPY_ARGS").is_some()
        || env::var("RUSTC_WORKSPACE_WRAPPER")
            .ok()
            .is_some_and(|v| v.contains("clippy"));
    if env::var_os("RISC0_SKIP_BUILD").is_some() || clippy {
        let out = PathBuf::from(env::var_os("OUT_DIR").ok_or("OUT_DIR missing")?);
        fs::write(out.join("methods.rs"),
            "pub const ZENODEX_ECONOMIC_ROOT_GUEST_ELF: &[u8] = &[];\npub const ZENODEX_ECONOMIC_ROOT_GUEST_ID: [u32; 8] = [0; 8];\n")?;
    } else {
        risc0_build::embed_methods();
    }
    Ok(())
}
