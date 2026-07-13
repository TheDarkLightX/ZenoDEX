use std::{env, fs, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-env-changed=RISC0_SKIP_BUILD");
    println!("cargo:rerun-if-env-changed=RISC0_FORCE_BUILD");

    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR must be set"));
    let methods_rs = out_dir.join("methods.rs");

    if env::var("RISC0_SKIP_BUILD").as_deref() == Ok("1") {
        println!(
            "cargo:warning=RISC0_SKIP_BUILD=1: using placeholder methods (ELF empty, ID all-zero)"
        );
        write_placeholder(&methods_rs);
        return;
    }
    if is_clippy_build() {
        println!("cargo:warning=clippy build: using placeholder methods for lint-only pass");
        write_placeholder(&methods_rs);
        return;
    }

    // risc0-build 3.x resolves its guest compiler through rzup/RISC0_HOME. Any
    // missing or mismatched toolchain must fail the build instead of silently
    // producing a placeholder production binary.
    risc0_build::embed_methods();
}

fn write_placeholder(methods_rs: &std::path::Path) {
    let stub = r#"// @generated (placeholder)
// Risc0 guest methods are not embedded in this build.
//
// - Install the Risc0 toolchain:
//     rzup install
// - Then rebuild without RISC0_SKIP_BUILD=1.
//
// For fail-closed builds, set RISC0_FORCE_BUILD=1.

pub const TAU_STATE_PROOF_RISC0_GUEST_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_RISC0_GUEST_ID: [u32; 8] = [0; 8];
pub const TAU_STATE_PROOF_RISC0_AGGREGATE_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_RISC0_AGGREGATE_ID: [u32; 8] = [0; 8];
pub const TAU_STATE_PROOF_RISC0_PERPS_NP_LEAF_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_RISC0_PERPS_NP_LEAF_ID: [u32; 8] = [0; 8];
pub const TAU_STATE_PROOF_RISC0_SPOT_LEAF_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_RISC0_SPOT_LEAF_ID: [u32; 8] = [0; 8];
pub const TAU_STATE_PROOF_RISC0_SUMMARY_LEAF_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_RISC0_SUMMARY_LEAF_ID: [u32; 8] = [0; 8];
pub const TAU_STATE_PROOF_RISC0_ZUSD_LEAF_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_RISC0_ZUSD_LEAF_ID: [u32; 8] = [0; 8];
"#;
    fs::write(methods_rs, stub).expect("write placeholder methods.rs");
}

fn is_clippy_build() -> bool {
    env::var_os("CARGO_CFG_CLIPPY").is_some()
        || env::var_os("CLIPPY_ARGS").is_some()
        || env_contains("RUSTC_WRAPPER", "clippy")
        || env_contains("RUSTC_WORKSPACE_WRAPPER", "clippy")
}

fn env_contains(key: &str, needle: &str) -> bool {
    env::var_os(key)
        .and_then(|value| value.into_string().ok())
        .is_some_and(|value| value.contains(needle))
}
