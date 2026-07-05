use std::{env, fs, path::PathBuf, process::Command};

const RISC0_TARGET: &str = "riscv32im-risc0-zkvm-elf";

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

    let force = env::var("RISC0_FORCE_BUILD").as_deref() == Ok("1");
    if !risc0_sysroot_has_target() && !force {
        println!(
            "cargo:warning=Risc0 target `{RISC0_TARGET}` not found under rustup toolchain `risc0`; using placeholder methods. Install with `rzup install`, or set RISC0_FORCE_BUILD=1 to fail closed."
        );
        write_placeholder(&methods_rs);
        return;
    }

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
pub const TAU_STATE_PROOF_RISC0_SPOT_LEAF_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_RISC0_SPOT_LEAF_ID: [u32; 8] = [0; 8];
pub const TAU_STATE_PROOF_RISC0_SUMMARY_LEAF_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_RISC0_SUMMARY_LEAF_ID: [u32; 8] = [0; 8];
pub const TAU_STATE_PROOF_RISC0_ZUSD_LEAF_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_RISC0_ZUSD_LEAF_ID: [u32; 8] = [0; 8];
"#;
    fs::write(methods_rs, stub).expect("write placeholder methods.rs");
}

fn risc0_sysroot_has_target() -> bool {
    let Ok(output) = Command::new("rustup")
        .arg("+risc0")
        .args(["which", "rustc"])
        .output()
    else {
        return false;
    };
    if !output.status.success() {
        return false;
    }
    let rustc = String::from_utf8_lossy(&output.stdout);
    let rustc = std::path::Path::new(rustc.trim());
    let Some(sysroot) = rustc.parent().and_then(std::path::Path::parent) else {
        return false;
    };
    let target_lib = sysroot
        .join("lib")
        .join("rustlib")
        .join(RISC0_TARGET)
        .join("lib");
    let Ok(entries) = fs::read_dir(target_lib) else {
        return false;
    };
    entries.filter_map(Result::ok).any(|entry| {
        entry
            .file_name()
            .to_str()
            .is_some_and(|name| name.starts_with("libcore-") && name.ends_with(".rlib"))
    })
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
