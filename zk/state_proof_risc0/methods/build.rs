fn main() {
    println!("cargo:rerun-if-env-changed=RISC0_SKIP_BUILD");
    println!("cargo:rerun-if-env-changed=RISC0_FORCE_BUILD");

    let out_dir =
        std::path::PathBuf::from(std::env::var_os("OUT_DIR").expect("OUT_DIR must be set"));
    let methods_rs = out_dir.join("methods.rs");

    let write_placeholder = || {
        let stub = r#"// @generated (placeholder)
// Risc0 guest methods are not embedded in this build.
//
// - Install the Risc0 toolchain and target:
//     rustup target add riscv32im-risc0-zkvm-elf --toolchain risc0
// - Then rebuild without RISC0_SKIP_BUILD=1.
//
// For fail-closed builds, set RISC0_FORCE_BUILD=1.

pub const TAU_STATE_PROOF_GUEST_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_GUEST_ID: [u32; 8] = [0; 8];
"#;
        std::fs::write(&methods_rs, stub).expect("write placeholder methods.rs");
    };

    if std::env::var("RISC0_SKIP_BUILD").as_deref() == Ok("1") {
        println!("cargo:warning=RISC0_SKIP_BUILD=1: using placeholder methods (ELF empty, ID all-zero)");
        write_placeholder();
        return;
    }

    let force = std::env::var("RISC0_FORCE_BUILD").as_deref() == Ok("1");

    let target_ok = std::process::Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain", "risc0"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).into_owned())
        .is_some_and(|out| out.lines().any(|l| l.trim() == "riscv32im-risc0-zkvm-elf"));

    if !target_ok && !force {
        println!(
            "cargo:warning=Risc0 target `riscv32im-risc0-zkvm-elf` not installed for toolchain `risc0`; using placeholder methods. Install with `rustup target add riscv32im-risc0-zkvm-elf --toolchain risc0`, or set RISC0_FORCE_BUILD=1 to fail-closed."
        );
        write_placeholder();
        return;
    }

    risc0_build::embed_methods();
}

