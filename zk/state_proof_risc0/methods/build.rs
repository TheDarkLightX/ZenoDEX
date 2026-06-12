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
// - Install the Risc0 toolchain/components:
//     rzup install
// - Then rebuild without RISC0_SKIP_BUILD=1.
//
// For fail-closed builds, set RISC0_FORCE_BUILD=1.

pub const TAU_STATE_PROOF_RISC0_GUEST_ELF: &[u8] = &[];
pub const TAU_STATE_PROOF_RISC0_GUEST_ID: [u32; 8] = [0; 8];
"#;
        std::fs::write(&methods_rs, stub).expect("write placeholder methods.rs");
    };

    if std::env::var("RISC0_SKIP_BUILD").as_deref() == Ok("1") {
        println!(
            "cargo:warning=RISC0_SKIP_BUILD=1: using placeholder methods (ELF empty, ID all-zero)"
        );
        write_placeholder();
        return;
    }

    let force = std::env::var("RISC0_FORCE_BUILD").as_deref() == Ok("1");

    let toolchain_ok = rustup_target_ok() || rzup_components_ok();

    if !toolchain_ok && !force {
        println!(
            "cargo:warning=Risc0 guest toolchain/components not detected; using placeholder methods. Install with `rzup install`, or set RISC0_FORCE_BUILD=1 to fail-closed."
        );
        write_placeholder();
        return;
    }

    risc0_build::embed_methods();
}

fn rustup_target_ok() -> bool {
    command_stdout("rustup", &["+risc0", "target", "list", "--installed"])
        .is_some_and(|out| out.lines().any(|l| l.trim() == "riscv32im-risc0-zkvm-elf"))
}

fn rzup_components_ok() -> bool {
    command_stdout("rzup", &["show"]).is_some_and(|out| {
        component_present(&out, "cargo-risczero")
            && component_present(&out, "r0vm")
            && component_present(&out, "rust")
    })
}

fn component_present(output: &str, name: &str) -> bool {
    output.lines().any(|line| line.trim() == name)
}

fn command_stdout(program: &str, args: &[&str]) -> Option<String> {
    std::process::Command::new(program)
        .args(args)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).into_owned())
}
