fn main() {
    println!("cargo:rerun-if-env-changed=RISC0_SKIP_BUILD");
    if std::env::var_os("RISC0_SKIP_BUILD").is_some() {
        panic!("margin V2 methods require an actual guest build; unset RISC0_SKIP_BUILD");
    }
    // Host Clippy uses its own sysroot, which has no zkVM std library. The
    // nested guest build must use the SDK-selected RISC0 compiler directly.
    // Native workspace targets retain the outer Cargo Clippy wrapper.
    std::env::remove_var("RUSTC_WORKSPACE_WRAPPER");
    risc0_build::embed_methods();
}
