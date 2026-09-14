fn main() {
    println!("cargo:rerun-if-env-changed=RISC0_SKIP_BUILD");
    if std::env::var_os("RISC0_SKIP_BUILD").is_some() {
        panic!("Spot methods require an actual guest build; unset RISC0_SKIP_BUILD");
    }
    // The nested guest build must use the SDK sysroot, not host Clippy's.
    std::env::remove_var("RUSTC_WORKSPACE_WRAPPER");
    risc0_build::embed_methods();
}
