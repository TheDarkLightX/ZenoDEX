fn main() {
    println!("cargo:rerun-if-env-changed=RISC0_SKIP_BUILD");
    if std::env::var_os("RISC0_SKIP_BUILD").is_some() {
        panic!("custody V2 methods require an actual guest build; unset RISC0_SKIP_BUILD");
    }
    risc0_build::embed_methods();
}
