include!(concat!(env!("OUT_DIR"), "/methods.rs"));

// `risc0_build::embed_methods` derives these names from the guest binary.
// Host code consumes the stable profile aliases below in real and skipped
// builds, so build-mode naming cannot change the verifier ABI.
pub use ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_GUEST_ELF as ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ELF;
pub use ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_GUEST_ID as ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID;
