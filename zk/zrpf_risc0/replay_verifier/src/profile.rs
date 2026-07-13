pub(crate) const REPORT_SCHEMA: &str = "zenodex/zrpf_v3_retained_structural_replay/v1";
pub(crate) const REPLAY_PROFILE_ID: &str = "zrpf_v3_retained_structural_receipt_replay_v1";
pub(crate) const EXPECTED_ROOT_JOURNAL_HASH: &str =
    "2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768";
pub(crate) const MAX_RECEIPT_READ_BYTES_U64: u64 = 16_777_217;
pub(crate) const ROOT_SEAL_MUTATION_WORD_INDEX: usize = 1;

pub(crate) const ADAPTER_ID: [u32; 8] = [
    0xb582_f271,
    0x10c6_7f51,
    0xccc1_8889,
    0x8001_469b,
    0x33ae_407a,
    0x0f0f_0e1c,
    0x2bd1_0555,
    0x7455_1e24,
];
pub(crate) const LEVEL_ONE_ID: [u32; 8] = [
    0x51be_7242,
    0x295e_f665,
    0x814f_13cb,
    0xc46f_6c5d,
    0x2949_7f0d,
    0x0896_f579,
    0xc310_ac2c,
    0x2b3c_d4f0,
];
pub(crate) const LEVEL_TWO_ID: [u32; 8] = [
    0x118d_853b,
    0xb255_b13c,
    0x731c_6e94,
    0xe55f_df3f,
    0xf46b_2b59,
    0x0a3d_906c,
    0x2032_fb3c,
    0x3657_8499,
];

pub(crate) const LEAF_NAMES: [&str; 4] = [
    "adapter-leaf-0.receipt.json",
    "adapter-leaf-1.receipt.json",
    "adapter-leaf-2.receipt.json",
    "adapter-leaf-3.receipt.json",
];
pub(crate) const LEVEL_ONE_NAMES: [&str; 2] = [
    "structural-l1-left.receipt.json",
    "structural-l1-right.receipt.json",
];
pub(crate) const ROOT_NAME: &str = "structural-l2-root.receipt.json";
pub(crate) const MUTATION_NAME: &str = "structural-l2-root.seal-word-1-xor-lsb.receipt.json";

pub(crate) const RETAINED_ARTIFACTS: [RetainedArtifact; 8] = [
    RetainedArtifact::new(
        LEAF_NAMES[0],
        593_416,
        "219e389be6ff9d035f86b6d73de8c4f95fae230956382d2fd63823167047b63a",
    ),
    RetainedArtifact::new(
        LEAF_NAMES[1],
        593_399,
        "af45ec023d8939648c741389d9e766d5d1dd2945811652bae42e998d84bb3a82",
    ),
    RetainedArtifact::new(
        LEAF_NAMES[2],
        593_136,
        "4e09c872617143e9ac360ea8059b6f2a20ab6e5ce05eb7cf51eead70f974965a",
    ),
    RetainedArtifact::new(
        LEAF_NAMES[3],
        593_032,
        "7030c4a4818b31623fb137ebdac0eb8bb2af8cbeb9fdc1e8d3dcb75fc26ef8f4",
    ),
    RetainedArtifact::new(
        LEVEL_ONE_NAMES[0],
        593_161,
        "47b850237585faeee953b04dae72d21c5d87adfb710d4e914314d4a72e6c1cd5",
    ),
    RetainedArtifact::new(
        LEVEL_ONE_NAMES[1],
        593_280,
        "a6b8ceaa559bfe85fa9263fefcec9438e78ec721632fbd7a1cf651867d30348d",
    ),
    RetainedArtifact::new(
        ROOT_NAME,
        593_320,
        "edd25fca20b0205c2f778b866605b343922615623256abcc1a098957664c2d16",
    ),
    RetainedArtifact::new(
        MUTATION_NAME,
        593_320,
        "27c71152044124762efd5398fa6206a9627a5eae2ed9db851b1bb33783c6e985",
    ),
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RetainedArtifact {
    pub(crate) name: &'static str,
    pub(crate) size_bytes: usize,
    pub(crate) sha256: &'static str,
}

impl RetainedArtifact {
    const fn new(name: &'static str, size_bytes: usize, sha256: &'static str) -> Self {
        Self {
            name,
            size_bytes,
            sha256,
        }
    }
}
