use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    CommitmentV3, EconomicLaneIdV1, LaneModuleMigrationCompatibilityV1, LaneModuleMigrationModeV1,
    LaneModuleProvenanceRootsV1, LaneModuleReleaseContentV1, LaneModuleReleaseIdV1,
    LaneModuleReleaseRegistryV1, LaneModuleReleaseStatusV1, LaneModuleReleaseV1,
    LaneModuleResourceLimitsV1, LaneModuleSchemaRootsV1, LaneModuleTerminalCoverageV1, ProgramIdV3,
    TerminalCoverageStatusV1, LANE_MODULE_RELEASE_REGISTRY_VERSION_V1,
};

pub fn root(seed: u8, offset: u8) -> CommitmentV3 {
    CommitmentV3::new([nonzero_byte(seed, offset); 32]).expect("fixture commitment byte is nonzero")
}

fn program_id(seed: u8) -> ProgramIdV3 {
    ProgramIdV3::new([nonzero_byte(seed, 5); 32]).expect("fixture program ID byte is nonzero")
}

fn nonzero_byte(seed: u8, offset: u8) -> u8 {
    let value = (u16::from(seed) + u16::from(offset)) % 255;
    u8::try_from(value + 1).expect("value is in the nonzero byte domain")
}

pub fn release(
    lane_id: EconomicLaneIdV1,
    seed: u8,
    status: LaneModuleReleaseStatusV1,
    predecessor_release_id: Option<LaneModuleReleaseIdV1>,
) -> LaneModuleReleaseV1 {
    let migration_mode = if predecessor_release_id.is_some() {
        LaneModuleMigrationModeV1::CoexistAndDrain
    } else {
        LaneModuleMigrationModeV1::Genesis
    };
    let migration = LaneModuleMigrationCompatibilityV1::new(
        migration_mode,
        predecessor_release_id,
        root(seed, 11),
    )
    .expect("fixture migration shape is valid");
    let content = LaneModuleReleaseContentV1::new(
        lane_id,
        LaneModuleSchemaRootsV1::new(root(seed, 0), root(seed, 1), root(seed, 2), root(seed, 3)),
        root(seed, 4),
        LaneModuleProvenanceRootsV1::new(
            program_id(seed),
            root(seed, 6),
            root(seed, 7),
            root(seed, 8),
        ),
        LaneModuleTerminalCoverageV1::new(TerminalCoverageStatusV1::Complete, root(seed, 9)),
        migration,
        LaneModuleResourceLimitsV1::new(
            u32::from(seed) + 1,
            u32::from(seed) + 2,
            u32::from(seed) + 3,
            u64::from(seed) + 4,
        )
        .expect("fixture resource limits are nonzero"),
    );
    LaneModuleReleaseV1::new(content, status).expect("fixture release is valid")
}

pub fn canonical(mut releases: Vec<LaneModuleReleaseV1>) -> Vec<LaneModuleReleaseV1> {
    releases.sort_by_key(LaneModuleReleaseV1::release_id);
    releases
}

pub fn registry(releases: Vec<LaneModuleReleaseV1>) -> LaneModuleReleaseRegistryV1 {
    LaneModuleReleaseRegistryV1::new(EconomicLaneIdV1::SpotLiquidity, canonical(releases))
        .expect("fixture registry is valid")
}

pub fn independent_registry_root(registry: &LaneModuleReleaseRegistryV1) -> CommitmentV3 {
    let domain = b"zenodex.global_settlement.lane_module_release_registry.v1";
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher.update(LANE_MODULE_RELEASE_REGISTRY_VERSION_V1.to_be_bytes());
    hasher.update([registry.lane_id().code()]);
    hasher.update(
        u16::try_from(registry.releases().len())
            .unwrap()
            .to_be_bytes(),
    );
    for release in registry.releases() {
        hasher.update(
            release
                .canonical_record_commitment()
                .expect("fixture record commitment")
                .as_bytes(),
        );
    }
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

pub fn hex32(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
