use zenodex_zrpf_protocol_v3::{
    CommitmentV3, EconomicLaneIdV1, LaneModuleMigrationCompatibilityV1, LaneModuleMigrationModeV1,
    LaneModuleProvenanceRootsV1, LaneModuleReleaseContentV1, LaneModuleReleaseIdV1,
    LaneModuleReleaseStatusV1, LaneModuleReleaseV1, LaneModuleResourceLimitsV1,
    LaneModuleSchemaRootsV1, LaneModuleTerminalCoverageV1, ProgramIdV3, TerminalCoverageStatusV1,
};

#[derive(Clone, Copy)]
struct IdentityFixture {
    lane_id: EconomicLaneIdV1,
    schemas: LaneModuleSchemaRootsV1,
    command_variants_root: CommitmentV3,
    provenance: LaneModuleProvenanceRootsV1,
    terminal: LaneModuleTerminalCoverageV1,
    migration: LaneModuleMigrationCompatibilityV1,
    resource_limits: LaneModuleResourceLimitsV1,
}

impl IdentityFixture {
    fn baseline() -> Self {
        Self {
            lane_id: EconomicLaneIdV1::SpotLiquidity,
            schemas: LaneModuleSchemaRootsV1::new(root(1), root(2), root(3), root(4)),
            command_variants_root: root(5),
            provenance: LaneModuleProvenanceRootsV1::new(program_id(6), root(7), root(8), root(9)),
            terminal: LaneModuleTerminalCoverageV1::new(
                TerminalCoverageStatusV1::Complete,
                root(10),
            ),
            migration: LaneModuleMigrationCompatibilityV1::new(
                LaneModuleMigrationModeV1::Genesis,
                None,
                root(11),
            )
            .unwrap(),
            resource_limits: limits(1_024, 65_536, 4_096, 1_000_000),
        }
    }

    fn release(self, status: LaneModuleReleaseStatusV1) -> LaneModuleReleaseV1 {
        let content = LaneModuleReleaseContentV1::new(
            self.lane_id,
            self.schemas,
            self.command_variants_root,
            self.provenance,
            self.terminal,
            self.migration,
            self.resource_limits,
        );
        LaneModuleReleaseV1::new(content, status).expect("identity fixture must be valid")
    }

    fn release_id(self) -> LaneModuleReleaseIdV1 {
        self.release(LaneModuleReleaseStatusV1::Candidate)
            .release_id()
    }
}

fn root(byte: u8) -> CommitmentV3 {
    CommitmentV3::new([byte; 32]).unwrap()
}

fn program_id(byte: u8) -> ProgramIdV3 {
    ProgramIdV3::new([byte; 32]).unwrap()
}

fn predecessor(byte: u8) -> LaneModuleReleaseIdV1 {
    LaneModuleReleaseIdV1::new([byte; 32]).unwrap()
}

fn limits(
    max_command_bytes: u32,
    max_state_bytes: u32,
    max_journal_bytes: u32,
    max_cycles: u64,
) -> LaneModuleResourceLimitsV1 {
    LaneModuleResourceLimitsV1::new(
        max_command_bytes,
        max_state_bytes,
        max_journal_bytes,
        max_cycles,
    )
    .unwrap()
}

fn hex32(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn assert_ids_change(baseline: IdentityFixture, mutations: &[IdentityFixture]) {
    let baseline_id = baseline.release_id();
    for mutation in mutations {
        assert_ne!(baseline_id, mutation.release_id());
    }
}

#[test]
fn lifecycle_status_is_outside_content_identity_and_record_commitment_binds_it() {
    // Arrange
    let fixture = IdentityFixture::baseline();

    // Act
    let candidate = fixture.release(LaneModuleReleaseStatusV1::Candidate);
    let shadow = fixture.release(LaneModuleReleaseStatusV1::Shadow);

    // Assert
    assert_eq!(candidate.release_id(), shadow.release_id());
    assert_eq!(
        hex32(candidate.release_id().into_bytes()),
        "bccb5f3d9db235c60e823e89bfade730efb13bc17a30be755bb8dc0a3e092de0"
    );
    assert_ne!(
        candidate.canonical_record_commitment().unwrap(),
        shadow.canonical_record_commitment().unwrap()
    );
}

#[test]
fn content_identity_binds_each_schema_and_command_variant_root() {
    // Arrange
    let baseline = IdentityFixture::baseline();
    let mutations = [
        IdentityFixture {
            schemas: LaneModuleSchemaRootsV1::new(root(12), root(2), root(3), root(4)),
            ..baseline
        },
        IdentityFixture {
            schemas: LaneModuleSchemaRootsV1::new(root(1), root(12), root(3), root(4)),
            ..baseline
        },
        IdentityFixture {
            schemas: LaneModuleSchemaRootsV1::new(root(1), root(2), root(12), root(4)),
            ..baseline
        },
        IdentityFixture {
            schemas: LaneModuleSchemaRootsV1::new(root(1), root(2), root(3), root(12)),
            ..baseline
        },
        IdentityFixture {
            command_variants_root: root(12),
            ..baseline
        },
    ];

    // Act / Assert
    assert_ids_change(baseline, &mutations);
}

#[test]
fn content_identity_binds_guest_image_spec_source_and_toolchain_roots() {
    // Arrange
    let baseline = IdentityFixture::baseline();
    let mutations = [
        IdentityFixture {
            provenance: LaneModuleProvenanceRootsV1::new(program_id(12), root(7), root(8), root(9)),
            ..baseline
        },
        IdentityFixture {
            provenance: LaneModuleProvenanceRootsV1::new(program_id(6), root(12), root(8), root(9)),
            ..baseline
        },
        IdentityFixture {
            provenance: LaneModuleProvenanceRootsV1::new(program_id(6), root(7), root(12), root(9)),
            ..baseline
        },
        IdentityFixture {
            provenance: LaneModuleProvenanceRootsV1::new(program_id(6), root(7), root(8), root(12)),
            ..baseline
        },
    ];

    // Act / Assert
    assert_ids_change(baseline, &mutations);
}

#[test]
fn content_identity_binds_lane_terminal_and_migration_contracts() {
    // Arrange
    let baseline = IdentityFixture::baseline();
    let mutations = [
        IdentityFixture {
            lane_id: EconomicLaneIdV1::OracleMarket,
            ..baseline
        },
        IdentityFixture {
            terminal: LaneModuleTerminalCoverageV1::new(
                TerminalCoverageStatusV1::Incomplete,
                root(10),
            ),
            ..baseline
        },
        IdentityFixture {
            terminal: LaneModuleTerminalCoverageV1::new(
                TerminalCoverageStatusV1::Complete,
                root(12),
            ),
            ..baseline
        },
        IdentityFixture {
            migration: LaneModuleMigrationCompatibilityV1::new(
                LaneModuleMigrationModeV1::CoexistAndDrain,
                Some(predecessor(12)),
                root(11),
            )
            .unwrap(),
            ..baseline
        },
        IdentityFixture {
            migration: LaneModuleMigrationCompatibilityV1::new(
                LaneModuleMigrationModeV1::Genesis,
                None,
                root(12),
            )
            .unwrap(),
            ..baseline
        },
    ];

    // Act / Assert
    assert_ids_change(baseline, &mutations);
}

#[test]
fn content_identity_binds_each_resource_limit() {
    // Arrange
    let baseline = IdentityFixture::baseline();
    let mutations = [
        IdentityFixture {
            resource_limits: limits(1_025, 65_536, 4_096, 1_000_000),
            ..baseline
        },
        IdentityFixture {
            resource_limits: limits(1_024, 65_537, 4_096, 1_000_000),
            ..baseline
        },
        IdentityFixture {
            resource_limits: limits(1_024, 65_536, 4_097, 1_000_000),
            ..baseline
        },
        IdentityFixture {
            resource_limits: limits(1_024, 65_536, 4_096, 1_000_001),
            ..baseline
        },
    ];

    // Act / Assert
    assert_ids_change(baseline, &mutations);
}
