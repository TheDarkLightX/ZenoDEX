use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_lane_module_release_v1, encode_lane_module_release_v1, CommitmentV3,
    EconomicLaneIdV1, LaneModuleMigrationCompatibilityV1, LaneModuleMigrationModeV1,
    LaneModuleProvenanceRootsV1, LaneModuleReleaseContentV1, LaneModuleReleaseErrorV1,
    LaneModuleReleaseIdV1, LaneModuleReleaseStatusV1, LaneModuleReleaseV1,
    LaneModuleResourceLimitsV1, LaneModuleSchemaRootsV1, LaneModuleTerminalCoverageV1, ProgramIdV3,
    TerminalCoverageStatusV1, MAX_LANE_MODULE_RELEASE_BYTES_V1,
};

#[path = "lane_module_release_v1/identity.rs"]
mod identity;

fn root(byte: u8) -> CommitmentV3 {
    CommitmentV3::new([byte; 32]).expect("fixture commitment must be nonzero")
}

fn predecessor(byte: u8) -> LaneModuleReleaseIdV1 {
    LaneModuleReleaseIdV1::new([byte; 32]).expect("fixture release ID must be nonzero")
}

fn program_id(byte: u8) -> ProgramIdV3 {
    ProgramIdV3::new([byte; 32]).expect("fixture guest image ID must be nonzero")
}

fn hex32(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn limits(
    max_command_bytes: u32,
    max_state_bytes: u32,
    max_journal_bytes: u32,
    max_cycles: u64,
) -> Result<LaneModuleResourceLimitsV1, LaneModuleReleaseErrorV1> {
    LaneModuleResourceLimitsV1::new(
        max_command_bytes,
        max_state_bytes,
        max_journal_bytes,
        max_cycles,
    )
}

fn content(
    terminal_status: TerminalCoverageStatusV1,
    migration_mode: LaneModuleMigrationModeV1,
    predecessor_release_id: Option<LaneModuleReleaseIdV1>,
    resource_limits: LaneModuleResourceLimitsV1,
) -> Result<LaneModuleReleaseContentV1, LaneModuleReleaseErrorV1> {
    let schemas = LaneModuleSchemaRootsV1::new(root(1), root(2), root(3), root(4));
    let provenance = LaneModuleProvenanceRootsV1::new(program_id(6), root(7), root(8), root(9));
    let terminal = LaneModuleTerminalCoverageV1::new(terminal_status, root(10));
    let migration =
        LaneModuleMigrationCompatibilityV1::new(migration_mode, predecessor_release_id, root(11))?;
    Ok(LaneModuleReleaseContentV1::new(
        EconomicLaneIdV1::SpotLiquidity,
        schemas,
        root(5),
        provenance,
        terminal,
        migration,
        resource_limits,
    ))
}

fn complete_content() -> LaneModuleReleaseContentV1 {
    content(
        TerminalCoverageStatusV1::Complete,
        LaneModuleMigrationModeV1::Genesis,
        None,
        limits(1_024, 65_536, 4_096, 1_000_000).expect("valid fixture limits"),
    )
    .expect("valid complete release content")
}

fn complete_release(status: LaneModuleReleaseStatusV1) -> LaneModuleReleaseV1 {
    LaneModuleReleaseV1::new(complete_content(), status).expect("valid complete release")
}

#[test]
fn release_status_codes_and_transition_graph_are_closed() {
    // Arrange
    let statuses = [
        LaneModuleReleaseStatusV1::Candidate,
        LaneModuleReleaseStatusV1::Shadow,
        LaneModuleReleaseStatusV1::ActiveNew,
        LaneModuleReleaseStatusV1::DrainOnly,
        LaneModuleReleaseStatusV1::VerifyOnly,
        LaneModuleReleaseStatusV1::Retired,
        LaneModuleReleaseStatusV1::Revoked,
    ];
    assert_eq!(
        statuses.map(LaneModuleReleaseStatusV1::code),
        [0, 1, 2, 3, 4, 5, 6]
    );

    for from in statuses {
        for to in statuses {
            let release = complete_release(from);
            let before = release.clone();
            let expected = matches!(
                (from, to),
                (
                    LaneModuleReleaseStatusV1::Candidate,
                    LaneModuleReleaseStatusV1::Shadow
                ) | (
                    LaneModuleReleaseStatusV1::Shadow,
                    LaneModuleReleaseStatusV1::ActiveNew
                ) | (
                    LaneModuleReleaseStatusV1::ActiveNew,
                    LaneModuleReleaseStatusV1::DrainOnly
                ) | (
                    LaneModuleReleaseStatusV1::DrainOnly,
                    LaneModuleReleaseStatusV1::VerifyOnly
                ) | (
                    LaneModuleReleaseStatusV1::VerifyOnly,
                    LaneModuleReleaseStatusV1::Retired
                )
            ) || (to == LaneModuleReleaseStatusV1::Revoked
                && from != LaneModuleReleaseStatusV1::Revoked);

            // Act
            let result = release.transition_status(to);

            // Assert
            if expected {
                let transitioned = result.expect("declared lifecycle edge must be accepted");
                assert_eq!(transitioned.status(), to);
                assert_eq!(transitioned.release_id(), before.release_id());
                assert_eq!(transitioned.content(), before.content());
            } else {
                assert_eq!(
                    result,
                    Err(LaneModuleReleaseErrorV1::InvalidStatusTransition { from, to })
                );
                assert_eq!(release, before);
            }
        }
    }
}

#[test]
fn terminal_incomplete_release_cannot_gain_current_authority() {
    // Arrange
    let incomplete = content(
        TerminalCoverageStatusV1::Incomplete,
        LaneModuleMigrationModeV1::Genesis,
        None,
        limits(1, 1, 1, 1).expect("one-unit limits are valid"),
    )
    .expect("incomplete candidate content is representable");
    let candidate =
        LaneModuleReleaseV1::new(incomplete.clone(), LaneModuleReleaseStatusV1::Candidate)
            .expect("incomplete candidate is valid");
    let shadow = candidate
        .transition_status(LaneModuleReleaseStatusV1::Shadow)
        .expect("incomplete content may enter shadow");
    let before = shadow.clone();

    // Act
    let promotion = shadow.transition_status(LaneModuleReleaseStatusV1::ActiveNew);
    let direct = LaneModuleReleaseV1::new(incomplete, LaneModuleReleaseStatusV1::ActiveNew);

    // Assert
    let expected =
        LaneModuleReleaseErrorV1::TerminalCoverageIncomplete(LaneModuleReleaseStatusV1::ActiveNew);
    assert_eq!(promotion, Err(expected.clone()));
    assert_eq!(direct, Err(expected));
    assert_eq!(shadow, before);
}

#[test]
fn status_admission_is_exact_and_reject_is_noop() {
    let statuses = [
        LaneModuleReleaseStatusV1::Candidate,
        LaneModuleReleaseStatusV1::Shadow,
        LaneModuleReleaseStatusV1::ActiveNew,
        LaneModuleReleaseStatusV1::DrainOnly,
        LaneModuleReleaseStatusV1::VerifyOnly,
        LaneModuleReleaseStatusV1::Retired,
        LaneModuleReleaseStatusV1::Revoked,
    ];

    for status in statuses {
        // Arrange
        let release = complete_release(status);
        let before = release.clone();
        let commitment_before = release.canonical_record_commitment().unwrap();

        // Act
        let new_object = release.admit_new_object_creation();
        let existing_object = release.admit_existing_object_transition();

        // Assert
        if status == LaneModuleReleaseStatusV1::ActiveNew {
            assert_eq!(new_object, Ok(()));
        } else {
            assert_eq!(
                new_object,
                Err(LaneModuleReleaseErrorV1::StatusDisallowsNewObject(status))
            );
        }
        if matches!(
            status,
            LaneModuleReleaseStatusV1::ActiveNew | LaneModuleReleaseStatusV1::DrainOnly
        ) {
            assert_eq!(existing_object, Ok(()));
        } else {
            assert_eq!(
                existing_object,
                Err(LaneModuleReleaseErrorV1::StatusDisallowsExistingObject(
                    status
                ))
            );
        }
        assert_eq!(release, before);
        assert_eq!(
            release.canonical_record_commitment().unwrap(),
            commitment_before
        );
    }
}

#[test]
fn migration_mode_and_predecessor_cardinality_are_exact() {
    // Arrange / Act / Assert
    assert_eq!(
        LaneModuleMigrationCompatibilityV1::new(
            LaneModuleMigrationModeV1::Genesis,
            Some(predecessor(12)),
            root(11),
        ),
        Err(LaneModuleReleaseErrorV1::UnexpectedMigrationPredecessor)
    );
    for mode in [
        LaneModuleMigrationModeV1::CoexistAndDrain,
        LaneModuleMigrationModeV1::ProvedBulkMigration,
    ] {
        assert_eq!(
            LaneModuleMigrationCompatibilityV1::new(mode, None, root(11)),
            Err(LaneModuleReleaseErrorV1::MissingMigrationPredecessor(mode))
        );
        assert!(
            LaneModuleMigrationCompatibilityV1::new(mode, Some(predecessor(12)), root(11),).is_ok()
        );
    }
    assert_eq!(
        LaneModuleReleaseIdV1::new([0; 32]),
        Err(LaneModuleReleaseErrorV1::ZeroReleaseId)
    );
}

#[test]
fn resource_limits_cover_zero_one_and_integer_maxima() {
    // Arrange / Act / Assert
    assert_eq!(
        limits(0, 1, 1, 1),
        Err(LaneModuleReleaseErrorV1::ZeroResourceLimit(
            "max_command_bytes"
        ))
    );
    assert_eq!(
        limits(1, 0, 1, 1),
        Err(LaneModuleReleaseErrorV1::ZeroResourceLimit(
            "max_state_bytes"
        ))
    );
    assert_eq!(
        limits(1, 1, 0, 1),
        Err(LaneModuleReleaseErrorV1::ZeroResourceLimit(
            "max_journal_bytes"
        ))
    );
    assert_eq!(
        limits(1, 1, 1, 0),
        Err(LaneModuleReleaseErrorV1::ZeroResourceLimit("max_cycles"))
    );
    assert!(limits(1, 1, 1, 1).is_ok());
    assert!(limits(u32::MAX, u32::MAX, u32::MAX, u64::MAX).is_ok());
}

#[test]
fn codec_is_exact_bounded_and_rejects_counterfeit_identity() {
    // Arrange
    let release = complete_release(LaneModuleReleaseStatusV1::ActiveNew);
    let encoded = encode_lane_module_release_v1(&release).expect("canonical encode");
    let encoded_digest: [u8; 32] = Sha256::digest(&encoded).into();
    let mut counterfeit_id = encoded.clone();
    assert_eq!(counterfeit_id[0], 1);
    counterfeit_id[1] ^= 1;
    let mut wrong_version = encoded.clone();
    wrong_version[0] = 2;
    let mut bad_status = encoded.clone();
    *bad_status.last_mut().expect("encoded release is nonempty") = 7;
    let mut trailing = encoded.clone();
    trailing.push(0);

    // Act / Assert
    assert_eq!(decode_exact_lane_module_release_v1(&encoded), Ok(release));
    assert_eq!(
        hex32(encoded_digest),
        "5dd4a6981186f18d87249585f8482ce0e889fbccb36bf823aafa26b714572c41"
    );
    assert_eq!(
        decode_exact_lane_module_release_v1(&counterfeit_id),
        Err(LaneModuleReleaseErrorV1::CounterfeitReleaseId)
    );
    assert_eq!(
        decode_exact_lane_module_release_v1(&wrong_version),
        Err(LaneModuleReleaseErrorV1::InvalidReleaseVersion(2))
    );
    assert_eq!(
        decode_exact_lane_module_release_v1(&bad_status),
        Err(LaneModuleReleaseErrorV1::PostcardDecode)
    );
    assert_eq!(
        decode_exact_lane_module_release_v1(&trailing),
        Err(LaneModuleReleaseErrorV1::TrailingBytes)
    );
    assert_eq!(
        decode_exact_lane_module_release_v1(&[]),
        Err(LaneModuleReleaseErrorV1::EmptyInput)
    );
    let oversized = vec![0; MAX_LANE_MODULE_RELEASE_BYTES_V1 + 1];
    assert_eq!(
        decode_exact_lane_module_release_v1(&oversized),
        Err(LaneModuleReleaseErrorV1::InputTooLarge {
            actual: MAX_LANE_MODULE_RELEASE_BYTES_V1 + 1,
            maximum: MAX_LANE_MODULE_RELEASE_BYTES_V1,
        })
    );
}
