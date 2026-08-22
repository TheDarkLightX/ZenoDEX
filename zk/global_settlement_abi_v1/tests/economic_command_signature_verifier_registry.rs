use zenodex_global_settlement_abi_v1::*;

const ALGORITHM: &str = "BLS12_381_G2_BASIC_V1";
const COMMAND: &str = "asset_transfer";

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).unwrap()
}

fn active_evidence() -> Vec<CommandSignatureVerifierEvidenceStatusV1> {
    vec![
        CommandSignatureVerifierEvidenceStatusV1::DEPLOYMENT_BOUND,
        CommandSignatureVerifierEvidenceStatusV1::IMPLEMENTATION_REPLAYED,
        CommandSignatureVerifierEvidenceStatusV1::IMPLEMENTED,
        CommandSignatureVerifierEvidenceStatusV1::INDEPENDENTLY_REVIEWED,
        CommandSignatureVerifierEvidenceStatusV1::NO_BYPASS,
        CommandSignatureVerifierEvidenceStatusV1::RELEASE_BACKED,
        CommandSignatureVerifierEvidenceStatusV1::SOURCE_PINNED,
        CommandSignatureVerifierEvidenceStatusV1::SPECIFIED,
        CommandSignatureVerifierEvidenceStatusV1::TESTED,
        CommandSignatureVerifierEvidenceStatusV1::TOOLCHAIN_PINNED,
    ]
}

fn release(
    implementation_root: RootV1,
    status: ReleaseStatusV1,
    accepts_new_authentications: bool,
) -> EconomicCommandSignatureVerifierReleaseV1 {
    release_for_algorithm(
        ALGORITHM,
        implementation_root,
        status,
        accepts_new_authentications,
    )
}

fn release_for_algorithm(
    signature_algorithm: &str,
    implementation_root: RootV1,
    status: ReleaseStatusV1,
    accepts_new_authentications: bool,
) -> EconomicCommandSignatureVerifierReleaseV1 {
    let mut release = EconomicCommandSignatureVerifierReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        release_id: root(99),
        semantic_version: "1.0.0-test".to_owned(),
        signature_algorithm: signature_algorithm.to_owned(),
        implementation_root,
        public_key_schema_root: root(2),
        signature_schema_root: root(3),
        message_schema_root: root(4),
        specification_root: root(5),
        source_root: root(6),
        toolchain_root: root(7),
        evidence_manifest_root: root(8),
        max_public_key_bytes: 32,
        max_signature_bytes: 16,
        status,
        accepts_new_authentications,
        evidence_statuses: if accepts_new_authentications {
            active_evidence()
        } else {
            vec![]
        },
    };
    release.release_id = release.derived_release_id().unwrap();
    release.validate().unwrap();
    release
}

fn registry(
    releases: Vec<EconomicCommandSignatureVerifierReleaseV1>,
) -> EconomicCommandSignatureVerifierRegistryV1 {
    EconomicCommandSignatureVerifierRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases,
    }
}

fn policy(registry: &EconomicCommandSignatureVerifierRegistryV1) -> EconomicPolicyRegistryV1 {
    EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![EconomicPolicyBindingV1 {
            policy_kind: ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1.to_owned(),
            command_kind: COMMAND.to_owned(),
            policy_root: registry.registry_root().unwrap(),
        }],
    }
}

fn select<'a>(
    registry: &'a EconomicCommandSignatureVerifierRegistryV1,
    signature: &[u8],
) -> AbiResultV1<&'a EconomicCommandSignatureVerifierReleaseV1> {
    select_profile_governed_command_signature_verifier_release_v1(
        &policy(registry),
        registry,
        COMMAND,
        ALGORITHM,
        "test-public-key",
        signature,
    )
}

#[test]
fn release_and_registry_roots_match_cross_language_golden() {
    let release = release(root(1), ReleaseStatusV1::ACTIVE_NEW, true);
    let registry = registry(vec![release.clone()]);

    assert_eq!(
        release.release_id.as_str(),
        "0x01368bcd29677a41ffe2248a74ea2fce6ab490d898d72866c772fc9b2d8f440e"
    );
    assert_eq!(
        registry.registry_root().unwrap().as_str(),
        "0x101888ac655b02e227e77b9fdf020f6f968b1a9a55793f139e11964731277051"
    );
}

#[test]
fn signature_ceiling_uses_closed_boundary_bva() {
    let registry = registry(vec![release(root(1), ReleaseStatusV1::ACTIVE_NEW, true)]);
    assert!(select(&registry, &[0; 15]).is_ok());
    assert!(select(&registry, &[0; 16]).is_ok());
    assert!(matches!(
        select(&registry, &[0; 17]),
        Err(AbiErrorV1::InvalidBounds(
            "command signature release ceiling"
        ))
    ));
}

#[test]
fn public_key_ceiling_uses_utf8_byte_boundary_bva() {
    let registry = registry(vec![release(root(1), ReleaseStatusV1::ACTIVE_NEW, true)]);
    assert!(
        select_profile_governed_command_signature_verifier_release_v1(
            &policy(&registry),
            &registry,
            COMMAND,
            ALGORITHM,
            &"k".repeat(31),
            b"signature",
        )
        .is_ok()
    );
    assert!(
        select_profile_governed_command_signature_verifier_release_v1(
            &policy(&registry),
            &registry,
            COMMAND,
            ALGORITHM,
            &"k".repeat(32),
            b"signature",
        )
        .is_ok()
    );
    assert!(matches!(
        select_profile_governed_command_signature_verifier_release_v1(
            &policy(&registry),
            &registry,
            COMMAND,
            ALGORITHM,
            &"k".repeat(33),
            b"signature",
        ),
        Err(AbiErrorV1::InvalidBounds(
            "command signature public key release ceiling"
        ))
    ));
    for (utf8_key, expected_bytes, accepted) in [
        (format!("{}a", "é".repeat(15)), 31, true),
        ("é".repeat(16), 32, true),
        (format!("{}a", "é".repeat(16)), 33, false),
    ] {
        assert_eq!(utf8_key.len(), expected_bytes);
        assert_eq!(
            select_profile_governed_command_signature_verifier_release_v1(
                &policy(&registry),
                &registry,
                COMMAND,
                ALGORITHM,
                &utf8_key,
                b"signature",
            )
            .is_ok(),
            accepted
        );
    }
}

#[test]
fn registry_release_count_uses_closed_boundary_bva() {
    assert!(matches!(
        registry(vec![]).validate(),
        Err(AbiErrorV1::InvalidBounds(
            "command signature verifier registry"
        ))
    ));
    let releases = |count: u64| {
        let mut releases = (0..count)
            .map(|index| {
                release_for_algorithm(
                    &format!("TEST_SIGNATURE_ALGORITHM_{index:02}_V1"),
                    root(100 + index),
                    ReleaseStatusV1::ACTIVE_NEW,
                    true,
                )
            })
            .collect::<Vec<_>>();
        releases.sort_by(|left, right| {
            (&left.signature_algorithm, &left.release_id)
                .cmp(&(&right.signature_algorithm, &right.release_id))
        });
        releases
    };
    for accepted_count in [1, 31, 32] {
        assert!(registry(releases(accepted_count)).validate().is_ok());
    }
    assert!(matches!(
        registry(releases(33)).validate(),
        Err(AbiErrorV1::InvalidBounds(
            "command signature verifier registry"
        ))
    ));
}

#[test]
fn wrong_policy_root_rejects_before_release_selection() {
    let registry = registry(vec![release(root(1), ReleaseStatusV1::ACTIVE_NEW, true)]);
    let wrong_policy = EconomicPolicyRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        bindings: vec![EconomicPolicyBindingV1 {
            policy_kind: ECONOMIC_COMMAND_SIGNATURE_VERIFIER_POLICY_KIND_V1.to_owned(),
            command_kind: COMMAND.to_owned(),
            policy_root: root(999),
        }],
    };

    assert!(matches!(
        select_profile_governed_command_signature_verifier_release_v1(
            &wrong_policy,
            &registry,
            COMMAND,
            ALGORITHM,
            "test-public-key",
            b"signature",
        ),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier registry profile governance"
        ))
    ));
}

#[test]
fn rotation_selects_active_and_rejects_two_active_releases() {
    let old = release(root(8), ReleaseStatusV1::VERIFY_ONLY, false);
    let active = release(root(1), ReleaseStatusV1::ACTIVE_NEW, true);
    let mut releases = vec![old, active.clone()];
    releases.sort_by(|left, right| {
        (&left.signature_algorithm, &left.release_id)
            .cmp(&(&right.signature_algorithm, &right.release_id))
    });
    assert_eq!(select(&registry(releases), b"signature").unwrap(), &active);

    let mut active_releases = vec![
        release(root(1), ReleaseStatusV1::ACTIVE_NEW, true),
        release(root(8), ReleaseStatusV1::ACTIVE_NEW, true),
    ];
    active_releases.sort_by(|left, right| {
        (&left.signature_algorithm, &left.release_id)
            .cmp(&(&right.signature_algorithm, &right.release_id))
    });
    assert!(matches!(
        select(&registry(active_releases), b"signature"),
        Err(AbiErrorV1::InvalidBinding(
            "command signature algorithm has multiple active verifier releases"
        ))
    ));
}

#[test]
fn zero_active_releases_for_algorithm_fail_closed() {
    let verify_only = release(root(1), ReleaseStatusV1::VERIFY_ONLY, false);
    assert!(matches!(
        select(&registry(vec![verify_only]), b"signature"),
        Err(AbiErrorV1::InvalidBinding(
            "command signature algorithm has no active verifier release"
        ))
    ));
}

#[test]
fn lifecycle_evidence_and_content_id_mutations_fail_closed() {
    let release = release(root(1), ReleaseStatusV1::ACTIVE_NEW, true);

    let mut inactive_flag = release.clone();
    inactive_flag.accepts_new_authentications = false;
    assert!(matches!(
        inactive_flag.validate(),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier active status"
        ))
    ));

    let mut missing_evidence = release.clone();
    missing_evidence.evidence_statuses.clear();
    assert!(matches!(
        missing_evidence.validate(),
        Err(AbiErrorV1::InvalidBinding(
            "active command signature verifier evidence"
        ))
    ));

    let mut duplicate_evidence = release.clone();
    duplicate_evidence
        .evidence_statuses
        .push(CommandSignatureVerifierEvidenceStatusV1::TOOLCHAIN_PINNED);
    assert!(matches!(
        duplicate_evidence.validate(),
        Err(AbiErrorV1::InvalidOrder(
            "command signature verifier evidence statuses"
        ))
    ));

    let mut unsorted_evidence = release.clone();
    unsorted_evidence.evidence_statuses.reverse();
    assert!(matches!(
        unsorted_evidence.validate(),
        Err(AbiErrorV1::InvalidOrder(
            "command signature verifier evidence statuses"
        ))
    ));

    let mut mutated_content = release.clone();
    mutated_content.implementation_root = root(999);
    assert!(matches!(
        mutated_content.validate(),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier content-derived release id"
        ))
    ));

    let mut mutated_manifest = release;
    mutated_manifest.evidence_manifest_root = root(998);
    assert!(matches!(
        mutated_manifest.validate(),
        Err(AbiErrorV1::InvalidBinding(
            "command signature verifier content-derived release id"
        ))
    ));
}

#[test]
fn configured_ceilings_use_zero_one_maximum_neighbor_bva() {
    let max_public_key_bytes = u64::try_from(MAX_TOKEN_BYTES_V1).unwrap();
    let max_signature_bytes = u64::try_from(MAX_COMMAND_SIGNATURE_BYTES_V1).unwrap();
    for (public_key_ceiling, signature_ceiling, accepted) in [
        (0, 16, false),
        (1, 16, true),
        (max_public_key_bytes, 16, true),
        (max_public_key_bytes + 1, 16, false),
        (32, 0, false),
        (32, 1, true),
        (32, max_signature_bytes, true),
        (32, max_signature_bytes + 1, false),
    ] {
        let mut candidate = release(root(1), ReleaseStatusV1::ACTIVE_NEW, true);
        candidate.max_public_key_bytes = public_key_ceiling;
        candidate.max_signature_bytes = signature_ceiling;
        candidate.release_id = candidate.derived_release_id().unwrap();
        assert_eq!(candidate.validate().is_ok(), accepted);
    }
}
