use zenodex_zrpf_protocol_v3::{
    evaluate_proof_assignment_compatibility_v1, ApplicationIdV3, CommitmentV3,
    CompatibleProofAssignmentV1, DomainIdV3, PrivacyClaimV1, ProfileIdV3, ProgramIdV3,
    ProgramManifestInputV1, ProgramManifestV1, ProofAssignmentCompatibilityVerdictV1,
    ProofAssignmentPendingV1, ProofAssignmentPolicyInputV1, ProofAssignmentPolicyV1,
    ProofAssignmentRejectV1, ProofAssignmentResourceV1, ProofSystemIdV1, ProofSystemVersionIdV1,
    ProofTaskInputV1, ProofTaskKindV1, ProofTaskPriorityV1, ProofTaskPrivacyPolicyV1, ProofTaskV1,
    ReceiptCodecIdV1, RedundancyPolicyV1, RewardAssetIdV1,
};

fn bytes(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new(bytes(seed)).unwrap()
}

fn proof_system(seed: u8) -> ProofSystemIdV1 {
    ProofSystemIdV1::new(bytes(seed)).unwrap()
}

fn manifest_input() -> ProgramManifestInputV1 {
    ProgramManifestInputV1 {
        proof_system_id: proof_system(1),
        proof_system_version_id: ProofSystemVersionIdV1::new(bytes(2)).unwrap(),
        program_id: ProgramIdV3::new(bytes(3)).unwrap(),
        source_tree_hash: commitment(4),
        compiler_hash: commitment(5),
        outer_cargo_hash: Some(commitment(6)),
        nested_cargo_hash: Some(commitment(7)),
        linker_hash: commitment(8),
        dependency_lock_hash: commitment(9),
        build_config_hash: commitment(10),
        verifier_binary_hash: commitment(11),
        verifier_policy_root: commitment(12),
        receipt_codec_id: ReceiptCodecIdV1::new(bytes(13)).unwrap(),
        security_level_bits: 128,
        privacy_claim: PrivacyClaimV1::WitnessPrivate,
        revocation_epoch: None,
    }
}

fn task_input(manifest_root: CommitmentV3) -> ProofTaskInputV1 {
    ProofTaskInputV1 {
        task_kind: ProofTaskKindV1::Leaf,
        application_id: ApplicationIdV3::new(bytes(20)).unwrap(),
        chain_or_domain_id: DomainIdV3::new(bytes(21)).unwrap(),
        epoch_id: 7,
        priority: ProofTaskPriorityV1::Normal,
        proof_profile_id: ProfileIdV3::new(bytes(22)).unwrap(),
        accepted_proof_systems: vec![proof_system(1), proof_system(2)],
        program_manifest_root: manifest_root,
        statement_hash: commitment(23),
        input_commitment_root: commitment(24),
        data_availability_root: commitment(25),
        parent_task_id: None,
        expected_child_task_root: None,
        max_input_bytes: 1_024,
        max_cycles_or_trace_rows: 2_048,
        max_memory_bytes: 4_096,
        deadline_sequence: 200,
        reward_asset_id: RewardAssetIdV1::new(bytes(26)).unwrap(),
        max_reward_atoms: 1_000_000,
        redundancy_policy: RedundancyPolicyV1::new(1, 1, 1).unwrap(),
        privacy_policy: ProofTaskPrivacyPolicyV1::PrivateWitnessRequired,
        created_sequence: 100,
    }
}

fn policy_input(manifest_root: CommitmentV3) -> ProofAssignmentPolicyInputV1 {
    ProofAssignmentPolicyInputV1 {
        authorized_program_manifest_root: manifest_root,
        required_proof_profile_id: ProfileIdV3::new(bytes(22)).unwrap(),
        required_receipt_codec_id: ReceiptCodecIdV1::new(bytes(13)).unwrap(),
        required_verifier_policy_root: commitment(12),
        minimum_security_level_bits: 128,
        valid_from_epoch: 90,
        valid_through_epoch: 110,
        max_input_bytes: 1_024,
        max_cycles_or_trace_rows: 2_048,
        max_memory_bytes: 4_096,
    }
}

fn verdict(
    manifest_input: ProgramManifestInputV1,
    mutate_task: impl FnOnce(&mut ProofTaskInputV1),
    mutate_policy: impl FnOnce(&mut ProofAssignmentPolicyInputV1),
    assignment_epoch: u64,
) -> ProofAssignmentCompatibilityVerdictV1 {
    let manifest = ProgramManifestV1::derive(manifest_input).unwrap();
    let mut task_input = task_input(manifest.manifest_root());
    mutate_task(&mut task_input);
    let task = ProofTaskV1::derive(task_input).unwrap();
    let mut policy_input = policy_input(manifest.manifest_root());
    mutate_policy(&mut policy_input);
    let policy = ProofAssignmentPolicyV1::new(policy_input).unwrap();
    evaluate_proof_assignment_compatibility_v1(&task, &manifest, &policy, assignment_epoch)
}

fn compatible(value: ProofAssignmentCompatibilityVerdictV1) -> CompatibleProofAssignmentV1 {
    match value {
        ProofAssignmentCompatibilityVerdictV1::Compatible(value) => value,
        other => panic!("expected compatible verdict, got {other:?}"),
    }
}

#[test]
fn compatible_assignment_binds_exact_checked_identities_without_authority() {
    let value = compatible(verdict(manifest_input(), |_| {}, |_| {}, 100));
    let expected_task = ProofTaskV1::derive(task_input(commitment_from_manifest())).unwrap();

    assert_eq!(value.task_id(), expected_task.task_id());
    assert_eq!(value.program_manifest_root(), commitment_from_manifest());
    assert_eq!(value.selected_proof_system_id(), proof_system(1));
    assert_eq!(
        value.proof_profile_id(),
        ProfileIdV3::new(bytes(22)).unwrap()
    );
    assert_eq!(
        value.receipt_codec_id(),
        ReceiptCodecIdV1::new(bytes(13)).unwrap()
    );
    assert_eq!(value.verifier_policy_root(), commitment(12));
    assert_eq!(value.assignment_epoch(), 100);
}

fn commitment_from_manifest() -> CommitmentV3 {
    ProgramManifestV1::derive(manifest_input())
        .unwrap()
        .manifest_root()
}

#[test]
fn root_and_profile_mutations_reject_at_the_owned_boundary() {
    assert_eq!(
        verdict(
            manifest_input(),
            |task| task.program_manifest_root = commitment(80),
            |_| {},
            100
        ),
        ProofAssignmentCompatibilityVerdictV1::Rejected(
            ProofAssignmentRejectV1::TaskManifestRootMismatch
        )
    );
    assert_eq!(
        verdict(
            manifest_input(),
            |_| {},
            |policy| policy.authorized_program_manifest_root = commitment(81),
            100
        ),
        ProofAssignmentCompatibilityVerdictV1::Rejected(
            ProofAssignmentRejectV1::ManifestRootNotAuthorized
        )
    );
    assert_eq!(
        verdict(
            manifest_input(),
            |task| task.proof_profile_id = ProfileIdV3::new(bytes(82)).unwrap(),
            |_| {},
            100
        ),
        ProofAssignmentCompatibilityVerdictV1::Rejected(
            ProofAssignmentRejectV1::ProofProfileMismatch
        )
    );
}

#[test]
fn codec_policy_root_and_system_mutations_reject_at_the_owned_boundary() {
    let mut codec = manifest_input();
    codec.receipt_codec_id = ReceiptCodecIdV1::new(bytes(83)).unwrap();
    assert_eq!(
        verdict(codec, |_| {}, |_| {}, 100),
        ProofAssignmentCompatibilityVerdictV1::Rejected(
            ProofAssignmentRejectV1::ReceiptCodecMismatch
        )
    );

    let mut policy_root = manifest_input();
    policy_root.verifier_policy_root = commitment(84);
    assert_eq!(
        verdict(policy_root, |_| {}, |_| {}, 100),
        ProofAssignmentCompatibilityVerdictV1::Rejected(
            ProofAssignmentRejectV1::VerifierPolicyRootMismatch
        )
    );

    let mut unsupported = manifest_input();
    unsupported.proof_system_id = proof_system(85);
    assert_eq!(
        verdict(unsupported, |_| {}, |_| {}, 100),
        ProofAssignmentCompatibilityVerdictV1::Rejected(
            ProofAssignmentRejectV1::UnsupportedProofSystem
        )
    );
}

#[test]
fn multiple_failures_follow_documented_first_reject_precedence() {
    let mut unsupported = manifest_input();
    unsupported.proof_system_id = proof_system(86);
    assert_eq!(
        verdict(
            unsupported.clone(),
            |task| task.program_manifest_root = commitment(87),
            |policy| policy.authorized_program_manifest_root = commitment(88),
            100,
        ),
        ProofAssignmentCompatibilityVerdictV1::Rejected(
            ProofAssignmentRejectV1::TaskManifestRootMismatch
        )
    );
    assert_eq!(
        verdict(
            unsupported,
            |_| {},
            |policy| policy.authorized_program_manifest_root = commitment(88),
            100,
        ),
        ProofAssignmentCompatibilityVerdictV1::Rejected(
            ProofAssignmentRejectV1::ManifestRootNotAuthorized
        )
    );
}

#[test]
fn declared_security_downgrade_and_private_witness_downgrade_reject() {
    let mut downgraded = manifest_input();
    downgraded.security_level_bits = 127;
    assert_eq!(
        verdict(downgraded, |_| {}, |_| {}, 100),
        ProofAssignmentCompatibilityVerdictV1::Rejected(
            ProofAssignmentRejectV1::SecurityLevelBelowMinimum
        )
    );

    let mut public = manifest_input();
    public.privacy_claim = PrivacyClaimV1::PublicComputation;
    assert_eq!(
        verdict(public.clone(), |_| {}, |_| {}, 100),
        ProofAssignmentCompatibilityVerdictV1::Rejected(ProofAssignmentRejectV1::PrivacyDowngrade)
    );
    compatible(verdict(
        public.clone(),
        |task| task.privacy_policy = ProofTaskPrivacyPolicyV1::PrivateWitnessAllowed,
        |_| {},
        100,
    ));
    compatible(verdict(
        manifest_input(),
        |task| task.privacy_policy = ProofTaskPrivacyPolicyV1::PrivateWitnessAllowed,
        |_| {},
        100,
    ));
    compatible(verdict(
        public,
        |task| task.privacy_policy = ProofTaskPrivacyPolicyV1::PublicInputs,
        |_| {},
        100,
    ));
    compatible(verdict(
        manifest_input(),
        |task| task.privacy_policy = ProofTaskPrivacyPolicyV1::PublicInputs,
        |_| {},
        100,
    ));
}

#[test]
fn policy_validity_and_manifest_revocation_boundaries_fail_closed() {
    assert_eq!(
        verdict(manifest_input(), |_| {}, |_| {}, 89),
        ProofAssignmentCompatibilityVerdictV1::Rejected(ProofAssignmentRejectV1::PolicyNotYetValid)
    );
    compatible(verdict(manifest_input(), |_| {}, |_| {}, 90));
    compatible(verdict(manifest_input(), |_| {}, |_| {}, 110));
    assert_eq!(
        verdict(manifest_input(), |_| {}, |_| {}, 111),
        ProofAssignmentCompatibilityVerdictV1::Rejected(ProofAssignmentRejectV1::PolicyExpired)
    );

    let mut revoked = manifest_input();
    revoked.revocation_epoch = Some(100);
    compatible(verdict(revoked.clone(), |_| {}, |_| {}, 99));
    for assignment_epoch in [100, 101] {
        assert_eq!(
            verdict(revoked.clone(), |_| {}, |_| {}, assignment_epoch),
            ProofAssignmentCompatibilityVerdictV1::Rejected(
                ProofAssignmentRejectV1::ManifestRevoked
            )
        );
    }
}

#[test]
fn each_task_resource_ceiling_is_checked_independently() {
    for (verdict, resource) in [
        (
            verdict(
                manifest_input(),
                |task| task.max_input_bytes += 1,
                |_| {},
                100,
            ),
            ProofAssignmentResourceV1::InputBytes,
        ),
        (
            verdict(
                manifest_input(),
                |task| task.max_cycles_or_trace_rows += 1,
                |_| {},
                100,
            ),
            ProofAssignmentResourceV1::CyclesOrTraceRows,
        ),
        (
            verdict(
                manifest_input(),
                |task| task.max_memory_bytes += 1,
                |_| {},
                100,
            ),
            ProofAssignmentResourceV1::MemoryBytes,
        ),
    ] {
        assert_eq!(
            verdict,
            ProofAssignmentCompatibilityVerdictV1::Rejected(
                ProofAssignmentRejectV1::ResourceCeilingExceeded(resource)
            )
        );
    }
}

#[test]
fn impossible_redundancy_rejects_and_standby_diversity_remains_pending() {
    let impossible = verdict(
        manifest_input(),
        |task| {
            task.accepted_proof_systems.push(proof_system(3));
            task.redundancy_policy = RedundancyPolicyV1::new(1, 1, 3).unwrap();
        },
        |_| {},
        100,
    );
    assert_eq!(
        impossible,
        ProofAssignmentCompatibilityVerdictV1::Rejected(
            ProofAssignmentRejectV1::ImpossibleRedundancy
        )
    );

    let pending = verdict(
        manifest_input(),
        |task| task.redundancy_policy = RedundancyPolicyV1::new(1, 1, 2).unwrap(),
        |_| {},
        100,
    );
    assert_eq!(
        pending,
        ProofAssignmentCompatibilityVerdictV1::Pending(
            ProofAssignmentPendingV1::StandbyDiversitySemantics
        )
    );

    compatible(verdict(
        manifest_input(),
        |task| task.redundancy_policy = RedundancyPolicyV1::new(2, 0, 2).unwrap(),
        |_| {},
        100,
    ));
}
