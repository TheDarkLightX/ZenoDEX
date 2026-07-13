use zenodex_zrpf_protocol_v3::{
    decode_exact_program_manifest_v1, decode_exact_proof_task_v1, encode_program_manifest_v1,
    encode_proof_task_v1, ApplicationIdV3, CommitmentV3, DomainIdV3, PrivacyClaimV1, ProfileIdV3,
    ProgramIdV3, ProgramManifestInputV1, ProgramManifestV1, ProofSystemIdV1,
    ProofSystemVersionIdV1, ProofTaskInputV1, ProofTaskKindV1, ProofTaskPriorityV1,
    ProofTaskPrivacyPolicyV1, ProofTaskV1, ReceiptCodecIdV1, RedundancyPolicyV1, RewardAssetIdV1,
    TaskIdV3, TaskManifestErrorV1, MAX_ACCEPTED_PROOF_SYSTEMS_V1, MAX_PROGRAM_MANIFEST_BYTES_V1,
    MAX_PROOF_TASK_BYTES_V1, MAX_TASK_CYCLES_V1, MAX_TASK_INPUT_BYTES_V1, MAX_TASK_MEMORY_BYTES_V1,
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
        privacy_claim: PrivacyClaimV1::PublicComputation,
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
        accepted_proof_systems: vec![proof_system(31), proof_system(30)],
        program_manifest_root: manifest_root,
        statement_hash: commitment(23),
        input_commitment_root: commitment(24),
        data_availability_root: commitment(25),
        parent_task_id: None,
        expected_child_task_root: None,
        max_input_bytes: 1_048_576,
        max_cycles_or_trace_rows: 5_000_000,
        max_memory_bytes: 512 * 1024 * 1024,
        deadline_sequence: 200,
        reward_asset_id: RewardAssetIdV1::new(bytes(26)).unwrap(),
        max_reward_atoms: 1_000_000,
        redundancy_policy: RedundancyPolicyV1::new(1, 1, 1).unwrap(),
        privacy_policy: ProofTaskPrivacyPolicyV1::PublicInputs,
        created_sequence: 100,
    }
}

#[test]
fn manifests_and_tasks_round_trip_through_exact_bounded_codecs() {
    let manifest = ProgramManifestV1::derive(manifest_input()).unwrap();
    let manifest_bytes = encode_program_manifest_v1(&manifest).unwrap();
    assert_eq!(
        decode_exact_program_manifest_v1(&manifest_bytes).unwrap(),
        manifest
    );
    assert_eq!(
        manifest.receipt_codec_id(),
        ReceiptCodecIdV1::new(bytes(13)).unwrap()
    );
    assert_eq!(manifest.verifier_policy_root(), commitment(12));
    assert_eq!(manifest.privacy_claim(), PrivacyClaimV1::PublicComputation);

    let task = ProofTaskV1::derive(task_input(manifest.manifest_root())).unwrap();
    let task_bytes = encode_proof_task_v1(&task).unwrap();
    assert_eq!(decode_exact_proof_task_v1(&task_bytes).unwrap(), task);
    assert_eq!(
        task.accepted_proof_systems(),
        &[proof_system(30), proof_system(31)]
    );
    assert_eq!(
        task.proof_profile_id(),
        ProfileIdV3::new(bytes(22)).unwrap()
    );
    assert_eq!(
        task.privacy_policy(),
        ProofTaskPrivacyPolicyV1::PublicInputs
    );
}

#[test]
fn exact_codecs_reject_truncation_trailing_and_oversize() {
    let manifest = ProgramManifestV1::derive(manifest_input()).unwrap();
    let manifest_bytes = encode_program_manifest_v1(&manifest).unwrap();
    for end in 0..manifest_bytes.len() {
        assert!(decode_exact_program_manifest_v1(&manifest_bytes[..end]).is_err());
    }
    let mut trailing = manifest_bytes;
    trailing.push(0);
    assert_eq!(
        decode_exact_program_manifest_v1(&trailing),
        Err(TaskManifestErrorV1::TrailingBytes)
    );
    assert!(matches!(
        decode_exact_program_manifest_v1(&vec![0; MAX_PROGRAM_MANIFEST_BYTES_V1 + 1]),
        Err(TaskManifestErrorV1::InputTooLarge { .. })
    ));

    let task = ProofTaskV1::derive(task_input(manifest.manifest_root())).unwrap();
    let task_bytes = encode_proof_task_v1(&task).unwrap();
    for end in 0..task_bytes.len() {
        assert!(decode_exact_proof_task_v1(&task_bytes[..end]).is_err());
    }
    let mut trailing = task_bytes;
    trailing.push(0);
    assert_eq!(
        decode_exact_proof_task_v1(&trailing),
        Err(TaskManifestErrorV1::TrailingBytes)
    );
    assert!(matches!(
        decode_exact_proof_task_v1(&vec![0; MAX_PROOF_TASK_BYTES_V1 + 1]),
        Err(TaskManifestErrorV1::InputTooLarge { .. })
    ));
}

#[test]
fn derived_roots_reject_json_substitution_and_unknown_fields() {
    let manifest = ProgramManifestV1::derive(manifest_input()).unwrap();
    let mut manifest_json = serde_json::to_value(&manifest).unwrap();
    manifest_json["manifest_root"] = serde_json::to_value(commitment(99)).unwrap();
    assert!(serde_json::from_value::<ProgramManifestV1>(manifest_json).is_err());

    let mut stale_manifest = serde_json::to_value(&manifest).unwrap();
    stale_manifest["manifest_version"] = serde_json::json!(2);
    assert!(serde_json::from_value::<ProgramManifestV1>(stale_manifest).is_err());

    let mut unknown_manifest = serde_json::to_value(&manifest).unwrap();
    unknown_manifest["operator_note"] = serde_json::json!(true);
    assert!(serde_json::from_value::<ProgramManifestV1>(unknown_manifest).is_err());

    let task = ProofTaskV1::derive(task_input(manifest.manifest_root())).unwrap();
    let mut task_json = serde_json::to_value(&task).unwrap();
    task_json["task_id"] = serde_json::to_value(TaskIdV3::new(bytes(98)).unwrap()).unwrap();
    assert!(serde_json::from_value::<ProofTaskV1>(task_json).is_err());

    let mut stale_task = serde_json::to_value(&task).unwrap();
    stale_task["task_version"] = serde_json::json!(2);
    assert!(serde_json::from_value::<ProofTaskV1>(stale_task).is_err());

    let mut unknown = serde_json::to_value(&task).unwrap();
    unknown["publisher_note"] = serde_json::json!(true);
    assert!(serde_json::from_value::<ProofTaskV1>(unknown).is_err());
}

#[test]
fn proof_system_set_is_canonical_and_bounded() {
    let manifest = ProgramManifestV1::derive(manifest_input()).unwrap();
    let mut duplicate = task_input(manifest.manifest_root());
    duplicate.accepted_proof_systems = vec![proof_system(1), proof_system(1)];
    assert_eq!(
        ProofTaskV1::derive(duplicate),
        Err(TaskManifestErrorV1::DuplicateProofSystem)
    );

    let mut oversized = task_input(manifest.manifest_root());
    oversized.accepted_proof_systems = (1..=MAX_ACCEPTED_PROOF_SYSTEMS_V1 + 1)
        .map(|value| proof_system(u8::try_from(value).unwrap()))
        .collect();
    assert!(matches!(
        ProofTaskV1::derive(oversized),
        Err(TaskManifestErrorV1::TooManyProofSystems { .. })
    ));

    let mut maximum = task_input(manifest.manifest_root());
    maximum.accepted_proof_systems = (1..=MAX_ACCEPTED_PROOF_SYSTEMS_V1)
        .map(|value| proof_system(u8::try_from(value).unwrap()))
        .collect();
    assert!(ProofTaskV1::derive(maximum).is_ok());

    let task = ProofTaskV1::derive(task_input(manifest.manifest_root())).unwrap();
    let mut oversized_json = serde_json::to_value(&task).unwrap();
    oversized_json["accepted_proof_systems"] = serde_json::json!((1
        ..=MAX_ACCEPTED_PROOF_SYSTEMS_V1 + 1)
        .map(|value| bytes(u8::try_from(value).unwrap()))
        .collect::<Vec<_>>());
    assert!(serde_json::from_value::<ProofTaskV1>(oversized_json).is_err());

    let mut unsorted_json = serde_json::to_value(task).unwrap();
    unsorted_json["accepted_proof_systems"] = serde_json::json!([bytes(31), bytes(30)]);
    assert!(serde_json::from_value::<ProofTaskV1>(unsorted_json).is_err());
}

#[test]
fn aggregate_child_binding_is_mandatory_and_leaf_binding_is_forbidden() {
    let manifest = ProgramManifestV1::derive(manifest_input()).unwrap();
    let mut aggregate = task_input(manifest.manifest_root());
    aggregate.task_kind = ProofTaskKindV1::Aggregate;
    assert_eq!(
        ProofTaskV1::derive(aggregate.clone()),
        Err(TaskManifestErrorV1::InvalidChildBinding)
    );
    aggregate.expected_child_task_root = Some(commitment(60));
    assert!(ProofTaskV1::derive(aggregate).is_ok());

    let mut leaf = task_input(manifest.manifest_root());
    leaf.expected_child_task_root = Some(commitment(61));
    assert_eq!(
        ProofTaskV1::derive(leaf),
        Err(TaskManifestErrorV1::InvalidChildBinding)
    );
}

#[test]
fn resources_deadline_reward_and_redundancy_fail_closed() {
    let manifest = ProgramManifestV1::derive(manifest_input()).unwrap();
    let mut zero = task_input(manifest.manifest_root());
    zero.max_input_bytes = 0;
    assert!(matches!(
        ProofTaskV1::derive(zero),
        Err(TaskManifestErrorV1::InvalidResourceBound("max_input_bytes"))
    ));

    let mut high = task_input(manifest.manifest_root());
    high.max_input_bytes = MAX_TASK_INPUT_BYTES_V1 + 1;
    assert!(ProofTaskV1::derive(high).is_err());

    let mut high = task_input(manifest.manifest_root());
    high.max_cycles_or_trace_rows = MAX_TASK_CYCLES_V1 + 1;
    assert!(ProofTaskV1::derive(high).is_err());

    let mut high = task_input(manifest.manifest_root());
    high.max_memory_bytes = MAX_TASK_MEMORY_BYTES_V1 + 1;
    assert!(ProofTaskV1::derive(high).is_err());

    let mut zero_reward = task_input(manifest.manifest_root());
    zero_reward.max_reward_atoms = 0;
    assert!(ProofTaskV1::derive(zero_reward).is_err());

    let mut deadline = task_input(manifest.manifest_root());
    deadline.deadline_sequence = deadline.created_sequence;
    assert_eq!(
        ProofTaskV1::derive(deadline),
        Err(TaskManifestErrorV1::InvalidDeadline)
    );

    assert_eq!(
        RedundancyPolicyV1::new(0, 0, 1),
        Err(TaskManifestErrorV1::InvalidRedundancy)
    );
    let mut excessive_diversity = task_input(manifest.manifest_root());
    excessive_diversity.redundancy_policy = RedundancyPolicyV1::new(1, 1, 3).unwrap();
    assert_eq!(
        ProofTaskV1::derive(excessive_diversity),
        Err(TaskManifestErrorV1::InvalidRedundancy)
    );
}

#[test]
fn epoch_statement_reward_and_creation_fields_separate_task_identity() {
    let manifest = ProgramManifestV1::derive(manifest_input()).unwrap();
    let baseline = task_input(manifest.manifest_root());
    let expected = ProofTaskV1::derive(baseline.clone()).unwrap().task_id();
    let variants = [
        {
            let mut value = baseline.clone();
            value.epoch_id += 1;
            value
        },
        {
            let mut value = baseline.clone();
            value.statement_hash = commitment(70);
            value
        },
        {
            let mut value = baseline.clone();
            value.max_reward_atoms += 1;
            value
        },
        {
            let mut value = baseline.clone();
            value.created_sequence += 1;
            value
        },
    ];
    for variant in variants {
        assert_ne!(ProofTaskV1::derive(variant).unwrap().task_id(), expected);
    }
}

#[test]
fn manifest_security_bound_rejects_and_revocation_uses_full_u64_domain() {
    let mut zero = manifest_input();
    zero.security_level_bits = 0;
    assert_eq!(
        ProgramManifestV1::derive(zero),
        Err(TaskManifestErrorV1::InvalidSecurityLevel)
    );
    let mut excessive = manifest_input();
    excessive.security_level_bits = 513;
    assert_eq!(
        ProgramManifestV1::derive(excessive),
        Err(TaskManifestErrorV1::InvalidSecurityLevel)
    );
    let mut revoked_at_genesis = manifest_input();
    revoked_at_genesis.revocation_epoch = Some(0);
    assert!(ProgramManifestV1::derive(revoked_at_genesis).is_ok());
}
