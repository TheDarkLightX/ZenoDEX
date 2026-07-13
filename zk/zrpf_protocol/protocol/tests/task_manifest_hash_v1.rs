use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    ApplicationIdV3, CommitmentV3, DomainIdV3, PrivacyClaimV1, ProfileIdV3, ProgramIdV3,
    ProgramManifestInputV1, ProgramManifestV1, ProofSystemIdV1, ProofSystemVersionIdV1,
    ProofTaskInputV1, ProofTaskKindV1, ProofTaskPriorityV1, ProofTaskPrivacyPolicyV1, ProofTaskV1,
    ReceiptCodecIdV1, RedundancyPolicyV1, RewardAssetIdV1, TaskIdV3,
};

const MANIFEST_DOMAIN_V1: &[u8] = b"zenodex.zrpf.program_manifest_root.v1";
const TASK_DOMAIN_V1: &[u8] = b"zenodex.zrpf.proof_task_id.v1";

fn bytes(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new(bytes(seed)).unwrap()
}

fn proof_system(seed: u8) -> ProofSystemIdV1 {
    ProofSystemIdV1::new(bytes(seed)).unwrap()
}

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

fn optional_commitment(hasher: &mut Sha256, value: Option<CommitmentV3>) {
    match value {
        None => hasher.update([0]),
        Some(value) => {
            hasher.update([1]);
            hasher.update(value.as_bytes());
        }
    }
}

fn task_kind_tag(value: ProofTaskKindV1) -> u8 {
    match value {
        ProofTaskKindV1::Leaf => 0,
        ProofTaskKindV1::Aggregate => 1,
        ProofTaskKindV1::EpochCheckpoint => 2,
        ProofTaskKindV1::DataAvailability => 3,
    }
}

fn priority_tag(value: ProofTaskPriorityV1) -> u8 {
    match value {
        ProofTaskPriorityV1::Normal => 0,
        ProofTaskPriorityV1::Urgent => 1,
        ProofTaskPriorityV1::CriticalCheckpoint => 2,
    }
}

fn privacy_policy_tag(value: ProofTaskPrivacyPolicyV1) -> u8 {
    match value {
        ProofTaskPrivacyPolicyV1::PublicInputs => 0,
        ProofTaskPrivacyPolicyV1::PrivateWitnessAllowed => 1,
        ProofTaskPrivacyPolicyV1::PrivateWitnessRequired => 2,
    }
}

fn manual_manifest_root(input: &ProgramManifestInputV1) -> [u8; 32] {
    let mut hasher = domain_hasher(MANIFEST_DOMAIN_V1);
    hasher.update(1_u16.to_be_bytes());
    for value in [
        input.proof_system_id.as_bytes(),
        input.proof_system_version_id.as_bytes(),
        input.program_id.as_bytes(),
        input.source_tree_hash.as_bytes(),
        input.compiler_hash.as_bytes(),
    ] {
        hasher.update(value);
    }
    optional_commitment(&mut hasher, input.outer_cargo_hash);
    optional_commitment(&mut hasher, input.nested_cargo_hash);
    for value in [
        input.linker_hash,
        input.dependency_lock_hash,
        input.build_config_hash,
        input.verifier_binary_hash,
        input.verifier_policy_root,
    ] {
        hasher.update(value.as_bytes());
    }
    hasher.update(input.receipt_codec_id.as_bytes());
    hasher.update(input.security_level_bits.to_be_bytes());
    hasher.update([match input.privacy_claim {
        PrivacyClaimV1::PublicComputation => 0,
        PrivacyClaimV1::WitnessPrivate => 1,
    }]);
    match input.revocation_epoch {
        None => hasher.update([0]),
        Some(value) => {
            hasher.update([1]);
            hasher.update(value.to_be_bytes());
        }
    }
    hasher.finalize().into()
}

fn manual_task_id(input: &ProofTaskInputV1) -> [u8; 32] {
    let mut systems = input.accepted_proof_systems.clone();
    systems.sort_unstable();
    let mut hasher = domain_hasher(TASK_DOMAIN_V1);
    hasher.update(1_u16.to_be_bytes());
    hasher.update([task_kind_tag(input.task_kind)]);
    hasher.update(input.application_id.as_bytes());
    hasher.update(input.chain_or_domain_id.as_bytes());
    hasher.update(input.epoch_id.to_be_bytes());
    hasher.update([priority_tag(input.priority)]);
    hasher.update(input.proof_profile_id.as_bytes());
    hasher.update(u16::try_from(systems.len()).unwrap().to_be_bytes());
    for system in systems {
        hasher.update(system.as_bytes());
    }
    for value in [
        input.program_manifest_root,
        input.statement_hash,
        input.input_commitment_root,
        input.data_availability_root,
    ] {
        hasher.update(value.as_bytes());
    }
    match input.parent_task_id {
        None => hasher.update([0]),
        Some(value) => {
            hasher.update([1]);
            hasher.update(value.as_bytes());
        }
    }
    optional_commitment(&mut hasher, input.expected_child_task_root);
    for value in [
        input.max_input_bytes,
        input.max_cycles_or_trace_rows,
        input.max_memory_bytes,
        input.deadline_sequence,
    ] {
        hasher.update(value.to_be_bytes());
    }
    hasher.update(input.reward_asset_id.as_bytes());
    hasher.update(input.max_reward_atoms.to_be_bytes());
    hasher.update([input.redundancy_policy.required_primary_proofs()]);
    hasher.update([input.redundancy_policy.standby_provers()]);
    hasher.update([input.redundancy_policy.minimum_distinct_proof_systems()]);
    hasher.update([privacy_policy_tag(input.privacy_policy)]);
    hasher.update(input.created_sequence.to_be_bytes());
    hasher.finalize().into()
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

fn hex_32(value: &str) -> [u8; 32] {
    let mut bytes = [0; 32];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
    }
    bytes
}

#[test]
fn manifest_root_and_task_id_match_independent_fixed_preimages() {
    let input = manifest_input();
    let expected_manifest =
        hex_32("a20cb20b458c693bb53ed14a51db5ed55ac7553f2934c0753acfb59c51bda2c7");
    assert_eq!(manual_manifest_root(&input), expected_manifest);
    let manifest = ProgramManifestV1::derive(input).unwrap();
    assert_eq!(manifest.manifest_root().as_bytes(), &expected_manifest);

    let input = task_input(manifest.manifest_root());
    let expected_task = hex_32("fe3a5d92a37aec9f4d9286403679fd8811eff0393164c3d9b331245987c88ade");
    assert_eq!(manual_task_id(&input), expected_task);
    assert_eq!(
        ProofTaskV1::derive(input).unwrap().task_id().as_bytes(),
        &expected_task
    );

    let mut input = manifest_input();
    input.outer_cargo_hash = None;
    input.nested_cargo_hash = None;
    input.privacy_claim = PrivacyClaimV1::WitnessPrivate;
    input.revocation_epoch = Some(u64::MAX);
    let expected_manifest =
        hex_32("ec629c23da31ad790e3dc38138837ab9753c315861f4660b0c14fa069a227c8d");
    assert_eq!(manual_manifest_root(&input), expected_manifest);
    let manifest = ProgramManifestV1::derive(input).unwrap();
    assert_eq!(manifest.manifest_root().as_bytes(), &expected_manifest);

    let mut input = task_input(manifest.manifest_root());
    input.task_kind = ProofTaskKindV1::Aggregate;
    input.priority = ProofTaskPriorityV1::CriticalCheckpoint;
    input.parent_task_id = Some(TaskIdV3::new(bytes(40)).unwrap());
    input.expected_child_task_root = Some(commitment(41));
    input.redundancy_policy = RedundancyPolicyV1::new(2, 1, 2).unwrap();
    input.privacy_policy = ProofTaskPrivacyPolicyV1::PrivateWitnessRequired;
    let expected_task = hex_32("8414b0c77fbbe029ed69084766a3ccc09360de8640561dd79d15f64f4ce646d5");
    assert_eq!(manual_task_id(&input), expected_task);
    assert_eq!(
        ProofTaskV1::derive(input).unwrap().task_id().as_bytes(),
        &expected_task
    );
}
