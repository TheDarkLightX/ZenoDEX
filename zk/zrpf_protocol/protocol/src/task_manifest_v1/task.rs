use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::Digest;

use super::base::{
    deserialize_bounded_proof_systems, ProofSystemIdV1, ProofTaskKindV1, ProofTaskPriorityV1,
    ProofTaskPrivacyPolicyV1, RedundancyPolicyV1, RewardAssetIdV1, TaskManifestErrorV1,
    MAX_ACCEPTED_PROOF_SYSTEMS_V1, MAX_TASK_CYCLES_V1, MAX_TASK_INPUT_BYTES_V1,
    MAX_TASK_MEMORY_BYTES_V1, PROOF_TASK_VERSION_V1,
};
use super::hash::{
    domain_hasher, priority_tag, privacy_policy_tag, task_kind_tag, write_optional_commitment,
    write_optional_task,
};
use crate::{ApplicationIdV3, CommitmentV3, DomainIdV3, ProfileIdV3, TaskIdV3};

const PROOF_TASK_ID_DOMAIN_V1: &[u8] = b"zenodex.zrpf.proof_task_id.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofTaskInputV1 {
    pub task_kind: ProofTaskKindV1,
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub epoch_id: u64,
    pub priority: ProofTaskPriorityV1,
    pub proof_profile_id: ProfileIdV3,
    pub accepted_proof_systems: Vec<ProofSystemIdV1>,
    pub program_manifest_root: CommitmentV3,
    pub statement_hash: CommitmentV3,
    pub input_commitment_root: CommitmentV3,
    pub data_availability_root: CommitmentV3,
    pub parent_task_id: Option<TaskIdV3>,
    pub expected_child_task_root: Option<CommitmentV3>,
    pub max_input_bytes: u64,
    pub max_cycles_or_trace_rows: u64,
    pub max_memory_bytes: u64,
    pub deadline_sequence: u64,
    pub reward_asset_id: RewardAssetIdV1,
    pub max_reward_atoms: u128,
    pub redundancy_policy: RedundancyPolicyV1,
    pub privacy_policy: ProofTaskPrivacyPolicyV1,
    pub created_sequence: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProofTaskV1 {
    task_version: u16,
    task_id: TaskIdV3,
    task_kind: ProofTaskKindV1,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    priority: ProofTaskPriorityV1,
    proof_profile_id: ProfileIdV3,
    accepted_proof_systems: Vec<ProofSystemIdV1>,
    program_manifest_root: CommitmentV3,
    statement_hash: CommitmentV3,
    input_commitment_root: CommitmentV3,
    data_availability_root: CommitmentV3,
    parent_task_id: Option<TaskIdV3>,
    expected_child_task_root: Option<CommitmentV3>,
    max_input_bytes: u64,
    max_cycles_or_trace_rows: u64,
    max_memory_bytes: u64,
    deadline_sequence: u64,
    reward_asset_id: RewardAssetIdV1,
    max_reward_atoms: u128,
    redundancy_policy: RedundancyPolicyV1,
    privacy_policy: ProofTaskPrivacyPolicyV1,
    created_sequence: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofTaskWireV1 {
    task_version: u16,
    task_id: TaskIdV3,
    task_kind: ProofTaskKindV1,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    priority: ProofTaskPriorityV1,
    proof_profile_id: ProfileIdV3,
    #[serde(deserialize_with = "deserialize_bounded_proof_systems")]
    accepted_proof_systems: Vec<ProofSystemIdV1>,
    program_manifest_root: CommitmentV3,
    statement_hash: CommitmentV3,
    input_commitment_root: CommitmentV3,
    data_availability_root: CommitmentV3,
    parent_task_id: Option<TaskIdV3>,
    expected_child_task_root: Option<CommitmentV3>,
    max_input_bytes: u64,
    max_cycles_or_trace_rows: u64,
    max_memory_bytes: u64,
    deadline_sequence: u64,
    reward_asset_id: RewardAssetIdV1,
    max_reward_atoms: u128,
    redundancy_policy: RedundancyPolicyV1,
    privacy_policy: ProofTaskPrivacyPolicyV1,
    created_sequence: u64,
}

impl ProofTaskV1 {
    pub fn derive(mut input: ProofTaskInputV1) -> Result<Self, TaskManifestErrorV1> {
        canonicalize_proof_systems(&mut input.accepted_proof_systems)?;
        validate_task_input(&input)?;
        let task_id = derive_proof_task_id(&input)?;
        let value = Self::from_input(task_id, input);
        value.validate()?;
        Ok(value)
    }

    fn from_input(task_id: TaskIdV3, input: ProofTaskInputV1) -> Self {
        Self {
            task_version: PROOF_TASK_VERSION_V1,
            task_id,
            task_kind: input.task_kind,
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            epoch_id: input.epoch_id,
            priority: input.priority,
            proof_profile_id: input.proof_profile_id,
            accepted_proof_systems: input.accepted_proof_systems,
            program_manifest_root: input.program_manifest_root,
            statement_hash: input.statement_hash,
            input_commitment_root: input.input_commitment_root,
            data_availability_root: input.data_availability_root,
            parent_task_id: input.parent_task_id,
            expected_child_task_root: input.expected_child_task_root,
            max_input_bytes: input.max_input_bytes,
            max_cycles_or_trace_rows: input.max_cycles_or_trace_rows,
            max_memory_bytes: input.max_memory_bytes,
            deadline_sequence: input.deadline_sequence,
            reward_asset_id: input.reward_asset_id,
            max_reward_atoms: input.max_reward_atoms,
            redundancy_policy: input.redundancy_policy,
            privacy_policy: input.privacy_policy,
            created_sequence: input.created_sequence,
        }
    }

    fn input(&self) -> ProofTaskInputV1 {
        ProofTaskInputV1 {
            task_kind: self.task_kind,
            application_id: self.application_id,
            chain_or_domain_id: self.chain_or_domain_id,
            epoch_id: self.epoch_id,
            priority: self.priority,
            proof_profile_id: self.proof_profile_id,
            accepted_proof_systems: self.accepted_proof_systems.clone(),
            program_manifest_root: self.program_manifest_root,
            statement_hash: self.statement_hash,
            input_commitment_root: self.input_commitment_root,
            data_availability_root: self.data_availability_root,
            parent_task_id: self.parent_task_id,
            expected_child_task_root: self.expected_child_task_root,
            max_input_bytes: self.max_input_bytes,
            max_cycles_or_trace_rows: self.max_cycles_or_trace_rows,
            max_memory_bytes: self.max_memory_bytes,
            deadline_sequence: self.deadline_sequence,
            reward_asset_id: self.reward_asset_id,
            max_reward_atoms: self.max_reward_atoms,
            redundancy_policy: self.redundancy_policy,
            privacy_policy: self.privacy_policy,
            created_sequence: self.created_sequence,
        }
    }

    pub fn validate(&self) -> Result<(), TaskManifestErrorV1> {
        if self.task_version != PROOF_TASK_VERSION_V1 {
            return Err(TaskManifestErrorV1::InvalidVersion {
                field: "proof_task",
                actual: self.task_version,
            });
        }
        let input = self.input();
        validate_task_input(&input)?;
        if self.task_id != derive_proof_task_id(&input)? {
            return Err(TaskManifestErrorV1::InvalidDerivedIdentity("task_id"));
        }
        Ok(())
    }

    pub const fn task_id(&self) -> TaskIdV3 {
        self.task_id
    }

    pub const fn program_manifest_root(&self) -> CommitmentV3 {
        self.program_manifest_root
    }

    pub fn accepted_proof_systems(&self) -> &[ProofSystemIdV1] {
        &self.accepted_proof_systems
    }

    pub const fn proof_profile_id(&self) -> ProfileIdV3 {
        self.proof_profile_id
    }

    pub const fn privacy_policy(&self) -> ProofTaskPrivacyPolicyV1 {
        self.privacy_policy
    }

    pub const fn max_input_bytes(&self) -> u64 {
        self.max_input_bytes
    }

    pub const fn max_cycles_or_trace_rows(&self) -> u64 {
        self.max_cycles_or_trace_rows
    }

    pub const fn max_memory_bytes(&self) -> u64 {
        self.max_memory_bytes
    }

    pub const fn redundancy_policy(&self) -> RedundancyPolicyV1 {
        self.redundancy_policy
    }
}

impl<'de> Deserialize<'de> for ProofTaskV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProofTaskWireV1::deserialize(deserializer)?;
        let value = Self {
            task_version: wire.task_version,
            task_id: wire.task_id,
            task_kind: wire.task_kind,
            application_id: wire.application_id,
            chain_or_domain_id: wire.chain_or_domain_id,
            epoch_id: wire.epoch_id,
            priority: wire.priority,
            proof_profile_id: wire.proof_profile_id,
            accepted_proof_systems: wire.accepted_proof_systems,
            program_manifest_root: wire.program_manifest_root,
            statement_hash: wire.statement_hash,
            input_commitment_root: wire.input_commitment_root,
            data_availability_root: wire.data_availability_root,
            parent_task_id: wire.parent_task_id,
            expected_child_task_root: wire.expected_child_task_root,
            max_input_bytes: wire.max_input_bytes,
            max_cycles_or_trace_rows: wire.max_cycles_or_trace_rows,
            max_memory_bytes: wire.max_memory_bytes,
            deadline_sequence: wire.deadline_sequence,
            reward_asset_id: wire.reward_asset_id,
            max_reward_atoms: wire.max_reward_atoms,
            redundancy_policy: wire.redundancy_policy,
            privacy_policy: wire.privacy_policy,
            created_sequence: wire.created_sequence,
        };
        value.validate().map_err(de::Error::custom)?;
        Ok(value)
    }
}

fn validate_task_input(input: &ProofTaskInputV1) -> Result<(), TaskManifestErrorV1> {
    validate_proof_systems(&input.accepted_proof_systems)?;
    let has_child_root = input.expected_child_task_root.is_some();
    if input.task_kind.requires_child_root() != has_child_root {
        return Err(TaskManifestErrorV1::InvalidChildBinding);
    }
    for (field, value, maximum) in [
        (
            "max_input_bytes",
            input.max_input_bytes,
            MAX_TASK_INPUT_BYTES_V1,
        ),
        (
            "max_cycles_or_trace_rows",
            input.max_cycles_or_trace_rows,
            MAX_TASK_CYCLES_V1,
        ),
        (
            "max_memory_bytes",
            input.max_memory_bytes,
            MAX_TASK_MEMORY_BYTES_V1,
        ),
    ] {
        if value == 0 || value > maximum {
            return Err(TaskManifestErrorV1::InvalidResourceBound(field));
        }
    }
    if input.deadline_sequence <= input.created_sequence {
        return Err(TaskManifestErrorV1::InvalidDeadline);
    }
    if input.max_reward_atoms == 0 {
        return Err(TaskManifestErrorV1::InvalidResourceBound(
            "max_reward_atoms",
        ));
    }
    input
        .redundancy_policy
        .validate(input.accepted_proof_systems.len())?;
    Ok(())
}

fn canonicalize_proof_systems(values: &mut [ProofSystemIdV1]) -> Result<(), TaskManifestErrorV1> {
    if values.len() > MAX_ACCEPTED_PROOF_SYSTEMS_V1 {
        return Err(TaskManifestErrorV1::TooManyProofSystems {
            actual: values.len(),
            maximum: MAX_ACCEPTED_PROOF_SYSTEMS_V1,
        });
    }
    values.sort_unstable();
    validate_proof_systems(values)
}

fn validate_proof_systems(values: &[ProofSystemIdV1]) -> Result<(), TaskManifestErrorV1> {
    if values.is_empty() {
        return Err(TaskManifestErrorV1::EmptyProofSystems);
    }
    if values.len() > MAX_ACCEPTED_PROOF_SYSTEMS_V1 {
        return Err(TaskManifestErrorV1::TooManyProofSystems {
            actual: values.len(),
            maximum: MAX_ACCEPTED_PROOF_SYSTEMS_V1,
        });
    }
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(TaskManifestErrorV1::DuplicateProofSystem);
    }
    Ok(())
}

fn derive_proof_task_id(input: &ProofTaskInputV1) -> Result<TaskIdV3, TaskManifestErrorV1> {
    let mut hasher = domain_hasher(PROOF_TASK_ID_DOMAIN_V1)?;
    hasher.update(PROOF_TASK_VERSION_V1.to_be_bytes());
    hasher.update([task_kind_tag(input.task_kind)]);
    hasher.update(input.application_id.as_bytes());
    hasher.update(input.chain_or_domain_id.as_bytes());
    hasher.update(input.epoch_id.to_be_bytes());
    hasher.update([priority_tag(input.priority)]);
    hasher.update(input.proof_profile_id.as_bytes());
    let count = u16::try_from(input.accepted_proof_systems.len())
        .map_err(|_| TaskManifestErrorV1::ArithmeticOverflow("accepted_proof_system_count"))?;
    hasher.update(count.to_be_bytes());
    for system in &input.accepted_proof_systems {
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
    write_optional_task(&mut hasher, input.parent_task_id);
    write_optional_commitment(&mut hasher, input.expected_child_task_root);
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
    TaskIdV3::new(hasher.finalize().into())
        .map_err(|_| TaskManifestErrorV1::InvalidDerivedIdentity("task_id_zero_hash"))
}
