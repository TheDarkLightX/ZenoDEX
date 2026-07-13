use super::assignment_policy::ProofAssignmentPolicyV1;
use super::base::{PrivacyClaimV1, ProofSystemIdV1, ProofTaskPrivacyPolicyV1, ReceiptCodecIdV1};
use super::manifest::ProgramManifestV1;
use super::task::ProofTaskV1;
use crate::{CommitmentV3, ProfileIdV3, TaskIdV3};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofAssignmentResourceV1 {
    InputBytes,
    CyclesOrTraceRows,
    MemoryBytes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofAssignmentRejectV1 {
    InvalidTask,
    InvalidManifest,
    InvalidPolicy,
    TaskManifestRootMismatch,
    ManifestRootNotAuthorized,
    UnsupportedProofSystem,
    ProofProfileMismatch,
    ReceiptCodecMismatch,
    VerifierPolicyRootMismatch,
    SecurityLevelBelowMinimum,
    PolicyNotYetValid,
    PolicyExpired,
    ManifestRevoked,
    PrivacyDowngrade,
    ResourceCeilingExceeded(ProofAssignmentResourceV1),
    ImpossibleRedundancy,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofAssignmentPendingV1 {
    StandbyDiversitySemantics,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofAssignmentCompatibilityVerdictV1 {
    Compatible(CompatibleProofAssignmentV1),
    Rejected(ProofAssignmentRejectV1),
    Pending(ProofAssignmentPendingV1),
}

/// Exact identities that passed the pure V1 compatibility check.
///
/// This snapshot carries no proof, payment, settlement, or admission authority.
/// It is intentionally neither serializable nor deserializable.
///
/// ```compile_fail
/// fn requires_serialize<T: serde::Serialize>() {}
/// requires_serialize::<zenodex_zrpf_protocol_v3::CompatibleProofAssignmentV1>();
/// ```
///
/// ```compile_fail
/// fn requires_deserialize<T: for<'de> serde::Deserialize<'de>>() {}
/// requires_deserialize::<zenodex_zrpf_protocol_v3::CompatibleProofAssignmentV1>();
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompatibleProofAssignmentV1 {
    task_id: TaskIdV3,
    program_manifest_root: CommitmentV3,
    selected_proof_system_id: ProofSystemIdV1,
    proof_profile_id: ProfileIdV3,
    receipt_codec_id: ReceiptCodecIdV1,
    verifier_policy_root: CommitmentV3,
    assignment_epoch: u64,
}

impl CompatibleProofAssignmentV1 {
    pub const fn task_id(&self) -> TaskIdV3 {
        self.task_id
    }

    pub const fn program_manifest_root(&self) -> CommitmentV3 {
        self.program_manifest_root
    }

    pub const fn selected_proof_system_id(&self) -> ProofSystemIdV1 {
        self.selected_proof_system_id
    }

    pub const fn proof_profile_id(&self) -> ProfileIdV3 {
        self.proof_profile_id
    }

    pub const fn receipt_codec_id(&self) -> ReceiptCodecIdV1 {
        self.receipt_codec_id
    }

    pub const fn verifier_policy_root(&self) -> CommitmentV3 {
        self.verifier_policy_root
    }

    pub const fn assignment_epoch(&self) -> u64 {
        self.assignment_epoch
    }
}

/// Evaluates local compatibility from explicit inputs with deterministic
/// first-reject precedence.
///
/// The caller remains responsible for authenticating `policy` and the meaning
/// of `assignment_epoch`.
pub fn evaluate_proof_assignment_compatibility_v1(
    task: &ProofTaskV1,
    manifest: &ProgramManifestV1,
    policy: &ProofAssignmentPolicyV1,
    assignment_epoch: u64,
) -> ProofAssignmentCompatibilityVerdictV1 {
    if let Err(reason) = first_reject(task, manifest, policy, assignment_epoch) {
        return ProofAssignmentCompatibilityVerdictV1::Rejected(reason);
    }
    if redundancy_needs_governed_semantics(task) {
        return ProofAssignmentCompatibilityVerdictV1::Pending(
            ProofAssignmentPendingV1::StandbyDiversitySemantics,
        );
    }
    ProofAssignmentCompatibilityVerdictV1::Compatible(CompatibleProofAssignmentV1 {
        task_id: task.task_id(),
        program_manifest_root: manifest.manifest_root(),
        selected_proof_system_id: manifest.proof_system_id(),
        proof_profile_id: task.proof_profile_id(),
        receipt_codec_id: manifest.receipt_codec_id(),
        verifier_policy_root: manifest.verifier_policy_root(),
        assignment_epoch,
    })
}

fn first_reject(
    task: &ProofTaskV1,
    manifest: &ProgramManifestV1,
    policy: &ProofAssignmentPolicyV1,
    assignment_epoch: u64,
) -> Result<(), ProofAssignmentRejectV1> {
    validate_objects(task, manifest, policy)?;
    check_root_and_system(task, manifest, policy)?;
    check_profile_contract(task, manifest, policy)?;
    check_security_and_time(manifest, policy, assignment_epoch)?;
    check_privacy(task, manifest)?;
    check_resources(task, policy)?;
    check_redundancy_feasibility(task)
}

fn validate_objects(
    task: &ProofTaskV1,
    manifest: &ProgramManifestV1,
    policy: &ProofAssignmentPolicyV1,
) -> Result<(), ProofAssignmentRejectV1> {
    task.validate()
        .map_err(|_| ProofAssignmentRejectV1::InvalidTask)?;
    manifest
        .validate()
        .map_err(|_| ProofAssignmentRejectV1::InvalidManifest)?;
    policy
        .validate()
        .map_err(|_| ProofAssignmentRejectV1::InvalidPolicy)
}

fn check_root_and_system(
    task: &ProofTaskV1,
    manifest: &ProgramManifestV1,
    policy: &ProofAssignmentPolicyV1,
) -> Result<(), ProofAssignmentRejectV1> {
    if task.program_manifest_root() != manifest.manifest_root() {
        return Err(ProofAssignmentRejectV1::TaskManifestRootMismatch);
    }
    if manifest.manifest_root() != policy.authorized_program_manifest_root() {
        return Err(ProofAssignmentRejectV1::ManifestRootNotAuthorized);
    }
    if task
        .accepted_proof_systems()
        .binary_search(&manifest.proof_system_id())
        .is_err()
    {
        return Err(ProofAssignmentRejectV1::UnsupportedProofSystem);
    }
    Ok(())
}

fn check_profile_contract(
    task: &ProofTaskV1,
    manifest: &ProgramManifestV1,
    policy: &ProofAssignmentPolicyV1,
) -> Result<(), ProofAssignmentRejectV1> {
    if task.proof_profile_id() != policy.required_proof_profile_id() {
        return Err(ProofAssignmentRejectV1::ProofProfileMismatch);
    }
    if manifest.receipt_codec_id() != policy.required_receipt_codec_id() {
        return Err(ProofAssignmentRejectV1::ReceiptCodecMismatch);
    }
    if manifest.verifier_policy_root() != policy.required_verifier_policy_root() {
        return Err(ProofAssignmentRejectV1::VerifierPolicyRootMismatch);
    }
    Ok(())
}

fn check_security_and_time(
    manifest: &ProgramManifestV1,
    policy: &ProofAssignmentPolicyV1,
    assignment_epoch: u64,
) -> Result<(), ProofAssignmentRejectV1> {
    if manifest.security_level_bits() < policy.minimum_security_level_bits() {
        return Err(ProofAssignmentRejectV1::SecurityLevelBelowMinimum);
    }
    if assignment_epoch < policy.valid_from_epoch() {
        return Err(ProofAssignmentRejectV1::PolicyNotYetValid);
    }
    if assignment_epoch > policy.valid_through_epoch() {
        return Err(ProofAssignmentRejectV1::PolicyExpired);
    }
    if manifest
        .revocation_epoch()
        .is_some_and(|revocation_epoch| assignment_epoch >= revocation_epoch)
    {
        return Err(ProofAssignmentRejectV1::ManifestRevoked);
    }
    Ok(())
}

fn check_privacy(
    task: &ProofTaskV1,
    manifest: &ProgramManifestV1,
) -> Result<(), ProofAssignmentRejectV1> {
    if matches!(
        (task.privacy_policy(), manifest.privacy_claim()),
        (
            ProofTaskPrivacyPolicyV1::PrivateWitnessRequired,
            PrivacyClaimV1::PublicComputation
        )
    ) {
        return Err(ProofAssignmentRejectV1::PrivacyDowngrade);
    }
    Ok(())
}

fn check_resources(
    task: &ProofTaskV1,
    policy: &ProofAssignmentPolicyV1,
) -> Result<(), ProofAssignmentRejectV1> {
    for (resource, actual, maximum) in [
        (
            ProofAssignmentResourceV1::InputBytes,
            task.max_input_bytes(),
            policy.max_input_bytes(),
        ),
        (
            ProofAssignmentResourceV1::CyclesOrTraceRows,
            task.max_cycles_or_trace_rows(),
            policy.max_cycles_or_trace_rows(),
        ),
        (
            ProofAssignmentResourceV1::MemoryBytes,
            task.max_memory_bytes(),
            policy.max_memory_bytes(),
        ),
    ] {
        if actual > maximum {
            return Err(ProofAssignmentRejectV1::ResourceCeilingExceeded(resource));
        }
    }
    Ok(())
}

fn check_redundancy_feasibility(task: &ProofTaskV1) -> Result<(), ProofAssignmentRejectV1> {
    let redundancy = task.redundancy_policy();
    let total_slots =
        u16::from(redundancy.required_primary_proofs()) + u16::from(redundancy.standby_provers());
    if u16::from(redundancy.minimum_distinct_proof_systems()) > total_slots {
        return Err(ProofAssignmentRejectV1::ImpossibleRedundancy);
    }
    Ok(())
}

fn redundancy_needs_governed_semantics(task: &ProofTaskV1) -> bool {
    let redundancy = task.redundancy_policy();
    redundancy.minimum_distinct_proof_systems() > redundancy.required_primary_proofs()
}
