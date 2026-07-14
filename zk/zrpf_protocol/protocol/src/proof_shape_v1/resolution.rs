use alloc::vec::Vec;

use serde::Serialize;
use sha2::Digest;

use super::hash::{domain_hasher, resolution_id};
use super::{
    AllowedChildBindingV1, AssumptionIdV1, AssumptionManifestIdV1, AssumptionManifestV1,
    AssumptionResolutionIdV1, ProofShapeErrorV1, ProofShapeIdV1, ProofShapeKindV1, ProofShapeV1,
    ASSUMPTION_RESOLUTION_VERSION_V1, MAX_RESOLVED_CHILD_CLAIMS_V1, MAX_SHAPE_JOURNAL_BYTES_V1,
};
use crate::{CommitmentV3, ProfileIdV3, ProgramIdV3};

const ASSUMPTION_RESOLUTION_ID_DOMAIN_V1: &[u8] = b"zkpf.assumption_resolution_id.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedChildClaimInputV1 {
    pub assumption_id: AssumptionIdV1,
    pub verification_claim_hash: CommitmentV3,
    pub child_shape_id: ProofShapeIdV1,
    pub child_program_id: ProgramIdV3,
    pub child_profile_id: ProfileIdV3,
    pub child_journal_hash: CommitmentV3,
    pub child_journal_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResolvedChildClaimV1 {
    assumption_id: AssumptionIdV1,
    verification_claim_hash: CommitmentV3,
    child_shape_id: ProofShapeIdV1,
    child_program_id: ProgramIdV3,
    child_profile_id: ProfileIdV3,
    child_journal_hash: CommitmentV3,
    child_journal_bytes: u64,
}

impl ResolvedChildClaimV1 {
    pub fn new(input: ResolvedChildClaimInputV1) -> Result<Self, ProofShapeErrorV1> {
        if input.child_journal_bytes == 0 || input.child_journal_bytes > MAX_SHAPE_JOURNAL_BYTES_V1
        {
            return Err(ProofShapeErrorV1::InvalidResolvedChildJournalBytes);
        }
        Ok(Self {
            assumption_id: input.assumption_id,
            verification_claim_hash: input.verification_claim_hash,
            child_shape_id: input.child_shape_id,
            child_program_id: input.child_program_id,
            child_profile_id: input.child_profile_id,
            child_journal_hash: input.child_journal_hash,
            child_journal_bytes: input.child_journal_bytes,
        })
    }

    pub const fn assumption_id(&self) -> AssumptionIdV1 {
        self.assumption_id
    }

    pub const fn verification_claim_hash(&self) -> CommitmentV3 {
        self.verification_claim_hash
    }

    pub const fn child_shape_id(&self) -> ProofShapeIdV1 {
        self.child_shape_id
    }

    pub const fn child_program_id(&self) -> ProgramIdV3 {
        self.child_program_id
    }

    pub const fn child_profile_id(&self) -> ProfileIdV3 {
        self.child_profile_id
    }

    pub const fn child_journal_hash(&self) -> CommitmentV3 {
        self.child_journal_hash
    }

    pub const fn child_journal_bytes(&self) -> u64 {
        self.child_journal_bytes
    }

    pub const fn proof_authority(&self) -> bool {
        false
    }

    pub const fn release_authority(&self) -> bool {
        false
    }

    pub const fn settlement_authority(&self) -> bool {
        false
    }

    pub const fn production_authority(&self) -> bool {
        false
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AssumptionResolutionV1 {
    resolution_version: u16,
    resolution_id: AssumptionResolutionIdV1,
    proof_shape_id: ProofShapeIdV1,
    assumption_manifest_id: AssumptionManifestIdV1,
    claims: Vec<ResolvedChildClaimV1>,
}

impl AssumptionResolutionV1 {
    pub fn validate(&self) -> Result<(), ProofShapeErrorV1> {
        if self.resolution_version != ASSUMPTION_RESOLUTION_VERSION_V1 {
            return Err(ProofShapeErrorV1::InvalidVersion {
                field: "assumption_resolution",
                actual: self.resolution_version,
            });
        }
        validate_resolved_claim_set(&self.claims)?;
        if self.resolution_id != derive_resolution_id_v1(self)? {
            return Err(ProofShapeErrorV1::InvalidDerivedIdentity(
                "assumption_resolution_id",
            ));
        }
        Ok(())
    }

    pub const fn resolution_id(&self) -> AssumptionResolutionIdV1 {
        self.resolution_id
    }

    pub const fn proof_shape_id(&self) -> ProofShapeIdV1 {
        self.proof_shape_id
    }

    pub const fn assumption_manifest_id(&self) -> AssumptionManifestIdV1 {
        self.assumption_manifest_id
    }

    pub fn claims(&self) -> &[ResolvedChildClaimV1] {
        &self.claims
    }

    pub const fn proof_authority(&self) -> bool {
        false
    }

    pub const fn release_authority(&self) -> bool {
        false
    }

    pub const fn settlement_authority(&self) -> bool {
        false
    }

    pub const fn production_authority(&self) -> bool {
        false
    }
}

pub fn resolve_assumptions_v1(
    shape: &ProofShapeV1,
    manifest: &AssumptionManifestV1,
    claims: Vec<ResolvedChildClaimV1>,
) -> Result<AssumptionResolutionV1, ProofShapeErrorV1> {
    validate_shape_manifest_contract_v1(shape, manifest)?;
    validate_resolved_claim_set(&claims)?;
    reject_surplus_claims(manifest, &claims)?;

    let mut canonical_claims = Vec::with_capacity(manifest.required_assumptions().len());
    let mut total_child_journal_bytes = 0_u64;
    for requirement in manifest.required_assumptions() {
        let claim = claims
            .iter()
            .find(|claim| claim.assumption_id() == requirement.assumption_id())
            .ok_or(ProofShapeErrorV1::UnresolvedAssumption {
                slot: requirement.slot(),
            })?;
        let binding = find_allowed_binding(shape, requirement.allowed_child_binding_id())?;
        validate_claim_binding(claim, binding)?;
        total_child_journal_bytes = total_child_journal_bytes
            .checked_add(claim.child_journal_bytes())
            .ok_or(ProofShapeErrorV1::ArithmeticOverflow(
                "resolved_child_journal_bytes",
            ))?;
        canonical_claims.push(claim.clone());
    }
    let maximum = shape.resource_ceilings().max_total_child_journal_bytes();
    if total_child_journal_bytes > maximum {
        return Err(ProofShapeErrorV1::TotalChildJournalCeilingExceeded {
            actual: total_child_journal_bytes,
            maximum,
        });
    }

    let resolution_id =
        derive_resolution_id_parts_v1(shape.shape_id(), manifest.manifest_id(), &canonical_claims)?;
    let resolution = AssumptionResolutionV1 {
        resolution_version: ASSUMPTION_RESOLUTION_VERSION_V1,
        resolution_id,
        proof_shape_id: shape.shape_id(),
        assumption_manifest_id: manifest.manifest_id(),
        claims: canonical_claims,
    };
    resolution.validate()?;
    Ok(resolution)
}

pub(super) fn validate_shape_manifest_contract_v1(
    shape: &ProofShapeV1,
    manifest: &AssumptionManifestV1,
) -> Result<(), ProofShapeErrorV1> {
    shape.validate()?;
    manifest.validate()?;
    if manifest.proof_shape_id() != shape.shape_id() {
        return Err(ProofShapeErrorV1::ProofShapeMismatch {
            expected: shape.shape_id(),
            actual: manifest.proof_shape_id(),
        });
    }
    let required_count = manifest.required_assumptions().len();
    let maximum = usize::try_from(shape.resource_ceilings().max_assumptions())
        .map_err(|_| ProofShapeErrorV1::ArithmeticOverflow("max_assumptions"))?;
    if required_count > maximum {
        return Err(ProofShapeErrorV1::AssumptionCountCeilingExceeded {
            actual: required_count,
            maximum,
        });
    }
    match shape.shape_kind() {
        ProofShapeKindV1::Leaf if required_count != 0 => {
            return Err(ProofShapeErrorV1::LeafHasChildContract);
        }
        ProofShapeKindV1::Aggregate if required_count == 0 => {
            return Err(ProofShapeErrorV1::AggregateHasNoChildContract);
        }
        ProofShapeKindV1::Leaf | ProofShapeKindV1::Aggregate => {}
    }

    let mut maximum_child_journal_bytes = 0_u64;
    for requirement in manifest.required_assumptions() {
        let binding = find_allowed_binding(shape, requirement.allowed_child_binding_id())?;
        maximum_child_journal_bytes = maximum_child_journal_bytes
            .checked_add(binding.max_child_journal_bytes())
            .ok_or(ProofShapeErrorV1::ArithmeticOverflow(
                "maximum_child_journal_bytes",
            ))?;
    }
    let maximum_total = shape.resource_ceilings().max_total_child_journal_bytes();
    if maximum_child_journal_bytes > maximum_total {
        return Err(ProofShapeErrorV1::TotalChildJournalCeilingExceeded {
            actual: maximum_child_journal_bytes,
            maximum: maximum_total,
        });
    }
    Ok(())
}

fn validate_resolved_claim_set(claims: &[ResolvedChildClaimV1]) -> Result<(), ProofShapeErrorV1> {
    if claims.len() > MAX_RESOLVED_CHILD_CLAIMS_V1 {
        return Err(ProofShapeErrorV1::TooManyResolvedClaims {
            actual: claims.len(),
            maximum: MAX_RESOLVED_CHILD_CLAIMS_V1,
        });
    }
    for (index, claim) in claims.iter().enumerate() {
        for prior in &claims[..index] {
            if prior.assumption_id() == claim.assumption_id() {
                return Err(ProofShapeErrorV1::DuplicateResolvedAssumption);
            }
            if prior.verification_claim_hash() == claim.verification_claim_hash() {
                return Err(ProofShapeErrorV1::DuplicateVerificationClaim);
            }
            if prior.child_journal_hash() == claim.child_journal_hash() {
                return Err(ProofShapeErrorV1::DuplicateResolvedChildJournal);
            }
        }
    }
    Ok(())
}

fn reject_surplus_claims(
    manifest: &AssumptionManifestV1,
    claims: &[ResolvedChildClaimV1],
) -> Result<(), ProofShapeErrorV1> {
    for claim in claims {
        if !manifest
            .required_assumptions()
            .iter()
            .any(|requirement| requirement.assumption_id() == claim.assumption_id())
        {
            return Err(ProofShapeErrorV1::SurplusResolvedClaim {
                assumption_id: claim.assumption_id(),
            });
        }
    }
    Ok(())
}

fn find_allowed_binding(
    shape: &ProofShapeV1,
    binding_id: super::AllowedChildBindingIdV1,
) -> Result<&AllowedChildBindingV1, ProofShapeErrorV1> {
    shape
        .allowed_child_bindings()
        .iter()
        .find(|binding| binding.binding_id() == binding_id)
        .ok_or(ProofShapeErrorV1::RequiredBindingNotAllowed)
}

fn validate_claim_binding(
    claim: &ResolvedChildClaimV1,
    binding: &AllowedChildBindingV1,
) -> Result<(), ProofShapeErrorV1> {
    if claim.child_shape_id() != binding.child_shape_id() {
        return Err(ProofShapeErrorV1::ChildShapeMismatch);
    }
    if claim.child_program_id() != binding.child_program_id() {
        return Err(ProofShapeErrorV1::ChildProgramMismatch);
    }
    if claim.child_profile_id() != binding.child_profile_id() {
        return Err(ProofShapeErrorV1::ChildProfileMismatch);
    }
    if claim.child_journal_hash() != binding.child_journal_hash() {
        return Err(ProofShapeErrorV1::ChildJournalMismatch);
    }
    if claim.child_journal_bytes() > binding.max_child_journal_bytes() {
        return Err(ProofShapeErrorV1::ChildJournalBytesExceeded {
            actual: claim.child_journal_bytes(),
            maximum: binding.max_child_journal_bytes(),
        });
    }
    Ok(())
}

fn derive_resolution_id_v1(
    resolution: &AssumptionResolutionV1,
) -> Result<AssumptionResolutionIdV1, ProofShapeErrorV1> {
    derive_resolution_id_parts_v1(
        resolution.proof_shape_id,
        resolution.assumption_manifest_id,
        &resolution.claims,
    )
}

fn derive_resolution_id_parts_v1(
    proof_shape_id: ProofShapeIdV1,
    assumption_manifest_id: AssumptionManifestIdV1,
    claims: &[ResolvedChildClaimV1],
) -> Result<AssumptionResolutionIdV1, ProofShapeErrorV1> {
    let mut hasher = domain_hasher(ASSUMPTION_RESOLUTION_ID_DOMAIN_V1)?;
    hasher.update(ASSUMPTION_RESOLUTION_VERSION_V1.to_be_bytes());
    hasher.update(proof_shape_id.as_bytes());
    hasher.update(assumption_manifest_id.as_bytes());
    let count = u16::try_from(claims.len())
        .map_err(|_| ProofShapeErrorV1::ArithmeticOverflow("resolved_claim_count"))?;
    hasher.update(count.to_be_bytes());
    for claim in claims {
        hasher.update(claim.assumption_id().as_bytes());
        hasher.update(claim.verification_claim_hash().as_bytes());
        hasher.update(claim.child_journal_bytes().to_be_bytes());
    }
    resolution_id(hasher)
}
