use sha2::{Digest, Sha256};

use super::{
    AllowedChildBindingIdV1, AssumptionIdV1, AssumptionManifestIdV1, AssumptionResolutionIdV1,
    ProofShapeErrorV1, ProofShapeIdV1, ProofShapeRegistryIdV1,
};

pub(super) fn domain_hasher(domain: &[u8]) -> Result<Sha256, ProofShapeErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| ProofShapeErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

pub(super) fn binding_id(hasher: Sha256) -> Result<AllowedChildBindingIdV1, ProofShapeErrorV1> {
    AllowedChildBindingIdV1::new(hasher.finalize().into())
        .map_err(|_| ProofShapeErrorV1::InvalidDerivedIdentity("allowed_child_binding_id"))
}

pub(super) fn proof_shape_id(hasher: Sha256) -> Result<ProofShapeIdV1, ProofShapeErrorV1> {
    ProofShapeIdV1::new(hasher.finalize().into())
        .map_err(|_| ProofShapeErrorV1::InvalidDerivedIdentity("proof_shape_id"))
}

pub(super) fn assumption_id(hasher: Sha256) -> Result<AssumptionIdV1, ProofShapeErrorV1> {
    AssumptionIdV1::new(hasher.finalize().into())
        .map_err(|_| ProofShapeErrorV1::InvalidDerivedIdentity("assumption_id"))
}

pub(super) fn manifest_id(hasher: Sha256) -> Result<AssumptionManifestIdV1, ProofShapeErrorV1> {
    AssumptionManifestIdV1::new(hasher.finalize().into())
        .map_err(|_| ProofShapeErrorV1::InvalidDerivedIdentity("assumption_manifest_id"))
}

pub(super) fn resolution_id(hasher: Sha256) -> Result<AssumptionResolutionIdV1, ProofShapeErrorV1> {
    AssumptionResolutionIdV1::new(hasher.finalize().into())
        .map_err(|_| ProofShapeErrorV1::InvalidDerivedIdentity("assumption_resolution_id"))
}

pub(super) fn registry_id(hasher: Sha256) -> Result<ProofShapeRegistryIdV1, ProofShapeErrorV1> {
    ProofShapeRegistryIdV1::new(hasher.finalize().into())
        .map_err(|_| ProofShapeErrorV1::InvalidDerivedIdentity("proof_shape_registry_id"))
}
