use sha2::{Digest, Sha256};

use super::super::{semantic_epoch_profile_id_v1, CommitmentV3, SemanticEpochDependencyProgramsV1};
use super::SemanticEpochErrorV2;

const DEPENDENCY_MANIFEST_DOMAIN_V2: &[u8] = b"zenodex.zrpf.semantic_epoch_dependency_manifest.v1";
const DEPENDENCY_MANIFEST_CLASS_V2: &[u8] = b"unreleased_semantic_epoch_dependency_manifest";
const ADAPTER_PROGRAM_ROLE_V2: &[u8] = b"adapter_program_id";
const LEVEL_ONE_PROGRAM_ROLE_V2: &[u8] = b"level_one_program_id";
const LEVEL_TWO_PROGRAM_ROLE_V2: &[u8] = b"level_two_program_id";

/// Commits the three programs whose authenticated statements are interpreted
/// by the semantic guest. The semantic guest's own runtime image is excluded
/// deliberately and is attached only by the sealed receipt verifier.
pub fn semantic_epoch_dependency_manifest_root_v2(
    dependencies: &SemanticEpochDependencyProgramsV1,
) -> Result<CommitmentV3, SemanticEpochErrorV2> {
    let profile_id = semantic_epoch_profile_id_v1()?;
    let adapter_program_id = dependencies.adapter_program_id();
    let level_one_program_id = dependencies.level_one_program_id();
    let level_two_program_id = dependencies.level_two_program_id();
    let fields: [&[u8]; 8] = [
        profile_id.as_bytes(),
        ADAPTER_PROGRAM_ROLE_V2,
        adapter_program_id.as_bytes(),
        LEVEL_ONE_PROGRAM_ROLE_V2,
        level_one_program_id.as_bytes(),
        LEVEL_TWO_PROGRAM_ROLE_V2,
        level_two_program_id.as_bytes(),
        DEPENDENCY_MANIFEST_CLASS_V2,
    ];
    let mut hasher = Sha256::new();
    let domain_length = u16::try_from(DEPENDENCY_MANIFEST_DOMAIN_V2.len())
        .map_err(|_| SemanticEpochErrorV2::ArithmeticOverflow("dependency_manifest_domain"))?;
    hasher.update(domain_length.to_be_bytes());
    hasher.update(DEPENDENCY_MANIFEST_DOMAIN_V2);
    for field in fields {
        let length = u32::try_from(field.len())
            .map_err(|_| SemanticEpochErrorV2::ArithmeticOverflow("dependency_manifest_field"))?;
        hasher.update(length.to_be_bytes());
        hasher.update(field);
    }
    Ok(CommitmentV3::new(hasher.finalize().into())?)
}
