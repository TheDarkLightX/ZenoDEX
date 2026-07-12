use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, ProfileIdV3, ProgramIdV3};
use zenodex_zrpf_risc0_semantic_shared::spot_represented_value_profile_id_v1;
use zenodex_zrpf_risc0_shared::profile_id_v3;

use crate::SpotValueLeafProposalErrorV4;

pub const PINNED_V1_ADAPTER_IMAGE_ID_A: [u32; 8] = [
    2_750_530_258,
    37_668_129,
    744_178_984,
    4_248_971_762,
    810_572_263,
    4_257_446_307,
    1_152_353_364,
    1_683_867_498,
];

pub const RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1: &str = "risc0_succinct_poseidon2_resolve_3_0_5_v1";
pub const RISC0_VERIFIER_PARAMETERS_DIGEST_V1: [u8; 32] = [
    0xec, 0xe5, 0xe9, 0xb8, 0xae, 0x2c, 0xd6, 0xea, 0x6b, 0x18, 0x27, 0xb4, 0x64, 0xff, 0x03, 0x48,
    0xf9, 0xa7, 0xf4, 0xde, 0xcd, 0x26, 0x9c, 0x00, 0x87, 0xfd, 0xfd, 0x75, 0x09, 0x8d, 0xa0, 0x13,
];
pub const RISC0_RESOLVE_CONTROL_ID_V1: [u8; 32] = [
    0x53, 0xa7, 0xb2, 0x3d, 0x07, 0xf9, 0x9e, 0x5d, 0x56, 0x85, 0xe8, 0x58, 0x74, 0xf5, 0x18, 0x1e,
    0x84, 0x86, 0xaa, 0x26, 0x7a, 0x0a, 0xe6, 0x07, 0xff, 0xe9, 0xba, 0x47, 0xc8, 0xbd, 0xda, 0x4a,
];

const PROOF_SYSTEM_DOMAIN_V4: &[u8] = b"zenodex.zrpf.proof_system_id.v4";
const RECEIPT_SECURITY_DOMAIN_V4: &[u8] = b"zenodex.zrpf.receipt_security_profile_id.v4";
const VALUE_LEAF_MANIFEST_DOMAIN_V4: &[u8] = b"zenodex.zrpf.spot_value_leaf_manifest.v4";
const VALUE_LEAF_MANIFEST_CLASS_V4: &[u8] = b"unreleased_spot_value_leaf_manifest_v4";
const VALUE_LEAF_PROFILE_V4: &str = "zrpf_spot_value_leaf_v4";

pub fn spot_value_leaf_profile_id_v4() -> Result<ProfileIdV3, SpotValueLeafProposalErrorV4> {
    profile_id_v3(VALUE_LEAF_PROFILE_V4)
        .map_err(|_| SpotValueLeafProposalErrorV4::Derivation("leaf_profile_id"))
}

pub fn risc0_proof_system_id_v4() -> Result<CommitmentV3, SpotValueLeafProposalErrorV4> {
    commitment_hash_framed(
        PROOF_SYSTEM_DOMAIN_V4,
        &[b"risc0-zkvm", b"3.0.5", b"rv32im"],
    )
}

pub fn risc0_succinct_receipt_security_profile_id_v4(
) -> Result<CommitmentV3, SpotValueLeafProposalErrorV4> {
    commitment_hash_framed(
        RECEIPT_SECURITY_DOMAIN_V4,
        &[
            RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1.as_bytes(),
            b"succinct",
            &RISC0_VERIFIER_PARAMETERS_DIGEST_V1,
            b"poseidon2",
            &RISC0_RESOLVE_CONTROL_ID_V1,
        ],
    )
}

pub fn risc0_verifier_parameters_root_v4() -> Result<CommitmentV3, SpotValueLeafProposalErrorV4> {
    CommitmentV3::new(RISC0_VERIFIER_PARAMETERS_DIGEST_V1)
        .map_err(SpotValueLeafProposalErrorV4::Structural)
}

pub fn spot_value_leaf_manifest_root_v4(
    program_id: ProgramIdV3,
    adapter_program_id: ProgramIdV3,
) -> Result<CommitmentV3, SpotValueLeafProposalErrorV4> {
    let profile_id = spot_value_leaf_profile_id_v4()?;
    let proof_system = risc0_proof_system_id_v4()?;
    let receipt_security = risc0_succinct_receipt_security_profile_id_v4()?;
    let verifier_parameters = risc0_verifier_parameters_root_v4()?;
    let value_profile = spot_represented_value_profile_id_v1()?;
    commitment_hash_framed(
        VALUE_LEAF_MANIFEST_DOMAIN_V4,
        &[
            program_id.as_bytes(),
            profile_id.as_bytes(),
            adapter_program_id.as_bytes(),
            proof_system.as_bytes(),
            receipt_security.as_bytes(),
            verifier_parameters.as_bytes(),
            value_profile.as_bytes(),
            VALUE_LEAF_MANIFEST_CLASS_V4,
        ],
    )
}

fn commitment_hash_framed(
    domain: &[u8],
    fields: &[&[u8]],
) -> Result<CommitmentV3, SpotValueLeafProposalErrorV4> {
    let mut hasher = Sha256::new();
    let domain_length = u16::try_from(domain.len())
        .map_err(|_| SpotValueLeafProposalErrorV4::Derivation("hash_domain_length"))?;
    hasher.update(domain_length.to_be_bytes());
    hasher.update(domain);
    for field in fields {
        let length = u32::try_from(field.len())
            .map_err(|_| SpotValueLeafProposalErrorV4::Derivation("hash_field_length"))?;
        hasher.update(length.to_be_bytes());
        hasher.update(field);
    }
    CommitmentV3::new(hasher.finalize().into()).map_err(SpotValueLeafProposalErrorV4::Structural)
}
