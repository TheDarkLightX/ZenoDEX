//! Exact binary manifest for the receipt-verifying Spot V7 PID-1 lane.
//!
//! Decoding this manifest grants no execution or settlement authority. It
//! closes the bounded byte and image-identity proposal consumed immediately
//! before the governed verifier. The live runner, release policy, final image
//! identities, and atomic store remain separate authority gates.

use core::fmt;

use sha2::{Digest as _, Sha256};

use crate::SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1;

pub const SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1: usize = 256;
pub const SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V7_RECEIPT_BYTES_V1: usize = 16 * 1_024 * 1_024;
pub const SPOT_V7_FIRECRACKER_AUTHORITY_MAX_GUEST_INPUT_BYTES_V1: usize = 16 * 1_024 * 1_024;
pub const SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V6_RECEIPT_BYTES_V1: usize = 16 * 1_024 * 1_024;

const MANIFEST_MAGIC_V1: &[u8; 8] = b"ZSV7AIM1";
const MANIFEST_VERSION_V1: u16 = 1;
const MANIFEST_BYTES_FIELD_V1: u16 = 256;

pub const SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1: &[u8] = concat!(
    "zenodex.zrpf.spot_v7.firecracker.authority_input_profile.v1\n",
    "manifest_magic=ZSV7AIM1\n",
    "manifest_bytes=256\n",
    "manifest_version=1\n",
    "manifest_endian=big\n",
    "image_id_word_endian=little\n",
    "manifest_layout=magic:u8x8,version:u16,bytes:u16,flags:u32,profile:u8x32,runtime_profile:u8x32,v7_image_id:u32lex8,v6_image_id:u32lex8,v7_receipt_bytes:u32,v7_receipt_sha256:u8x32,v7_guest_input_bytes:u32,v7_guest_input_sha256:u8x32,v6_receipt_bytes:u32,v6_receipt_sha256:u8x32,reserved:u8x4\n",
    "artifact_names=spot-v7-authority-input.bin,spot-v7.receipt.json,spot-v7.guest-input.bin,spot-v6.receipt.json\n",
    "v7_receipt_max_bytes=16777216\n",
    "v7_guest_input_max_bytes=16777216\n",
    "v6_receipt_max_bytes=16777216\n",
    "runtime_profile_sha256=c8cf02b22988315b667c8b37675b6c8d8cd56f5638b8aa176357a044a89fcdd6\n",
    "request_settlement_intent_binding=authority_input_manifest_sha256\n",
    "verification=governed_spot_v7_verifier_once\n",
    "output=derived_spot_v7_verifier_output_v1\n",
    "authority=disabled_until_final_images_release_runner_store\n",
)
.as_bytes();

// SHA-256 of the exact descriptor above. Independent Rust and Python vectors
// check this value before the profile can enter a governed runtime manifest.
pub const SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1: [u8; 32] = [
    0x8c, 0x62, 0x4e, 0x6d, 0x6e, 0xd5, 0xe1, 0xf9, 0x7b, 0xc8, 0xb6, 0xde, 0x92, 0xe9, 0xff, 0x59,
    0x02, 0xc8, 0xba, 0x65, 0xd7, 0x16, 0x98, 0x4d, 0xa2, 0xf5, 0x62, 0x1f, 0xaa, 0xf8, 0xd5, 0x3a,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpotV7FirecrackerAuthorityInputErrorV1 {
    ManifestLength,
    ManifestMagic,
    ManifestVersion,
    ManifestFlags,
    ManifestProfile,
    ManifestRuntimeProfile,
    ManifestReserved,
    V7ImageIdUnmaterialized,
    V6ImageIdUnmaterialized,
    V7ImageIdMismatch,
    V6ImageIdMismatch,
    V7ReceiptLength,
    GuestInputLength,
    V6ReceiptLength,
    V7ReceiptBinding,
    GuestInputBinding,
    V6ReceiptBinding,
}

impl SpotV7FirecrackerAuthorityInputErrorV1 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::ManifestLength => "authority_manifest_length",
            Self::ManifestMagic => "authority_manifest_magic",
            Self::ManifestVersion => "authority_manifest_version",
            Self::ManifestFlags => "authority_manifest_flags",
            Self::ManifestProfile => "authority_manifest_profile",
            Self::ManifestRuntimeProfile => "authority_manifest_runtime_profile",
            Self::ManifestReserved => "authority_manifest_reserved",
            Self::V7ImageIdUnmaterialized => "authority_v7_image_id_unmaterialized",
            Self::V6ImageIdUnmaterialized => "authority_v6_image_id_unmaterialized",
            Self::V7ImageIdMismatch => "authority_v7_image_id_mismatch",
            Self::V6ImageIdMismatch => "authority_v6_image_id_mismatch",
            Self::V7ReceiptLength => "authority_v7_receipt_length",
            Self::GuestInputLength => "authority_guest_input_length",
            Self::V6ReceiptLength => "authority_v6_receipt_length",
            Self::V7ReceiptBinding => "authority_v7_receipt_binding",
            Self::GuestInputBinding => "authority_guest_input_binding",
            Self::V6ReceiptBinding => "authority_v6_receipt_binding",
        }
    }
}

impl fmt::Display for SpotV7FirecrackerAuthorityInputErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.code())
    }
}

impl std::error::Error for SpotV7FirecrackerAuthorityInputErrorV1 {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpotV7FirecrackerAuthorityInputManifestV1 {
    v7_image_id: [u32; 8],
    v6_image_id: [u32; 8],
    v7_receipt_length: u32,
    v7_receipt_sha256: [u8; 32],
    guest_input_length: u32,
    guest_input_sha256: [u8; 32],
    v6_receipt_length: u32,
    v6_receipt_sha256: [u8; 32],
}

struct AuthorityManifestFieldsV1 {
    v7_image_id: [u32; 8],
    v6_image_id: [u32; 8],
    v7_receipt_length: u32,
    v7_receipt_sha256: [u8; 32],
    guest_input_length: u32,
    guest_input_sha256: [u8; 32],
    v6_receipt_length: u32,
    v6_receipt_sha256: [u8; 32],
}

impl SpotV7FirecrackerAuthorityInputManifestV1 {
    pub fn new(
        v7_image_id: [u32; 8],
        v6_image_id: [u32; 8],
        v7_receipt_bytes: &[u8],
        guest_input_bytes: &[u8],
        v6_receipt_bytes: &[u8],
    ) -> Result<Self, SpotV7FirecrackerAuthorityInputErrorV1> {
        Self::from_fields(AuthorityManifestFieldsV1 {
            v7_image_id,
            v6_image_id,
            v7_receipt_length: bounded_length(
                v7_receipt_bytes.len(),
                SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V7_RECEIPT_BYTES_V1,
                SpotV7FirecrackerAuthorityInputErrorV1::V7ReceiptLength,
            )?,
            v7_receipt_sha256: sha256(v7_receipt_bytes),
            guest_input_length: bounded_length(
                guest_input_bytes.len(),
                SPOT_V7_FIRECRACKER_AUTHORITY_MAX_GUEST_INPUT_BYTES_V1,
                SpotV7FirecrackerAuthorityInputErrorV1::GuestInputLength,
            )?,
            guest_input_sha256: sha256(guest_input_bytes),
            v6_receipt_length: bounded_length(
                v6_receipt_bytes.len(),
                SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V6_RECEIPT_BYTES_V1,
                SpotV7FirecrackerAuthorityInputErrorV1::V6ReceiptLength,
            )?,
            v6_receipt_sha256: sha256(v6_receipt_bytes),
        })
    }

    fn from_fields(
        fields: AuthorityManifestFieldsV1,
    ) -> Result<Self, SpotV7FirecrackerAuthorityInputErrorV1> {
        require_materialized_image_id(
            fields.v7_image_id,
            SpotV7FirecrackerAuthorityInputErrorV1::V7ImageIdUnmaterialized,
        )?;
        require_materialized_image_id(
            fields.v6_image_id,
            SpotV7FirecrackerAuthorityInputErrorV1::V6ImageIdUnmaterialized,
        )?;
        require_declared_length(
            fields.v7_receipt_length,
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V7_RECEIPT_BYTES_V1,
            SpotV7FirecrackerAuthorityInputErrorV1::V7ReceiptLength,
        )?;
        require_digest(
            fields.v7_receipt_sha256,
            SpotV7FirecrackerAuthorityInputErrorV1::V7ReceiptBinding,
        )?;
        require_declared_length(
            fields.guest_input_length,
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_GUEST_INPUT_BYTES_V1,
            SpotV7FirecrackerAuthorityInputErrorV1::GuestInputLength,
        )?;
        require_digest(
            fields.guest_input_sha256,
            SpotV7FirecrackerAuthorityInputErrorV1::GuestInputBinding,
        )?;
        require_declared_length(
            fields.v6_receipt_length,
            SPOT_V7_FIRECRACKER_AUTHORITY_MAX_V6_RECEIPT_BYTES_V1,
            SpotV7FirecrackerAuthorityInputErrorV1::V6ReceiptLength,
        )?;
        require_digest(
            fields.v6_receipt_sha256,
            SpotV7FirecrackerAuthorityInputErrorV1::V6ReceiptBinding,
        )?;
        Ok(Self {
            v7_image_id: fields.v7_image_id,
            v6_image_id: fields.v6_image_id,
            v7_receipt_length: fields.v7_receipt_length,
            v7_receipt_sha256: fields.v7_receipt_sha256,
            guest_input_length: fields.guest_input_length,
            guest_input_sha256: fields.guest_input_sha256,
            v6_receipt_length: fields.v6_receipt_length,
            v6_receipt_sha256: fields.v6_receipt_sha256,
        })
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, SpotV7FirecrackerAuthorityInputErrorV1> {
        if bytes.len() != SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1 {
            return Err(SpotV7FirecrackerAuthorityInputErrorV1::ManifestLength);
        }
        if &bytes[0..8] != MANIFEST_MAGIC_V1 {
            return Err(SpotV7FirecrackerAuthorityInputErrorV1::ManifestMagic);
        }
        if read_u16_be(bytes, 8)? != MANIFEST_VERSION_V1
            || read_u16_be(bytes, 10)? != MANIFEST_BYTES_FIELD_V1
        {
            return Err(SpotV7FirecrackerAuthorityInputErrorV1::ManifestVersion);
        }
        if read_u32_be(bytes, 12)? != 0 {
            return Err(SpotV7FirecrackerAuthorityInputErrorV1::ManifestFlags);
        }
        if array_32(bytes, 16)? != SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1 {
            return Err(SpotV7FirecrackerAuthorityInputErrorV1::ManifestProfile);
        }
        if array_32(bytes, 48)? != SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1 {
            return Err(SpotV7FirecrackerAuthorityInputErrorV1::ManifestRuntimeProfile);
        }
        if bytes[252..].iter().any(|byte| *byte != 0) {
            return Err(SpotV7FirecrackerAuthorityInputErrorV1::ManifestReserved);
        }
        Self::from_fields(AuthorityManifestFieldsV1 {
            v7_image_id: read_image_id(bytes, 80)?,
            v6_image_id: read_image_id(bytes, 112)?,
            v7_receipt_length: read_u32_be(bytes, 144)?,
            v7_receipt_sha256: array_32(bytes, 148)?,
            guest_input_length: read_u32_be(bytes, 180)?,
            guest_input_sha256: array_32(bytes, 184)?,
            v6_receipt_length: read_u32_be(bytes, 216)?,
            v6_receipt_sha256: array_32(bytes, 220)?,
        })
    }

    pub fn encode(&self) -> [u8; SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1] {
        let mut bytes = [0_u8; SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_MANIFEST_BYTES_V1];
        bytes[0..8].copy_from_slice(MANIFEST_MAGIC_V1);
        bytes[8..10].copy_from_slice(&MANIFEST_VERSION_V1.to_be_bytes());
        bytes[10..12].copy_from_slice(&MANIFEST_BYTES_FIELD_V1.to_be_bytes());
        bytes[16..48].copy_from_slice(&SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_SHA256_V1);
        bytes[48..80].copy_from_slice(&SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1);
        write_image_id(&mut bytes[80..112], self.v7_image_id);
        write_image_id(&mut bytes[112..144], self.v6_image_id);
        bytes[144..148].copy_from_slice(&self.v7_receipt_length.to_be_bytes());
        bytes[148..180].copy_from_slice(&self.v7_receipt_sha256);
        bytes[180..184].copy_from_slice(&self.guest_input_length.to_be_bytes());
        bytes[184..216].copy_from_slice(&self.guest_input_sha256);
        bytes[216..220].copy_from_slice(&self.v6_receipt_length.to_be_bytes());
        bytes[220..252].copy_from_slice(&self.v6_receipt_sha256);
        bytes
    }

    pub fn validate_artifacts(
        &self,
        v7_receipt_bytes: &[u8],
        guest_input_bytes: &[u8],
        v6_receipt_bytes: &[u8],
    ) -> Result<(), SpotV7FirecrackerAuthorityInputErrorV1> {
        require_artifact(
            v7_receipt_bytes,
            self.v7_receipt_length,
            self.v7_receipt_sha256,
            SpotV7FirecrackerAuthorityInputErrorV1::V7ReceiptBinding,
        )?;
        require_artifact(
            guest_input_bytes,
            self.guest_input_length,
            self.guest_input_sha256,
            SpotV7FirecrackerAuthorityInputErrorV1::GuestInputBinding,
        )?;
        require_artifact(
            v6_receipt_bytes,
            self.v6_receipt_length,
            self.v6_receipt_sha256,
            SpotV7FirecrackerAuthorityInputErrorV1::V6ReceiptBinding,
        )
    }

    pub fn require_governed_image_ids(
        &self,
        governed_v7_image_id: [u32; 8],
        governed_v6_image_id: [u32; 8],
    ) -> Result<(), SpotV7FirecrackerAuthorityInputErrorV1> {
        require_materialized_image_id(
            governed_v7_image_id,
            SpotV7FirecrackerAuthorityInputErrorV1::V7ImageIdUnmaterialized,
        )?;
        require_materialized_image_id(
            governed_v6_image_id,
            SpotV7FirecrackerAuthorityInputErrorV1::V6ImageIdUnmaterialized,
        )?;
        if self.v7_image_id != governed_v7_image_id {
            return Err(SpotV7FirecrackerAuthorityInputErrorV1::V7ImageIdMismatch);
        }
        if self.v6_image_id != governed_v6_image_id {
            return Err(SpotV7FirecrackerAuthorityInputErrorV1::V6ImageIdMismatch);
        }
        Ok(())
    }

    pub const fn v7_image_id(&self) -> [u32; 8] {
        self.v7_image_id
    }

    pub const fn v6_image_id(&self) -> [u32; 8] {
        self.v6_image_id
    }

    pub const fn runtime_profile_sha256(&self) -> [u8; 32] {
        SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
    }

    pub fn sha256(&self) -> [u8; 32] {
        sha256(&self.encode())
    }
}

fn bounded_length(
    length: usize,
    maximum: usize,
    error: SpotV7FirecrackerAuthorityInputErrorV1,
) -> Result<u32, SpotV7FirecrackerAuthorityInputErrorV1> {
    if length == 0 || length > maximum {
        return Err(error);
    }
    u32::try_from(length).map_err(|_| error)
}

fn require_declared_length(
    length: u32,
    maximum: usize,
    error: SpotV7FirecrackerAuthorityInputErrorV1,
) -> Result<(), SpotV7FirecrackerAuthorityInputErrorV1> {
    let length = usize::try_from(length).map_err(|_| error)?;
    if length == 0 || length > maximum {
        return Err(error);
    }
    Ok(())
}

fn require_materialized_image_id(
    image_id: [u32; 8],
    error: SpotV7FirecrackerAuthorityInputErrorV1,
) -> Result<(), SpotV7FirecrackerAuthorityInputErrorV1> {
    if image_id.iter().all(|word| *word == 0) {
        return Err(error);
    }
    Ok(())
}

fn require_digest(
    digest: [u8; 32],
    error: SpotV7FirecrackerAuthorityInputErrorV1,
) -> Result<(), SpotV7FirecrackerAuthorityInputErrorV1> {
    if digest.iter().all(|byte| *byte == 0) {
        return Err(error);
    }
    Ok(())
}

fn require_artifact(
    bytes: &[u8],
    expected_length: u32,
    expected_sha256: [u8; 32],
    error: SpotV7FirecrackerAuthorityInputErrorV1,
) -> Result<(), SpotV7FirecrackerAuthorityInputErrorV1> {
    if usize::try_from(expected_length).ok() != Some(bytes.len())
        || sha256(bytes) != expected_sha256
    {
        return Err(error);
    }
    Ok(())
}

fn read_image_id(
    bytes: &[u8],
    offset: usize,
) -> Result<[u32; 8], SpotV7FirecrackerAuthorityInputErrorV1> {
    let mut output = [0_u32; 8];
    for (index, word) in output.iter_mut().enumerate() {
        let start = offset
            .checked_add(index * 4)
            .ok_or(SpotV7FirecrackerAuthorityInputErrorV1::ManifestLength)?;
        let raw: [u8; 4] = bytes
            .get(start..start + 4)
            .ok_or(SpotV7FirecrackerAuthorityInputErrorV1::ManifestLength)?
            .try_into()
            .map_err(|_| SpotV7FirecrackerAuthorityInputErrorV1::ManifestLength)?;
        *word = u32::from_le_bytes(raw);
    }
    Ok(output)
}

fn write_image_id(output: &mut [u8], image_id: [u32; 8]) {
    for (chunk, word) in output.chunks_exact_mut(4).zip(image_id) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
}

fn read_u16_be(bytes: &[u8], offset: usize) -> Result<u16, SpotV7FirecrackerAuthorityInputErrorV1> {
    bytes
        .get(offset..offset + 2)
        .ok_or(SpotV7FirecrackerAuthorityInputErrorV1::ManifestLength)?
        .try_into()
        .map(u16::from_be_bytes)
        .map_err(|_| SpotV7FirecrackerAuthorityInputErrorV1::ManifestLength)
}

fn read_u32_be(bytes: &[u8], offset: usize) -> Result<u32, SpotV7FirecrackerAuthorityInputErrorV1> {
    bytes
        .get(offset..offset + 4)
        .ok_or(SpotV7FirecrackerAuthorityInputErrorV1::ManifestLength)?
        .try_into()
        .map(u32::from_be_bytes)
        .map_err(|_| SpotV7FirecrackerAuthorityInputErrorV1::ManifestLength)
}

fn array_32(
    bytes: &[u8],
    offset: usize,
) -> Result<[u8; 32], SpotV7FirecrackerAuthorityInputErrorV1> {
    bytes
        .get(offset..offset + 32)
        .ok_or(SpotV7FirecrackerAuthorityInputErrorV1::ManifestLength)?
        .try_into()
        .map_err(|_| SpotV7FirecrackerAuthorityInputErrorV1::ManifestLength)
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
