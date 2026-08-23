//! Research-only logical-set oracle for V2 economic object nullifiers.
//!
//! This crate exposes no verifier, proof, publication, persistence, release,
//! or settlement port. Its digest is reference evidence, not an ABI root.

use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

pub const REFERENCE_SCHEMA_V2: &str = "zenodex/global-economic-object-nullifier-reference/v2";
pub const MAX_REFERENCE_NULLIFIERS_V2: usize = 4_096;
pub const MAX_REFERENCE_CLAIMS_PER_STEP_V2: usize = 64;
pub const MAX_REFERENCE_ARCHIVE_BYTES_V2: usize = 1_048_576;

const REFERENCE_DIGEST_PREFIX_V2: &[u8] = b"global-economic-object-nullifier-reference\x002\x00";

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ReferenceObjectIdV2 {
    value: String,
    decoded: [u8; 32],
}

impl ReferenceObjectIdV2 {
    pub fn new(value: &str) -> Result<Self, &'static str> {
        let decoded = decode_reference_id_v2(value, "invalid object identifier")?;
        Ok(Self {
            value: value.to_owned(),
            decoded,
        })
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.value
    }

    fn decoded_bytes(&self) -> [u8; 32] {
        self.decoded
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceOccurrenceIdV2 {
    value: String,
}

impl ReferenceOccurrenceIdV2 {
    pub fn new(value: &str) -> Result<Self, &'static str> {
        decode_reference_id_v2(value, "invalid occurrence identifier")?;
        Ok(Self {
            value: value.to_owned(),
        })
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.value
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceConsumptionClaimV2 {
    pub object_id: ReferenceObjectIdV2,
    pub consumed_by_occurrence_id: ReferenceOccurrenceIdV2,
}

impl ReferenceConsumptionClaimV2 {
    #[must_use]
    pub fn new(
        object_id: ReferenceObjectIdV2,
        consumed_by_occurrence_id: ReferenceOccurrenceIdV2,
    ) -> Self {
        Self {
            object_id,
            consumed_by_occurrence_id,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceNullifierEntryV2 {
    pub object_id: ReferenceObjectIdV2,
    pub first_consumed_by_occurrence_id: ReferenceOccurrenceIdV2,
}

impl ReferenceNullifierEntryV2 {
    #[must_use]
    pub fn new(
        object_id: ReferenceObjectIdV2,
        first_consumed_by_occurrence_id: ReferenceOccurrenceIdV2,
    ) -> Self {
        Self {
            object_id,
            first_consumed_by_occurrence_id,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalReferenceNullifierArchiveV2 {
    entries: Vec<ReferenceNullifierEntryV2>,
}

impl CanonicalReferenceNullifierArchiveV2 {
    pub fn new(entries: Vec<ReferenceNullifierEntryV2>) -> Result<Self, &'static str> {
        if entries.len() > MAX_REFERENCE_NULLIFIERS_V2 {
            return Err("reference archive exceeds entry capacity");
        }
        if entries
            .windows(2)
            .any(|pair| pair[0].object_id >= pair[1].object_id)
        {
            return Err("reference archive entries must be strictly sorted and unique");
        }
        let archive = Self { entries };
        if canonical_reference_archive_bytes_v2(&archive).len() > MAX_REFERENCE_ARCHIVE_BYTES_V2 {
            return Err("reference archive exceeds canonical byte limit");
        }
        Ok(archive)
    }

    #[must_use]
    pub fn empty() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    #[must_use]
    pub fn entries(&self) -> &[ReferenceNullifierEntryV2] {
        &self.entries
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReferenceRejectCodeV2 {
    ReferenceStepLimitExceeded,
    ReferenceDuplicateInBatch,
    ReferenceAlreadyConsumed,
    ReferenceArchiveCapacityExceeded,
    ReferenceArchiveByteLimitExceeded,
}

impl ReferenceRejectCodeV2 {
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ReferenceStepLimitExceeded => "REFERENCE_STEP_LIMIT_EXCEEDED",
            Self::ReferenceDuplicateInBatch => "REFERENCE_DUPLICATE_IN_BATCH",
            Self::ReferenceAlreadyConsumed => "REFERENCE_ALREADY_CONSUMED",
            Self::ReferenceArchiveCapacityExceeded => "REFERENCE_ARCHIVE_CAPACITY_EXCEEDED",
            Self::ReferenceArchiveByteLimitExceeded => "REFERENCE_ARCHIVE_BYTE_LIMIT_EXCEEDED",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceAcceptedV2 {
    pre_reference_archive_digest: String,
    post_archive: CanonicalReferenceNullifierArchiveV2,
}

impl ReferenceAcceptedV2 {
    #[must_use]
    pub fn pre_reference_archive_digest(&self) -> &str {
        &self.pre_reference_archive_digest
    }

    #[must_use]
    pub fn post_archive(&self) -> &CanonicalReferenceNullifierArchiveV2 {
        &self.post_archive
    }

    #[must_use]
    pub fn post_reference_archive_digest(&self) -> String {
        reference_archive_digest_v2(&self.post_archive)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceRejectedV2 {
    code: ReferenceRejectCodeV2,
    pre_reference_archive_digest: String,
    diagnostic: &'static str,
}

impl ReferenceRejectedV2 {
    #[must_use]
    pub fn code(&self) -> ReferenceRejectCodeV2 {
        self.code
    }

    #[must_use]
    pub fn pre_reference_archive_digest(&self) -> &str {
        &self.pre_reference_archive_digest
    }

    #[must_use]
    pub fn diagnostic(&self) -> &'static str {
        self.diagnostic
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReferenceResultV2 {
    Accepted(ReferenceAcceptedV2),
    Rejected(ReferenceRejectedV2),
}

#[must_use]
pub fn canonical_reference_archive_bytes_v2(
    archive: &CanonicalReferenceNullifierArchiveV2,
) -> Vec<u8> {
    let mut output = Vec::with_capacity(128 + archive.entries.len() * 180);
    output.extend_from_slice(b"{\"entries\":[");
    for (index, entry) in archive.entries.iter().enumerate() {
        if index != 0 {
            output.push(b',');
        }
        output.extend_from_slice(b"{\"first_consumed_by_occurrence_id\":\"");
        output.extend_from_slice(entry.first_consumed_by_occurrence_id.as_str().as_bytes());
        output.extend_from_slice(b"\",\"object_id\":\"");
        output.extend_from_slice(entry.object_id.as_str().as_bytes());
        output.extend_from_slice(b"\"}");
    }
    output.extend_from_slice(b"],\"schema\":\"");
    output.extend_from_slice(REFERENCE_SCHEMA_V2.as_bytes());
    output.extend_from_slice(b"\"}");
    output
}

#[must_use]
pub fn reference_archive_digest_v2(archive: &CanonicalReferenceNullifierArchiveV2) -> String {
    let mut hasher = Sha256::new();
    hasher.update(REFERENCE_DIGEST_PREFIX_V2);
    hasher.update(canonical_reference_archive_bytes_v2(archive));
    let digest = hasher.finalize();
    let mut rendered = String::with_capacity(66);
    rendered.push_str("0x");
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in digest {
        rendered.push(char::from(HEX[usize::from(byte >> 4)]));
        rendered.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    rendered
}

#[must_use]
pub fn apply_reference_object_nullifiers_v2(
    pre_archive: &CanonicalReferenceNullifierArchiveV2,
    claims: &[ReferenceConsumptionClaimV2],
) -> ReferenceResultV2 {
    if claims.len() > MAX_REFERENCE_CLAIMS_PER_STEP_V2 {
        return rejected(
            pre_archive,
            ReferenceRejectCodeV2::ReferenceStepLimitExceeded,
            "reference step claim count exceeds 64",
        );
    }

    let claim_by_object = claims_by_object(claims);
    if claim_by_object.len() != claims.len() {
        return rejected(
            pre_archive,
            ReferenceRejectCodeV2::ReferenceDuplicateInBatch,
            "reference step repeats an object identifier",
        );
    }

    let consumed = consumed_object_ids(pre_archive);
    if claim_by_object
        .keys()
        .any(|object_id| consumed.contains(object_id))
    {
        return rejected(
            pre_archive,
            ReferenceRejectCodeV2::ReferenceAlreadyConsumed,
            "reference step includes a previously consumed object",
        );
    }

    if pre_archive.entries.len() + claims.len() > MAX_REFERENCE_NULLIFIERS_V2 {
        return rejected(
            pre_archive,
            ReferenceRejectCodeV2::ReferenceArchiveCapacityExceeded,
            "reference archive successor exceeds 4096 entries",
        );
    }
    if claims.is_empty() {
        return accepted_identity(pre_archive);
    }

    let candidate = match candidate_archive(pre_archive, claim_by_object) {
        Some(candidate) => candidate,
        None => {
            return rejected(
                pre_archive,
                ReferenceRejectCodeV2::ReferenceArchiveByteLimitExceeded,
                "reference archive successor exceeds canonical byte limit",
            )
        }
    };
    ReferenceResultV2::Accepted(ReferenceAcceptedV2 {
        pre_reference_archive_digest: reference_archive_digest_v2(pre_archive),
        post_archive: candidate,
    })
}

fn accepted_identity(pre_archive: &CanonicalReferenceNullifierArchiveV2) -> ReferenceResultV2 {
    ReferenceResultV2::Accepted(ReferenceAcceptedV2 {
        pre_reference_archive_digest: reference_archive_digest_v2(pre_archive),
        post_archive: pre_archive.clone(),
    })
}

fn consumed_object_ids(archive: &CanonicalReferenceNullifierArchiveV2) -> BTreeSet<[u8; 32]> {
    archive
        .entries
        .iter()
        .map(|entry| entry.object_id.decoded_bytes())
        .collect()
}

fn claims_by_object(
    claims: &[ReferenceConsumptionClaimV2],
) -> BTreeMap<[u8; 32], &ReferenceConsumptionClaimV2> {
    claims
        .iter()
        .map(|claim| (claim.object_id.decoded_bytes(), claim))
        .collect()
}

fn candidate_archive(
    pre_archive: &CanonicalReferenceNullifierArchiveV2,
    claim_by_object: BTreeMap<[u8; 32], &ReferenceConsumptionClaimV2>,
) -> Option<CanonicalReferenceNullifierArchiveV2> {
    let mut entries = pre_archive.entries.clone();
    entries.extend(claim_by_object.into_values().map(|claim| {
        ReferenceNullifierEntryV2::new(
            claim.object_id.clone(),
            claim.consumed_by_occurrence_id.clone(),
        )
    }));
    entries.sort_by(|left, right| left.object_id.cmp(&right.object_id));
    let candidate = CanonicalReferenceNullifierArchiveV2 { entries };
    if canonical_reference_archive_bytes_v2(&candidate).len() > MAX_REFERENCE_ARCHIVE_BYTES_V2 {
        return None;
    }
    Some(candidate)
}

fn rejected(
    pre_archive: &CanonicalReferenceNullifierArchiveV2,
    code: ReferenceRejectCodeV2,
    diagnostic: &'static str,
) -> ReferenceResultV2 {
    ReferenceResultV2::Rejected(ReferenceRejectedV2 {
        code,
        pre_reference_archive_digest: reference_archive_digest_v2(pre_archive),
        diagnostic,
    })
}

fn decode_reference_id_v2(value: &str, error: &'static str) -> Result<[u8; 32], &'static str> {
    let bytes = value.as_bytes();
    if bytes.len() != 66 || &bytes[..2] != b"0x" {
        return Err(error);
    }
    let mut decoded = [0_u8; 32];
    let mut nonzero = false;
    for (index, pair) in bytes[2..].chunks_exact(2).enumerate() {
        let high = lower_hex_nibble(pair[0]).ok_or(error)?;
        let low = lower_hex_nibble(pair[1]).ok_or(error)?;
        let byte = (high << 4) | low;
        decoded[index] = byte;
        nonzero |= byte != 0;
    }
    if !nonzero {
        return Err(error);
    }
    Ok(decoded)
}

fn lower_hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}
