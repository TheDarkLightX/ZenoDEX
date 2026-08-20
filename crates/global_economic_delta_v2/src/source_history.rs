//! Canonical statement boundary for source-history claims.
//!
//! A checked statement is a canonical claim about source occurrence identity,
//! finality, and nullifier absence at one history root. Checking this statement
//! creates no proof authority.

use std::collections::BTreeSet;
use std::fmt;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::model::{CanonicalIdV2, JsonAtomsV2, RootV2, SourceKindV2};
use crate::{require_delta_atoms_v2, sorted_json_v2, StructurallyValidDeltaPlanV2};

pub const SOURCE_HISTORY_SCHEMA_V2: &str = "zenodex/global-economic-source-history-statement/v2";
pub const MAX_SOURCE_HISTORY_INPUT_BYTES_V2: usize = 1_048_576;

const STATEMENT_ROOT_DOMAIN_V2: &[u8] = b"zenodex:global-economic-source-history-statement:v2\0";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceHistoryRejectCodeV2 {
    DecodeInvalid,
    SchemaMismatch,
    InputTooLarge,
    WriterEpochInvalid,
    SourceCountMismatch,
    DuplicateSourceClaim,
    NoncanonicalSourceOrder,
    SourceBindingMismatch,
    DuplicateOccurrence,
    DuplicateConsumptionNullifier,
    RootRoleConflict,
    FinalityOrderInvalid,
    DeltaPlanRootMismatch,
    VerifierReleaseMismatch,
    VerifierImageMismatch,
    ReceiptEmpty,
    ReceiptTooLarge,
    ReceiptRejected,
    CanonicalEncodingFailed,
}

impl SourceHistoryRejectCodeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::DecodeInvalid => "DECODE_INVALID",
            Self::SchemaMismatch => "SCHEMA_MISMATCH",
            Self::InputTooLarge => "INPUT_TOO_LARGE",
            Self::WriterEpochInvalid => "WRITER_EPOCH_INVALID",
            Self::SourceCountMismatch => "SOURCE_COUNT_MISMATCH",
            Self::DuplicateSourceClaim => "DUPLICATE_SOURCE_CLAIM",
            Self::NoncanonicalSourceOrder => "NONCANONICAL_SOURCE_ORDER",
            Self::SourceBindingMismatch => "SOURCE_BINDING_MISMATCH",
            Self::DuplicateOccurrence => "DUPLICATE_OCCURRENCE",
            Self::DuplicateConsumptionNullifier => "DUPLICATE_CONSUMPTION_NULLIFIER",
            Self::RootRoleConflict => "ROOT_ROLE_CONFLICT",
            Self::FinalityOrderInvalid => "FINALITY_ORDER_INVALID",
            Self::DeltaPlanRootMismatch => "DELTA_PLAN_ROOT_MISMATCH",
            Self::VerifierReleaseMismatch => "VERIFIER_RELEASE_MISMATCH",
            Self::VerifierImageMismatch => "VERIFIER_IMAGE_MISMATCH",
            Self::ReceiptEmpty => "RECEIPT_EMPTY",
            Self::ReceiptTooLarge => "RECEIPT_TOO_LARGE",
            Self::ReceiptRejected => "RECEIPT_REJECTED",
            Self::CanonicalEncodingFailed => "CANONICAL_ENCODING_FAILED",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceHistoryRejectV2 {
    pub code: SourceHistoryRejectCodeV2,
    pub detail: String,
}

impl fmt::Display for SourceHistoryRejectV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.code.as_str(), self.detail)
    }
}

impl std::error::Error for SourceHistoryRejectV2 {}

pub(crate) type SourceHistoryResultV2<T> = Result<T, SourceHistoryRejectV2>;

pub(crate) fn reject_history_v2(
    code: SourceHistoryRejectCodeV2,
    detail: impl Into<String>,
) -> SourceHistoryRejectV2 {
    SourceHistoryRejectV2 {
        code,
        detail: detail.into(),
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct SourceAvailabilityClaimV2 {
    source_root: RootV2,
    source_kind: SourceKindV2,
    asset: CanonicalIdV2,
    amount_atoms: JsonAtomsV2,
    source_height: u64,
    tx_index: u32,
    op_index: u32,
    finality_anchor_root: RootV2,
    finalized_height: u64,
    consumption_nullifier: RootV2,
}

impl SourceAvailabilityClaimV2 {
    fn source_root(&self) -> &str {
        self.source_root.as_str()
    }

    fn occurrence(&self) -> (u64, u32, u32) {
        (self.source_height, self.tx_index, self.op_index)
    }

    fn amount_atoms(&self) -> SourceHistoryResultV2<u128> {
        self.amount_atoms.as_u128().map_err(|error| {
            reject_history_v2(SourceHistoryRejectCodeV2::DecodeInvalid, error.to_string())
        })
    }

    fn validate(&self, history_height: u64) -> SourceHistoryResultV2<()> {
        let amount_atoms = self.amount_atoms()?;
        require_delta_atoms_v2(amount_atoms).map_err(|error| {
            reject_history_v2(SourceHistoryRejectCodeV2::DecodeInvalid, error.to_string())
        })?;
        if self.source_height > self.finalized_height || self.finalized_height > history_height {
            return Err(reject_history_v2(
                SourceHistoryRejectCodeV2::FinalityOrderInvalid,
                "source height must not exceed finality height or committed history height",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
struct RawSourceHistoryStatementV2 {
    schema: String,
    chain_id: CanonicalIdV2,
    deployment_root: RootV2,
    profile_root: RootV2,
    writer_epoch: u64,
    history_root: RootV2,
    history_height: u64,
    delta_plan_root: RootV2,
    verifier_release_id: RootV2,
    verifier_image_id: RootV2,
    source_availability_claims: Vec<SourceAvailabilityClaimV2>,
}

/// Canonical statement checked against one exact structural delta plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckedSourceHistoryStatementV2 {
    statement: RawSourceHistoryStatementV2,
    canonical_bytes: Vec<u8>,
    root: String,
}

impl CheckedSourceHistoryStatementV2 {
    pub fn chain_id(&self) -> &str {
        self.statement.chain_id.as_str()
    }

    pub fn deployment_root(&self) -> &str {
        self.statement.deployment_root.as_str()
    }

    pub fn profile_root(&self) -> &str {
        self.statement.profile_root.as_str()
    }

    pub fn source_claim_count(&self) -> usize {
        self.statement.source_availability_claims.len()
    }

    pub fn delta_plan_root(&self) -> &str {
        self.statement.delta_plan_root.as_str()
    }

    pub fn history_root(&self) -> &str {
        self.statement.history_root.as_str()
    }

    pub fn history_height(&self) -> u64 {
        self.statement.history_height
    }

    pub fn writer_epoch(&self) -> u64 {
        self.statement.writer_epoch
    }

    pub fn verifier_release_id(&self) -> &str {
        self.statement.verifier_release_id.as_str()
    }

    pub fn verifier_image_id(&self) -> &str {
        self.statement.verifier_image_id.as_str()
    }

    pub fn canonical_bytes(&self) -> &[u8] {
        &self.canonical_bytes
    }

    pub fn root(&self) -> &str {
        &self.root
    }
}

fn canonical_statement_bytes_v2(
    statement: &RawSourceHistoryStatementV2,
) -> SourceHistoryResultV2<Vec<u8>> {
    let value = serde_json::to_value(statement).map_err(|_| {
        reject_history_v2(
            SourceHistoryRejectCodeV2::CanonicalEncodingFailed,
            "source-history statement cannot be projected to canonical JSON",
        )
    })?;
    let mut bytes = serde_json::to_vec(&sorted_json_v2(value)).map_err(|_| {
        reject_history_v2(
            SourceHistoryRejectCodeV2::CanonicalEncodingFailed,
            "source-history canonical JSON cannot be encoded",
        )
    })?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn domain_hash_v2(domain: &[u8], bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(bytes);
    format!("sha256:{}", hex::encode(hasher.finalize()))
}

fn validate_claim_sets_v2(
    claims: &[SourceAvailabilityClaimV2],
    history_height: u64,
) -> SourceHistoryResultV2<()> {
    let mut roots = BTreeSet::new();
    let mut finality_anchors = BTreeSet::new();
    let mut occurrences = BTreeSet::new();
    let mut nullifiers = BTreeSet::new();
    for claim in claims {
        claim.validate(history_height)?;
        if !roots.insert(claim.source_root()) {
            return Err(reject_history_v2(
                SourceHistoryRejectCodeV2::DuplicateSourceClaim,
                "source-history claim roots must be unique",
            ));
        }
        if !occurrences.insert(claim.occurrence()) {
            return Err(reject_history_v2(
                SourceHistoryRejectCodeV2::DuplicateOccurrence,
                "canonical source occurrence coordinates must be unique",
            ));
        }
        if !nullifiers.insert(claim.consumption_nullifier.as_str()) {
            return Err(reject_history_v2(
                SourceHistoryRejectCodeV2::DuplicateConsumptionNullifier,
                "consumption nullifiers must be unique",
            ));
        }
        finality_anchors.insert(claim.finality_anchor_root.as_str());
    }
    if !roots.is_disjoint(&nullifiers)
        || !roots.is_disjoint(&finality_anchors)
        || !nullifiers.is_disjoint(&finality_anchors)
    {
        return Err(reject_history_v2(
            SourceHistoryRejectCodeV2::RootRoleConflict,
            "source, finality-anchor, and consumption-nullifier root roles must be disjoint",
        ));
    }
    Ok(())
}

fn validate_claim_order_v2(claims: &[SourceAvailabilityClaimV2]) -> SourceHistoryResultV2<()> {
    if !claims
        .windows(2)
        .all(|pair| pair[0].source_root() < pair[1].source_root())
    {
        return Err(reject_history_v2(
            SourceHistoryRejectCodeV2::NoncanonicalSourceOrder,
            "source-history claims must be ordered by source root",
        ));
    }
    Ok(())
}

fn validate_exact_bindings_v2(
    plan: &StructurallyValidDeltaPlanV2,
    claims: &[SourceAvailabilityClaimV2],
) -> SourceHistoryResultV2<()> {
    for (binding, claim) in plan.source_bindings().iter().zip(claims) {
        let amount = claim.amount_atoms()?;
        if binding.root() != claim.source_root()
            || binding.kind() != claim.source_kind
            || binding.asset().as_str() != claim.asset.as_str()
            || binding.amount_atoms().map_err(|error| {
                reject_history_v2(SourceHistoryRejectCodeV2::DecodeInvalid, error.to_string())
            })? != amount
        {
            return Err(reject_history_v2(
                SourceHistoryRejectCodeV2::SourceBindingMismatch,
                "source root, kind, asset, and amount must equal the delta-plan binding",
            ));
        }
    }
    Ok(())
}

fn validate_source_claims_v2(
    plan: &StructurallyValidDeltaPlanV2,
    statement: &RawSourceHistoryStatementV2,
) -> SourceHistoryResultV2<()> {
    let claims = &statement.source_availability_claims;
    if claims.len() != plan.source_binding_count() {
        return Err(reject_history_v2(
            SourceHistoryRejectCodeV2::SourceCountMismatch,
            "source-history claims must have the exact plan source-binding cardinality",
        ));
    }
    validate_claim_sets_v2(claims, statement.history_height)?;
    validate_claim_order_v2(claims)?;
    validate_exact_bindings_v2(plan, claims)
}

/// Decode and bind one source-history statement to an exact structural plan.
///
/// This operation checks a claim. It does not establish history inclusion,
/// finality, or nullifier absence and therefore creates no authority witness.
#[must_use = "source-history statement validation must be inspected"]
pub fn decode_source_history_statement_v2(
    plan: &StructurallyValidDeltaPlanV2,
    input: &[u8],
) -> SourceHistoryResultV2<CheckedSourceHistoryStatementV2> {
    if input.len() > MAX_SOURCE_HISTORY_INPUT_BYTES_V2 {
        return Err(reject_history_v2(
            SourceHistoryRejectCodeV2::InputTooLarge,
            "source-history statement exceeds the byte limit",
        ));
    }
    let statement: RawSourceHistoryStatementV2 =
        serde_json::from_slice(input).map_err(|error| {
            reject_history_v2(
                SourceHistoryRejectCodeV2::DecodeInvalid,
                format!("input is not one closed V2 source-history statement: {error}"),
            )
        })?;
    if statement.schema != SOURCE_HISTORY_SCHEMA_V2 {
        return Err(reject_history_v2(
            SourceHistoryRejectCodeV2::SchemaMismatch,
            "source-history statement schema is not V2",
        ));
    }
    if statement.writer_epoch == 0 {
        return Err(reject_history_v2(
            SourceHistoryRejectCodeV2::WriterEpochInvalid,
            "writer epoch must be positive",
        ));
    }
    if statement.delta_plan_root.as_str() != plan.root() {
        return Err(reject_history_v2(
            SourceHistoryRejectCodeV2::DeltaPlanRootMismatch,
            "source-history statement names a different delta plan",
        ));
    }
    validate_source_claims_v2(plan, &statement)?;
    let canonical_bytes = canonical_statement_bytes_v2(&statement)?;
    let root = domain_hash_v2(STATEMENT_ROOT_DOMAIN_V2, &canonical_bytes);
    Ok(CheckedSourceHistoryStatementV2 {
        statement,
        canonical_bytes,
        root,
    })
}
