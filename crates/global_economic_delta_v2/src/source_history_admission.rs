//! Sealed proof admission for checked source-history statements.

use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::source_history::{
    reject_history_v2, CheckedSourceHistoryStatementV2, SourceHistoryRejectCodeV2,
    SourceHistoryResultV2,
};
use crate::{sorted_json_v2, StructurallyValidDeltaPlanV2};

pub const MAX_SOURCE_HISTORY_RECEIPT_BYTES_V2: usize = 4_194_304;

const RECEIPT_DIGEST_DOMAIN_V2: &[u8] = b"zenodex:global-economic-source-history-receipt:v2\0";
const WITNESS_ROOT_DOMAIN_V2: &[u8] = b"zenodex:verified-source-history-delta-plan:v2\0";

/// Typed detail returned by an in-crate cryptographic proof backend.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceHistoryBackendRejectV2 {
    detail: String,
}

impl SourceHistoryBackendRejectV2 {
    pub fn new(detail: impl Into<String>) -> Self {
        Self {
            detail: detail.into(),
        }
    }
}

mod backend_seal {
    pub trait Sealed {}
}

/// Sealed proof-verifier port. A concrete release backend must live in this
/// crate, which prevents callers from supplying an accepting verifier.
///
/// ```compile_fail
/// use zenodex_global_economic_delta_v2::{
///     SourceHistoryBackendRejectV2, SourceHistoryProofBackendV2,
/// };
/// struct CallerSelectedVerifier;
/// impl SourceHistoryProofBackendV2 for CallerSelectedVerifier {
///     const VERIFIER_RELEASE_ID: &'static str = "sha256:1111111111111111111111111111111111111111111111111111111111111111";
///     const IMAGE_ID: &'static str = "sha256:2222222222222222222222222222222222222222222222222222222222222222";
///     fn verify_succinct_receipt(
///         &self,
///         _receipt_bytes: &[u8],
///         _expected_image_id: &str,
///         _expected_journal_bytes: &[u8],
///     ) -> Result<(), SourceHistoryBackendRejectV2> {
///         Ok(())
///     }
/// }
/// ```
pub trait SourceHistoryProofBackendV2: backend_seal::Sealed {
    const VERIFIER_RELEASE_ID: &'static str;
    const IMAGE_ID: &'static str;

    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &str,
        expected_journal_bytes: &[u8],
    ) -> Result<(), SourceHistoryBackendRejectV2>;
}

/// Opaque result owned by proof admission.
///
/// Construction is private and requires successful invocation of a sealed,
/// release-pinned backend through [`admit_source_history_v2`].
pub struct VerifiedSourceHistoryDeltaPlanV2 {
    plan: StructurallyValidDeltaPlanV2,
    statement_root: String,
    chain_id: String,
    deployment_root: String,
    profile_root: String,
    history_root: String,
    history_height: u64,
    writer_epoch: u64,
    verifier_release_id: String,
    verifier_image_id: String,
    receipt_digest: String,
    witness_root: String,
}

impl VerifiedSourceHistoryDeltaPlanV2 {
    pub fn delta_plan_root(&self) -> &str {
        self.plan.root()
    }

    pub fn source_claim_count(&self) -> usize {
        self.plan.source_binding_count()
    }

    pub fn statement_root(&self) -> &str {
        &self.statement_root
    }

    pub fn chain_id(&self) -> &str {
        &self.chain_id
    }

    pub fn deployment_root(&self) -> &str {
        &self.deployment_root
    }

    pub fn profile_root(&self) -> &str {
        &self.profile_root
    }

    pub fn history_root(&self) -> &str {
        &self.history_root
    }

    pub fn history_height(&self) -> u64 {
        self.history_height
    }

    pub fn writer_epoch(&self) -> u64 {
        self.writer_epoch
    }

    pub fn verifier_release_id(&self) -> &str {
        &self.verifier_release_id
    }

    pub fn verifier_image_id(&self) -> &str {
        &self.verifier_image_id
    }

    pub fn receipt_digest(&self) -> &str {
        &self.receipt_digest
    }

    pub fn witness_root(&self) -> &str {
        &self.witness_root
    }

    #[allow(dead_code, reason = "reserved for a future in-crate authority adapter")]
    pub(crate) fn into_structural_plan(self) -> StructurallyValidDeltaPlanV2 {
        self.plan
    }
}

#[derive(Serialize)]
struct WitnessBindingV2<'a> {
    delta_plan_root: &'a str,
    statement_root: &'a str,
    chain_id: &'a str,
    deployment_root: &'a str,
    profile_root: &'a str,
    history_root: &'a str,
    history_height: u64,
    writer_epoch: u64,
    verifier_release_id: &'a str,
    verifier_image_id: &'a str,
    receipt_digest: &'a str,
}

fn domain_hash_v2(domain: &[u8], bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(bytes);
    format!("sha256:{}", hex::encode(hasher.finalize()))
}

fn validate_admission_inputs_v2<B: SourceHistoryProofBackendV2>(
    plan: &StructurallyValidDeltaPlanV2,
    statement: &CheckedSourceHistoryStatementV2,
    receipt_bytes: &[u8],
) -> SourceHistoryResultV2<()> {
    let checks = [
        (
            statement.delta_plan_root() == plan.root(),
            SourceHistoryRejectCodeV2::DeltaPlanRootMismatch,
            "checked source-history statement no longer matches the supplied delta plan",
        ),
        (
            statement.verifier_release_id() == B::VERIFIER_RELEASE_ID,
            SourceHistoryRejectCodeV2::VerifierReleaseMismatch,
            "source-history statement names a different verifier release",
        ),
        (
            statement.verifier_image_id() == B::IMAGE_ID,
            SourceHistoryRejectCodeV2::VerifierImageMismatch,
            "source-history statement names a different verifier image",
        ),
        (
            !receipt_bytes.is_empty(),
            SourceHistoryRejectCodeV2::ReceiptEmpty,
            "source-history receipt bytes must be non-empty",
        ),
        (
            receipt_bytes.len() <= MAX_SOURCE_HISTORY_RECEIPT_BYTES_V2,
            SourceHistoryRejectCodeV2::ReceiptTooLarge,
            "source-history receipt exceeds the byte limit",
        ),
    ];
    for (accepted, code, detail) in checks {
        if !accepted {
            return Err(reject_history_v2(code, detail));
        }
    }
    Ok(())
}

fn verify_receipt_v2<B: SourceHistoryProofBackendV2>(
    statement: &CheckedSourceHistoryStatementV2,
    receipt_bytes: &[u8],
    backend: &B,
) -> SourceHistoryResultV2<()> {
    backend
        .verify_succinct_receipt(receipt_bytes, B::IMAGE_ID, statement.canonical_bytes())
        .map_err(|error| {
            reject_history_v2(SourceHistoryRejectCodeV2::ReceiptRejected, error.detail)
        })
}

fn derive_witness_root_v2<B: SourceHistoryProofBackendV2>(
    plan: &StructurallyValidDeltaPlanV2,
    statement: &CheckedSourceHistoryStatementV2,
    receipt_digest: &str,
) -> SourceHistoryResultV2<String> {
    let binding = WitnessBindingV2 {
        delta_plan_root: plan.root(),
        statement_root: statement.root(),
        chain_id: statement.chain_id(),
        deployment_root: statement.deployment_root(),
        profile_root: statement.profile_root(),
        history_root: statement.history_root(),
        history_height: statement.history_height(),
        writer_epoch: statement.writer_epoch(),
        verifier_release_id: B::VERIFIER_RELEASE_ID,
        verifier_image_id: B::IMAGE_ID,
        receipt_digest,
    };
    let value = serde_json::to_value(binding).map_err(|_| {
        reject_history_v2(
            SourceHistoryRejectCodeV2::CanonicalEncodingFailed,
            "verified source-history binding cannot be projected",
        )
    })?;
    let bytes = serde_json::to_vec(&sorted_json_v2(value)).map_err(|_| {
        reject_history_v2(
            SourceHistoryRejectCodeV2::CanonicalEncodingFailed,
            "verified source-history binding cannot be encoded",
        )
    })?;
    Ok(domain_hash_v2(WITNESS_ROOT_DOMAIN_V2, &bytes))
}

fn construct_verified_v2<B: SourceHistoryProofBackendV2>(
    plan: StructurallyValidDeltaPlanV2,
    statement: CheckedSourceHistoryStatementV2,
    receipt_digest: String,
    witness_root: String,
) -> VerifiedSourceHistoryDeltaPlanV2 {
    VerifiedSourceHistoryDeltaPlanV2 {
        plan,
        statement_root: statement.root().to_owned(),
        chain_id: statement.chain_id().to_owned(),
        deployment_root: statement.deployment_root().to_owned(),
        profile_root: statement.profile_root().to_owned(),
        history_root: statement.history_root().to_owned(),
        history_height: statement.history_height(),
        writer_epoch: statement.writer_epoch(),
        verifier_release_id: B::VERIFIER_RELEASE_ID.to_owned(),
        verifier_image_id: B::IMAGE_ID.to_owned(),
        receipt_digest,
        witness_root,
    }
}

/// Admit a source-history proof and create the only opaque witness in this ABI.
///
/// The backend type is sealed and release-pinned. This crate currently exports
/// no concrete backend, so downstream code cannot call this function until an
/// authenticated proof implementation is added here.
#[must_use = "proof admission must be inspected before witness use"]
pub fn admit_source_history_v2<B: SourceHistoryProofBackendV2>(
    plan: StructurallyValidDeltaPlanV2,
    statement: CheckedSourceHistoryStatementV2,
    receipt_bytes: &[u8],
    backend: &B,
) -> SourceHistoryResultV2<VerifiedSourceHistoryDeltaPlanV2> {
    validate_admission_inputs_v2::<B>(&plan, &statement, receipt_bytes)?;
    verify_receipt_v2(&statement, receipt_bytes, backend)?;
    let receipt_digest = domain_hash_v2(RECEIPT_DIGEST_DOMAIN_V2, receipt_bytes);
    let witness_root = derive_witness_root_v2::<B>(&plan, &statement, &receipt_digest)?;
    Ok(construct_verified_v2::<B>(
        plan,
        statement,
        receipt_digest,
        witness_root,
    ))
}

#[cfg(test)]
#[path = "source_history_admission_tests.rs"]
mod tests;
