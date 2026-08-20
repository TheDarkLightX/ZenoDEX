use std::cell::Cell;

use super::*;
use crate::{decode_delta_plan_v2, decode_source_history_statement_v2};

const PLAN: &str = include_str!("../../../tests/data/global_economic_delta_v2_plan.json");
const STATEMENT: &str =
    include_str!("../../../tests/data/global_economic_source_history_v2_statement.json");
const RELEASE: &str = "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
const IMAGE: &str = "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";

struct ExactFixtureBackend {
    reject: bool,
    calls: Cell<u8>,
}

impl backend_seal::Sealed for ExactFixtureBackend {}

impl SourceHistoryProofBackendV2 for ExactFixtureBackend {
    const VERIFIER_RELEASE_ID: &'static str = RELEASE;
    const IMAGE_ID: &'static str = IMAGE;

    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &str,
        expected_journal_bytes: &[u8],
    ) -> Result<(), SourceHistoryBackendRejectV2> {
        self.calls.set(self.calls.get() + 1);
        if self.reject
            || receipt_bytes != b"fixture-succinct-receipt"
            || expected_image_id != IMAGE
            || expected_journal_bytes != STATEMENT.as_bytes()
        {
            return Err(SourceHistoryBackendRejectV2::new(
                "fixture verifier rejected",
            ));
        }
        Ok(())
    }
}

fn fixture() -> (
    StructurallyValidDeltaPlanV2,
    CheckedSourceHistoryStatementV2,
) {
    let plan = decode_delta_plan_v2(PLAN.as_bytes()).unwrap();
    let statement = decode_source_history_statement_v2(&plan, STATEMENT.as_bytes()).unwrap();
    (plan, statement)
}

#[test]
fn exact_backend_acceptance_constructs_owned_opaque_witness() {
    // Arrange
    let (plan, statement) = fixture();
    let backend = ExactFixtureBackend {
        reject: false,
        calls: Cell::new(0),
    };

    // Act
    let verified =
        admit_source_history_v2(plan, statement, b"fixture-succinct-receipt", &backend).unwrap();

    // Assert
    assert_eq!(backend.calls.get(), 1);
    assert_eq!(verified.source_claim_count(), 3);
    assert_eq!(verified.writer_epoch(), 1);
    assert_eq!(verified.chain_id(), "zenodex:research");
    assert_eq!(
        verified.deployment_root(),
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    );
    assert_eq!(
        verified.profile_root(),
        "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
    );
    assert_eq!(verified.history_height(), 30);
    assert_eq!(verified.verifier_release_id(), RELEASE);
    assert_eq!(verified.verifier_image_id(), IMAGE);
    assert!(verified.receipt_digest().starts_with("sha256:"));
    assert!(verified.witness_root().starts_with("sha256:"));
    assert_eq!(verified.into_structural_plan().event_count(), 8);
}

#[test]
fn backend_rejection_returns_no_witness() {
    // Arrange
    let (plan, statement) = fixture();
    let backend = ExactFixtureBackend {
        reject: true,
        calls: Cell::new(0),
    };

    // Act
    let rejected = admit_source_history_v2(plan, statement, b"bad-receipt", &backend)
        .err()
        .unwrap();

    // Assert
    assert_eq!(backend.calls.get(), 1);
    assert_eq!(rejected.code, SourceHistoryRejectCodeV2::ReceiptRejected);
}

#[test]
fn empty_and_oversized_receipts_reject_before_backend_call() {
    // Arrange
    let backend = ExactFixtureBackend {
        reject: false,
        calls: Cell::new(0),
    };

    // Act / Assert
    let (plan, statement) = fixture();
    assert_eq!(
        admit_source_history_v2(plan, statement, b"", &backend)
            .err()
            .unwrap()
            .code,
        SourceHistoryRejectCodeV2::ReceiptEmpty
    );
    let (plan, statement) = fixture();
    assert_eq!(
        admit_source_history_v2(
            plan,
            statement,
            &vec![0; MAX_SOURCE_HISTORY_RECEIPT_BYTES_V2 + 1],
            &backend,
        )
        .err()
        .unwrap()
        .code,
        SourceHistoryRejectCodeV2::ReceiptTooLarge
    );
    assert_eq!(backend.calls.get(), 0);
}

struct WrongReleaseBackend;
impl backend_seal::Sealed for WrongReleaseBackend {}
impl SourceHistoryProofBackendV2 for WrongReleaseBackend {
    const VERIFIER_RELEASE_ID: &'static str =
        "sha256:abababababababababababababababababababababababababababababababab";
    const IMAGE_ID: &'static str = IMAGE;

    fn verify_succinct_receipt(
        &self,
        _receipt_bytes: &[u8],
        _expected_image_id: &str,
        _expected_journal_bytes: &[u8],
    ) -> Result<(), SourceHistoryBackendRejectV2> {
        panic!("release mismatch must reject before backend invocation")
    }
}

struct WrongImageBackend;
impl backend_seal::Sealed for WrongImageBackend {}
impl SourceHistoryProofBackendV2 for WrongImageBackend {
    const VERIFIER_RELEASE_ID: &'static str = RELEASE;
    const IMAGE_ID: &'static str =
        "sha256:acacacacacacacacacacacacacacacacacacacacacacacacacacacacacacacac";

    fn verify_succinct_receipt(
        &self,
        _receipt_bytes: &[u8],
        _expected_image_id: &str,
        _expected_journal_bytes: &[u8],
    ) -> Result<(), SourceHistoryBackendRejectV2> {
        panic!("image mismatch must reject before backend invocation")
    }
}

#[test]
fn verifier_release_is_selected_by_sealed_backend_type() {
    // Arrange
    let (plan, statement) = fixture();

    // Act
    let rejected = admit_source_history_v2(
        plan,
        statement,
        b"fixture-succinct-receipt",
        &WrongReleaseBackend,
    )
    .err()
    .unwrap();

    // Assert
    assert_eq!(
        rejected.code,
        SourceHistoryRejectCodeV2::VerifierReleaseMismatch
    );
}

#[test]
fn verifier_image_is_selected_by_sealed_backend_type() {
    // Arrange
    let (plan, statement) = fixture();

    // Act
    let rejected = admit_source_history_v2(
        plan,
        statement,
        b"fixture-succinct-receipt",
        &WrongImageBackend,
    )
    .err()
    .unwrap();

    // Assert
    assert_eq!(
        rejected.code,
        SourceHistoryRejectCodeV2::VerifierImageMismatch
    );
}

#[test]
fn checked_statement_cannot_be_rebound_to_a_different_plan() {
    // Arrange
    let (_, statement) = fixture();
    let different = PLAN.replace("\"amount_atoms\":1", "\"amount_atoms\":9");
    let plan = decode_delta_plan_v2(different.as_bytes()).unwrap();
    let backend = ExactFixtureBackend {
        reject: false,
        calls: Cell::new(0),
    };

    // Act
    let rejected = admit_source_history_v2(plan, statement, b"fixture-succinct-receipt", &backend)
        .err()
        .unwrap();

    // Assert
    assert_eq!(
        rejected.code,
        SourceHistoryRejectCodeV2::DeltaPlanRootMismatch
    );
    assert_eq!(backend.calls.get(), 0);
}
