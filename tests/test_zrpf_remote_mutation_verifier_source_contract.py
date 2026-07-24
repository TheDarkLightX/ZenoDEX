from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / (
    "zk/spot_settlement_v7_risc0/mutation_verifier/src/main.rs"
)


def test_remote_mutation_verifier_authenticates_all_five_positive_receipts() -> None:
    source = SOURCE.read_text(encoding="utf-8")
    required = (
        "VerifiedSourceOpenedSpotValueLeafReceiptV6::verify_governed_exact_succinct_bytes",
        "VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes",
        "VerifiedSourceOpenedSpotSettlementAdmissionV6::verify",
        "verify_spot_settlement_v7_canonical_succinct_bytes",
    )
    for call in required:
        assert call in source
    assert source.count("VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes") >= 4
    assert source.count("verify_spot_settlement_v7_canonical_succinct_bytes") >= 2


def test_remote_mutation_verifier_requires_crypto_reject_at_exact_boundary() -> None:
    source = SOURCE.read_text(encoding="utf-8")
    assert source.count("VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed") >= 3
    assert source.count("VerifiedSpotSettlementV7ErrorV1::ReceiptVerificationFailed") >= 1
    assert "word_index: MUTATION_WORD_INDEX" in source
    assert "original_word ^ XOR_MASK" in source
    assert "restored_bytes != source_bytes" in source


def test_settlement_is_linked_to_the_already_verified_l2_journal() -> None:
    source = SOURCE.read_text(encoding="utf-8")
    decoder = "decode_exact_source_opened_spot_settlement_guest_envelope_v3"
    link = "require_settlement_l2_claim("
    settlement_verify = "VerifiedSourceOpenedSpotSettlementAdmissionV6::verify("
    assert decoder in source
    assert "envelope.proposal_bytes(), verified_l2_journal" in source
    assert 'CliError("settlement_l2_claim_mismatch")' in source
    assert source.index(link) < source.index(settlement_verify)


def test_remote_mutation_report_is_authority_false_and_content_bound() -> None:
    source = SOURCE.read_text(encoding="utf-8")
    assert "REPORT_DOMAIN" in source
    assert "settlement_l2_claim_bound: true" in source
    assert 'report_id: ZERO_SHA256.to_owned()' in source
    for field in (
        "proof_authority: false",
        "release_authority: false",
        "settlement_authority: false",
        "production_authority: false",
    ):
        assert field in source
    assert "program_sha256" in source
    assert "positive_receipt_sha256" in source
    assert "mutation_receipt_sha256" in source
