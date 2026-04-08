from __future__ import annotations

from pathlib import Path

from tools import settlement_attestation_sequence_grammar_fuzz as fuzz


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_settlement_attestation_sequence_policy_mode_reaches_target_hits() -> None:
    report = fuzz.explore_target(
        max_depth=1,
        max_frontier=16,
        target_manifest=str(MANIFEST_PATH),
        target_id="settlement_attestation_policy_boundary",
        attestation_mode="policy",
    )
    assert report.reached_target_ids == ("settlement_attestation_policy_boundary",)
    labels = {case.outcome_label for case in report.cases}
    assert "ok:steps=2:policy" in labels
    assert "reject:step=1:settlement spot price attestation is stale" in labels
    assert "reject:step=1:source_id not allowlisted for signer: oracle:b" in labels
    assert "reject:step=1:packet_hash mismatch" in labels
    assert "reject:step=1:settlement spot price attestation signature invalid" in labels


def test_settlement_attestation_sequence_policy_minimize_case_preserves_stale_reject() -> None:
    witness = fuzz.minimize_case("stale_second_step", attestation_mode="policy")
    assert witness.outcome_label == "reject:step=1:settlement spot price attestation is stale"
    assert witness.attestation_mode == "policy"


def test_settlement_attestation_sequence_policy_minimize_case_preserves_allowlist_drift_reject() -> None:
    witness = fuzz.minimize_case("narrow_allowlist", attestation_mode="policy")
    assert witness.outcome_label == "reject:step=1:source_id not allowlisted for signer: oracle:b"
    assert witness.attestation_mode == "policy"


def test_settlement_attestation_sequence_policy_minimize_case_preserves_packet_hash_reject() -> None:
    witness = fuzz.minimize_case("tamper_second_step_hash", attestation_mode="policy")
    assert witness.outcome_label == "reject:step=1:packet_hash mismatch"
    assert witness.attestation_mode == "policy"


def test_settlement_attestation_sequence_policy_minimize_case_preserves_signature_reject() -> None:
    witness = fuzz.minimize_case("tamper_second_step_signature", attestation_mode="policy")
    assert witness.outcome_label == "reject:step=1:settlement spot price attestation signature invalid"
    assert witness.attestation_mode == "policy"


def test_settlement_attestation_sequence_policy_minimize_case_preserves_future_epoch_reject() -> None:
    witness = fuzz.minimize_case("future_second_step", attestation_mode="policy")
    assert witness.outcome_label == "reject:step=1:attestation signed_at_epoch is in the future"
    assert witness.attestation_mode == "policy"
