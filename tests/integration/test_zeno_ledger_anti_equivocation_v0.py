from __future__ import annotations

import pytest

from src.integration.zeno_ledger_anti_equivocation_v0 import (
    build_checkpoint_equivocation_slashing_evidence_v0,
    build_watcher_attestation_equivocation_slashing_evidence_v0,
    validate_checkpoint_non_equivocation_v0,
    validate_slashing_evidence_v0,
    validate_watcher_attestation_non_equivocation_v0,
)
from src.integration.zeno_ledger_v0 import build_checkpoint_v0, build_header_v0, hash_v0
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0

ZERO_ROOT = "0x" + "00" * 32


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _header(*, height: int, body_label: str) -> dict[str, object]:
    return build_header_v0(
        chain_id="zeno-ledger-devnet-0",
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=_root(f"ingress-{body_label}"),
        tx_root=_root(f"tx-{body_label}"),
        pre_state_root=_root(f"pre-{body_label}"),
        post_state_root=_root(f"post-{body_label}"),
        app_hash=_root(f"app-{body_label}"),
        evidence_root=_root(f"evidence-{body_label}"),
        body_root=_root(f"body-{body_label}"),
        data_availability_root=_root(f"da-{body_label}"),
        proof_journal_hash=_root(f"proof-{body_label}"),
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _verify_report(*, from_height: int, to_height: int, last_header_hash: str) -> dict[str, object]:
    return {
        "schema": "zenodex.zeno_ledger.verify_report.v0",
        "ok": True,
        "status": "range_verified",
        "mode": "replay_bound",
        "authority_scope": "replay_bound_range_v0",
        "range_verified": True,
        "header_linkage_checked": True,
        "state_continuity_checked": True,
        "state_replay_checked": True,
        "receipt_replay_checked": True,
        "config_binding_checked": True,
        "replay_config_digest": _root("replay-config"),
        "checked_heights": list(range(from_height, to_height + 1)),
        "proof_metadata_checked_heights": [],
        "proof_verification_checked_heights": [],
        "last_header_hash": last_header_hash,
        "last_post_state_root": _root(f"post-{last_header_hash}"),
        "last_app_hash": _root(f"app-{last_header_hash}"),
        "errors": [],
    }


def test_checkpoint_non_equivocation_accepts_duplicate_same_header() -> None:
    checkpoint = build_checkpoint_v0(_header(height=1, body_label="a"))
    validate_checkpoint_non_equivocation_v0([checkpoint, dict(checkpoint)])


def test_checkpoint_non_equivocation_rejects_same_height_conflict() -> None:
    checkpoint_a = build_checkpoint_v0(_header(height=1, body_label="a"))
    checkpoint_b = build_checkpoint_v0(_header(height=1, body_label="b"))

    with pytest.raises(ValueError, match="checkpoint equivocation"):
        validate_checkpoint_non_equivocation_v0([checkpoint_a, checkpoint_b])


def test_checkpoint_equivocation_slashing_evidence_is_hash_bound() -> None:
    checkpoint_a = build_checkpoint_v0(_header(height=1, body_label="a"))
    checkpoint_b = build_checkpoint_v0(_header(height=1, body_label="b"))

    evidence = build_checkpoint_equivocation_slashing_evidence_v0(checkpoint_a, checkpoint_b)
    reversed_evidence = build_checkpoint_equivocation_slashing_evidence_v0(checkpoint_b, checkpoint_a)

    assert evidence["schema"] == "zenodex/zeno_ledger/slashing_evidence/v0"
    assert evidence["evidence_kind"] == "checkpoint_equivocation"
    assert evidence["status"] == "slashable"
    assert evidence["height"] == 1
    assert len(evidence["conflicting_header_hashes"]) == 2
    assert evidence == reversed_evidence
    validate_slashing_evidence_v0(evidence)


def test_checkpoint_equivocation_slashing_evidence_rejects_unsorted_hashes() -> None:
    checkpoint_a = build_checkpoint_v0(_header(height=1, body_label="a"))
    checkpoint_b = build_checkpoint_v0(_header(height=1, body_label="b"))
    evidence = build_checkpoint_equivocation_slashing_evidence_v0(checkpoint_a, checkpoint_b)
    evidence["conflicting_header_hashes"] = list(reversed(evidence["conflicting_header_hashes"]))

    with pytest.raises(ValueError, match="header hashes must be sorted|hash mismatch"):
        validate_slashing_evidence_v0(evidence)


def test_checkpoint_equivocation_slashing_evidence_rejects_non_conflict() -> None:
    checkpoint = build_checkpoint_v0(_header(height=1, body_label="a"))

    with pytest.raises(ValueError, match="conflicting header hashes"):
        build_checkpoint_equivocation_slashing_evidence_v0(checkpoint, dict(checkpoint))


def test_watcher_attestation_non_equivocation_accepts_consistent_ranges() -> None:
    report = _verify_report(from_height=1, to_height=5, last_header_hash=_root("tip-a"))
    attestation = build_watcher_attestation_v0(
        verify_report=report,
        watcher_id="watcher-a",
        observed_time_ms=1_778_730_000_000,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    validate_watcher_attestation_non_equivocation_v0([attestation, dict(attestation)])


def test_watcher_attestation_non_equivocation_rejects_same_range_conflict() -> None:
    attestation_a = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=1, to_height=5, last_header_hash=_root("tip-a")),
        watcher_id="watcher-a",
        observed_time_ms=1,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    attestation_b = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=1, to_height=5, last_header_hash=_root("tip-b")),
        watcher_id="watcher-b",
        observed_time_ms=2,
        verifier_ref="python:zeno_ledger_verify:v0",
    )

    with pytest.raises(ValueError, match="watcher attestation equivocation"):
        validate_watcher_attestation_non_equivocation_v0([attestation_a, attestation_b])


def test_watcher_attestation_non_equivocation_rejects_same_tip_conflict() -> None:
    attestation_a = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=1, to_height=5, last_header_hash=_root("tip-a")),
        watcher_id="watcher-a",
        observed_time_ms=1,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    attestation_b = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=3, to_height=5, last_header_hash=_root("tip-b")),
        watcher_id="watcher-b",
        observed_time_ms=2,
        verifier_ref="python:zeno_ledger_verify:v0",
    )

    with pytest.raises(ValueError, match="tip equivocation"):
        validate_watcher_attestation_non_equivocation_v0([attestation_a, attestation_b])


def test_watcher_equivocation_slashing_evidence_is_hash_bound() -> None:
    attestation_a = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=1, to_height=5, last_header_hash=_root("tip-a")),
        watcher_id="watcher-a",
        observed_time_ms=1,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    attestation_b = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=3, to_height=5, last_header_hash=_root("tip-b")),
        watcher_id="watcher-b",
        observed_time_ms=2,
        verifier_ref="python:zeno_ledger_verify:v0",
    )

    evidence = build_watcher_attestation_equivocation_slashing_evidence_v0(attestation_a, attestation_b)
    reversed_evidence = build_watcher_attestation_equivocation_slashing_evidence_v0(attestation_b, attestation_a)

    assert evidence["schema"] == "zenodex/zeno_ledger/slashing_evidence/v0"
    assert evidence["evidence_kind"] == "watcher_attestation_equivocation"
    assert evidence["status"] == "slashable"
    assert evidence["height"] == 5
    assert evidence["conflict_key"]["conflict_scope"] == "tip"
    assert evidence == reversed_evidence
    validate_slashing_evidence_v0(evidence)


def test_watcher_equivocation_slashing_evidence_rejects_bad_attestation_hash() -> None:
    attestation_a = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=1, to_height=5, last_header_hash=_root("tip-a")),
        watcher_id="watcher-a",
        observed_time_ms=1,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    attestation_b = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=3, to_height=5, last_header_hash=_root("tip-b")),
        watcher_id="watcher-b",
        observed_time_ms=2,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    attestation_b["attestation_hash"] = _root("tampered-attestation")

    with pytest.raises(ValueError, match="attestation_hash mismatch"):
        build_watcher_attestation_equivocation_slashing_evidence_v0(attestation_a, attestation_b)
