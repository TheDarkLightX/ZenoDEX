from __future__ import annotations

import pytest

from src.integration.zeno_ledger_anti_equivocation_v0 import (
    build_checkpoint_equivocation_slashing_evidence_v0,
    build_watcher_attestation_equivocation_slashing_evidence_v0,
)
from src.integration.zeno_ledger_bonded_slashing_v0 import (
    apply_bonded_slashing_v0,
    build_bond_registry_v0,
    build_slashing_policy_v0,
    validate_bond_registry_v0,
    validate_bonded_slashing_receipt_v0,
    validate_slashing_policy_v0,
)
from src.integration.zeno_ledger_v0 import build_checkpoint_v0, build_header_v0, hash_v0
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0

ZERO_ROOT = "0x" + "00" * 32


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _header(*, height: int, body_label: str) -> dict[str, object]:
    return build_header_v0(
        chain_id="zeno-ledger-slashing-testnet-0",
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("validator-set"),
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


def _checkpoint_evidence() -> dict[str, object]:
    checkpoint_a = build_checkpoint_v0(_header(height=7, body_label="a"))
    checkpoint_b = build_checkpoint_v0(_header(height=7, body_label="b"))
    return build_checkpoint_equivocation_slashing_evidence_v0(checkpoint_a, checkpoint_b)


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


def _watcher_evidence() -> dict[str, object]:
    attestation_a = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=3, to_height=8, last_header_hash=_root("tip-a")),
        watcher_id="watcher-a",
        observed_time_ms=1,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    attestation_b = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=5, to_height=8, last_header_hash=_root("tip-b")),
        watcher_id="watcher-b",
        observed_time_ms=2,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    return build_watcher_attestation_equivocation_slashing_evidence_v0(attestation_a, attestation_b)


def _registry_for(evidence: dict[str, object], *, subject_kind: str, slashed_amount: int = 0) -> dict[str, object]:
    return build_bond_registry_v0(
        chain_id=str(evidence["chain_id"]),
        asset_id="ZENO",
        entries=[
            {
                "subject_id": evidence["subject_id"],
                "subject_kind": subject_kind,
                "bonded_amount": 1_000,
                "slashed_amount": slashed_amount,
                "slashable_until_height": 100,
                "status": "active",
                "processed_evidence_hashes": [],
            }
        ],
    )


def _policy_for(evidence: dict[str, object], *, max_slash_amount: int = 200) -> dict[str, object]:
    return build_slashing_policy_v0(
        chain_id=str(evidence["chain_id"]),
        policy_id="slashing-policy-v0",
        evidence_kind=str(evidence["evidence_kind"]),
        slash_fraction_bps=1_000,
        min_slash_amount=1,
        max_slash_amount=max_slash_amount,
        burn_fraction_bps=5_000,
    )


def test_bonded_slashing_accepts_checkpoint_equivocation_with_bounded_receipt() -> None:
    evidence = _checkpoint_evidence()
    registry = _registry_for(evidence, subject_kind="validator_set")
    policy = _policy_for(evidence)

    transition = apply_bonded_slashing_v0(evidence=evidence, bond_registry=registry, policy=policy)
    receipt = transition["receipt"]
    updated_registry = transition["bond_registry"]

    assert receipt["ok"] is True
    assert receipt["subject_kind"] == "validator_set"
    assert receipt["slash_amount"] == 100
    assert receipt["burn_amount"] == 50
    assert receipt["treasury_amount"] == 50
    assert receipt["remaining_bond"] == 900
    assert updated_registry["entries"][0]["processed_evidence_hashes"] == [evidence["evidence_hash"]]
    validate_bond_registry_v0(updated_registry)
    validate_slashing_policy_v0(policy)
    validate_bonded_slashing_receipt_v0(
        receipt=receipt,
        updated_bond_registry=updated_registry,
        evidence=evidence,
        bond_registry_before=registry,
        policy=policy,
    )


def test_bonded_slashing_rejects_replayed_evidence_hash() -> None:
    evidence = _checkpoint_evidence()
    registry = _registry_for(evidence, subject_kind="validator_set")
    policy = _policy_for(evidence)
    updated_registry = apply_bonded_slashing_v0(
        evidence=evidence,
        bond_registry=registry,
        policy=policy,
    )["bond_registry"]

    with pytest.raises(ValueError, match="already processed"):
        apply_bonded_slashing_v0(evidence=evidence, bond_registry=updated_registry, policy=policy)


def test_bonded_slashing_rejects_unbonded_subject() -> None:
    evidence = _checkpoint_evidence()
    empty_registry = build_bond_registry_v0(chain_id=str(evidence["chain_id"]), asset_id="ZENO", entries=[])

    with pytest.raises(ValueError, match="not bonded"):
        apply_bonded_slashing_v0(evidence=evidence, bond_registry=empty_registry, policy=_policy_for(evidence))


def test_bonded_slashing_rejects_slash_over_available_bond() -> None:
    evidence = _checkpoint_evidence()
    registry = _registry_for(evidence, subject_kind="validator_set", slashed_amount=990)
    policy = _policy_for(evidence)

    with pytest.raises(ValueError, match="exceeds available bond"):
        apply_bonded_slashing_v0(evidence=evidence, bond_registry=registry, policy=policy)


def test_bonded_slashing_rejects_expired_slashability_window() -> None:
    evidence = _checkpoint_evidence()
    registry = build_bond_registry_v0(
        chain_id=str(evidence["chain_id"]),
        asset_id="ZENO",
        entries=[
            {
                "subject_id": evidence["subject_id"],
                "subject_kind": "validator_set",
                "bonded_amount": 1_000,
                "slashed_amount": 0,
                "slashable_until_height": 6,
                "status": "active",
                "processed_evidence_hashes": [],
            }
        ],
    )

    with pytest.raises(ValueError, match="slashability window"):
        apply_bonded_slashing_v0(evidence=evidence, bond_registry=registry, policy=_policy_for(evidence))


def test_bonded_slashing_rejects_wrong_subject_kind() -> None:
    evidence = _checkpoint_evidence()
    registry = _registry_for(evidence, subject_kind="watcher_profile")

    with pytest.raises(ValueError, match="not bonded"):
        apply_bonded_slashing_v0(evidence=evidence, bond_registry=registry, policy=_policy_for(evidence))




def test_bonded_slashing_rejects_noncanonical_artifacts_even_with_valid_hash_binding() -> None:
    evidence = _checkpoint_evidence()
    forged = dict(evidence)
    forged["artifacts"] = [
        _header(height=7, body_label="forged-a"),
        _header(height=7, body_label="forged-b"),
    ]
    forged["evidence_hash"] = hash_v0(
        "zeno_ledger_slashing_evidence_v0",
        {key: value for key, value in forged.items() if key != "evidence_hash"},
    )
    registry = _registry_for(forged, subject_kind="validator_set")

    with pytest.raises(ValueError):
        apply_bonded_slashing_v0(evidence=forged, bond_registry=registry, policy=_policy_for(forged))

def test_bonded_slashing_accepts_watcher_equivocation() -> None:
    evidence = _watcher_evidence()
    registry = _registry_for(evidence, subject_kind="watcher_profile")
    policy = _policy_for(evidence)

    transition = apply_bonded_slashing_v0(evidence=evidence, bond_registry=registry, policy=policy)

    assert transition["receipt"]["subject_kind"] == "watcher_profile"
    assert transition["receipt"]["slash_amount"] == 100
    validate_bonded_slashing_receipt_v0(
        receipt=transition["receipt"],
        updated_bond_registry=transition["bond_registry"],
        evidence=evidence,
        bond_registry_before=registry,
        policy=policy,
    )


def test_checkpoint_evidence_is_order_invariant() -> None:
    checkpoint_a = build_checkpoint_v0(_header(height=7, body_label="a"))
    checkpoint_b = build_checkpoint_v0(_header(height=7, body_label="b"))

    evidence_ab = build_checkpoint_equivocation_slashing_evidence_v0(checkpoint_a, checkpoint_b)
    evidence_ba = build_checkpoint_equivocation_slashing_evidence_v0(checkpoint_b, checkpoint_a)

    assert evidence_ab == evidence_ba


def test_watcher_evidence_is_order_invariant() -> None:
    attestation_a = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=3, to_height=8, last_header_hash=_root("tip-a")),
        watcher_id="watcher-a",
        observed_time_ms=1,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    attestation_b = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=5, to_height=8, last_header_hash=_root("tip-b")),
        watcher_id="watcher-b",
        observed_time_ms=2,
        verifier_ref="python:zeno_ledger_verify:v0",
    )

    evidence_ab = build_watcher_attestation_equivocation_slashing_evidence_v0(attestation_a, attestation_b)
    evidence_ba = build_watcher_attestation_equivocation_slashing_evidence_v0(attestation_b, attestation_a)

    assert evidence_ab == evidence_ba
