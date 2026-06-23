#!/usr/bin/env python3
"""Replay the ZenoLedger bonded slashing policy sample cases."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_anti_equivocation_v0 import (  # noqa: E402
    build_checkpoint_equivocation_slashing_evidence_v0,
    build_watcher_attestation_equivocation_slashing_evidence_v0,
)
from src.integration.zeno_ledger_bonded_slashing_v0 import (  # noqa: E402
    apply_bonded_slashing_v0,
    build_bond_registry_v0,
    build_slashing_policy_v0,
    validate_bonded_slashing_receipt_v0,
)
from src.integration.zeno_ledger_v0 import build_checkpoint_v0, build_header_v0, hash_v0  # noqa: E402
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0  # noqa: E402


RESULT_SCHEMA = "zenodex.zeno_ledger.bonded_slashing_check.v1"
ZERO_ROOT = "0x" + "00" * 32


def _root(label: str) -> str:
    return hash_v0("bonded_slashing_check_root", {"label": label})


def _header(*, height: int, body_label: str) -> dict[str, object]:
    return build_header_v0(
        chain_id="zeno-ledger-slashing-checknet-0",
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
    return build_checkpoint_equivocation_slashing_evidence_v0(
        build_checkpoint_v0(_header(height=9, body_label="a")),
        build_checkpoint_v0(_header(height=9, body_label="b")),
    )


def _verify_report(*, from_height: int, to_height: int, last_header_hash: str) -> dict[str, object]:
    return {
        "schema": "zenodex.zeno_ledger.verify_report.v0",
        "ok": True,
        "status": "accepted",
        "checked_heights": list(range(from_height, to_height + 1)),
        "proof_metadata_checked_heights": [],
        "proof_verification_checked_heights": [],
        "last_header_hash": last_header_hash,
        "last_post_state_root": _root(f"post-{last_header_hash}"),
        "last_app_hash": _root(f"app-{last_header_hash}"),
        "errors": [],
    }


def _watcher_evidence() -> dict[str, object]:
    return build_watcher_attestation_equivocation_slashing_evidence_v0(
        build_watcher_attestation_v0(
            verify_report=_verify_report(from_height=2, to_height=5, last_header_hash=_root("tip-a")),
            watcher_id="watcher-a",
            observed_time_ms=1,
            verifier_ref="python:zeno_ledger_verify:v0",
        ),
        build_watcher_attestation_v0(
            verify_report=_verify_report(from_height=4, to_height=5, last_header_hash=_root("tip-b")),
            watcher_id="watcher-b",
            observed_time_ms=2,
            verifier_ref="python:zeno_ledger_verify:v0",
        ),
    )


def _registry_for(
    evidence: dict[str, object],
    *,
    subject_kind: str,
    bonded_amount: int = 1_000,
    slashed_amount: int = 0,
    slashable_until_height: int = 100,
) -> dict[str, object]:
    return build_bond_registry_v0(
        chain_id=str(evidence["chain_id"]),
        asset_id="ZENO",
        entries=[
            {
                "subject_id": evidence["subject_id"],
                "subject_kind": subject_kind,
                "bonded_amount": bonded_amount,
                "slashed_amount": slashed_amount,
                "slashable_until_height": slashable_until_height,
                "status": "active",
                "processed_evidence_hashes": [],
            }
        ],
    )


def _policy_for(evidence: dict[str, object]) -> dict[str, object]:
    return build_slashing_policy_v0(
        chain_id=str(evidence["chain_id"]),
        policy_id="bonded-slashing-check-policy-v0",
        evidence_kind=str(evidence["evidence_kind"]),
        slash_fraction_bps=1_000,
        min_slash_amount=1,
        max_slash_amount=200,
        burn_fraction_bps=5_000,
    )


def _case(name: str, fn: Callable[[], object]) -> dict[str, object]:
    try:
        fn()
        return {"name": name, "ok": True, "status": "accepted", "error": None}
    except Exception as exc:
        return {"name": name, "ok": False, "status": "rejected", "error": str(exc)}


def _validate_transition(
    *,
    evidence: dict[str, object],
    registry: dict[str, object],
    policy: dict[str, object],
) -> None:
    transition = apply_bonded_slashing_v0(evidence=evidence, bond_registry=registry, policy=policy)
    validate_bonded_slashing_receipt_v0(
        receipt=transition["receipt"],
        updated_bond_registry=transition["bond_registry"],
        evidence=evidence,
        bond_registry_before=registry,
        policy=policy,
    )


def run_check() -> dict[str, object]:
    checkpoint_evidence = _checkpoint_evidence()
    watcher_evidence = _watcher_evidence()
    checkpoint_registry = _registry_for(checkpoint_evidence, subject_kind="validator_set")
    checkpoint_policy = _policy_for(checkpoint_evidence)
    watcher_registry = _registry_for(watcher_evidence, subject_kind="watcher_profile")
    watcher_policy = _policy_for(watcher_evidence)
    transition = apply_bonded_slashing_v0(
        evidence=checkpoint_evidence,
        bond_registry=checkpoint_registry,
        policy=checkpoint_policy,
    )

    cases = [
        _case(
            "checkpoint_bonded_slash_receipt",
            lambda: validate_bonded_slashing_receipt_v0(
                receipt=transition["receipt"],
                updated_bond_registry=transition["bond_registry"],
                evidence=checkpoint_evidence,
                bond_registry_before=checkpoint_registry,
                policy=checkpoint_policy,
            ),
        ),
        _case(
            "watcher_bonded_slash_receipt",
            lambda: _validate_transition(
                evidence=watcher_evidence,
                registry=watcher_registry,
                policy=watcher_policy,
            ),
        ),
        _case(
            "replay_rejected",
            lambda: apply_bonded_slashing_v0(
                evidence=checkpoint_evidence,
                bond_registry=transition["bond_registry"],
                policy=checkpoint_policy,
            ),
        ),
        _case(
            "slash_over_available_bond_rejected",
            lambda: apply_bonded_slashing_v0(
                evidence=checkpoint_evidence,
                bond_registry=_registry_for(
                    checkpoint_evidence,
                    subject_kind="validator_set",
                    slashed_amount=990,
                ),
                policy=checkpoint_policy,
            ),
        ),
        _case(
            "expired_slashability_window_rejected",
            lambda: apply_bonded_slashing_v0(
                evidence=checkpoint_evidence,
                bond_registry=_registry_for(
                    checkpoint_evidence,
                    subject_kind="validator_set",
                    slashable_until_height=8,
                ),
                policy=checkpoint_policy,
            ),
        ),
    ]
    expected = {
        "checkpoint_bonded_slash_receipt": True,
        "watcher_bonded_slash_receipt": True,
        "replay_rejected": False,
        "slash_over_available_bond_rejected": False,
        "expired_slashability_window_rejected": False,
    }
    ok = all(case["ok"] is expected[str(case["name"])] for case in cases)
    return {"schema": RESULT_SCHEMA, "ok": ok, "cases": cases}


def main() -> int:
    result = run_check()
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
