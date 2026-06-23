#!/usr/bin/env python3
"""Replay anti-equivocation checks over sample ZenoLedger evidence."""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_anti_equivocation_v0 import (  # noqa: E402
    build_checkpoint_equivocation_slashing_evidence_v0,
    build_watcher_attestation_equivocation_slashing_evidence_v0,
    validate_checkpoint_non_equivocation_v0,
    validate_slashing_evidence_v0,
    validate_watcher_attestation_non_equivocation_v0,
)
from src.integration.zeno_ledger_v0 import build_checkpoint_v0, build_header_v0, hash_v0  # noqa: E402
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0  # noqa: E402

ZERO_ROOT = "0x" + "00" * 32
RESULT_SCHEMA = "zenodex.zeno_ledger.anti_equivocation_check.v1"


def _root(label: str) -> str:
    return hash_v0("anti_equivocation_check", {"label": label})


def _header(*, height: int, label: str) -> dict[str, object]:
    return build_header_v0(
        chain_id="zeno-ledger-devnet-0",
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=_root(f"ingress-{label}"),
        tx_root=_root(f"tx-{label}"),
        pre_state_root=_root(f"pre-{label}"),
        post_state_root=_root(f"post-{label}"),
        app_hash=_root(f"app-{label}"),
        evidence_root=_root(f"evidence-{label}"),
        body_root=_root(f"body-{label}"),
        data_availability_root=_root(f"da-{label}"),
        proof_journal_hash=_root(f"proof-{label}"),
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _verify_report(*, last_header_hash: str) -> dict[str, object]:
    return {
        "schema": "zenodex.zeno_ledger.verify_report.v0",
        "ok": True,
        "status": "accepted",
        "checked_heights": [1, 2, 3],
        "proof_metadata_checked_heights": [],
        "proof_verification_checked_heights": [],
        "last_header_hash": last_header_hash,
        "last_post_state_root": _root(f"post-{last_header_hash}"),
        "last_app_hash": _root(f"app-{last_header_hash}"),
        "errors": [],
    }


def _case(name: str, fn) -> dict[str, object]:
    try:
        fn()
        return {"name": name, "status": "accepted", "ok": True, "error": None}
    except Exception as exc:
        return {"name": name, "status": "rejected", "ok": False, "error": str(exc)}


def run_check() -> dict[str, object]:
    checkpoint = build_checkpoint_v0(_header(height=1, label="a"))
    conflicting_checkpoint_a = build_checkpoint_v0(_header(height=2, label="a"))
    conflicting_checkpoint_b = build_checkpoint_v0(_header(height=2, label="b"))
    attestation = build_watcher_attestation_v0(
        verify_report=_verify_report(last_header_hash=_root("tip-a")),
        watcher_id="watcher-a",
        observed_time_ms=1,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    conflicting_attestation = build_watcher_attestation_v0(
        verify_report=_verify_report(last_header_hash=_root("tip-b")),
        watcher_id="watcher-b",
        observed_time_ms=2,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    cases = [
        _case(
            "checkpoint_duplicate_same_header",
            lambda: validate_checkpoint_non_equivocation_v0([checkpoint, dict(checkpoint)]),
        ),
        _case(
            "checkpoint_conflict_rejected",
            lambda: validate_checkpoint_non_equivocation_v0([conflicting_checkpoint_a, conflicting_checkpoint_b]),
        ),
        _case(
            "checkpoint_conflict_slashing_evidence",
            lambda: validate_slashing_evidence_v0(
                build_checkpoint_equivocation_slashing_evidence_v0(
                    conflicting_checkpoint_a,
                    conflicting_checkpoint_b,
                )
            ),
        ),
        _case(
            "watcher_duplicate_same_range",
            lambda: validate_watcher_attestation_non_equivocation_v0([attestation, dict(attestation)]),
        ),
        _case(
            "watcher_conflict_rejected",
            lambda: validate_watcher_attestation_non_equivocation_v0([attestation, conflicting_attestation]),
        ),
        _case(
            "watcher_conflict_slashing_evidence",
            lambda: validate_slashing_evidence_v0(
                build_watcher_attestation_equivocation_slashing_evidence_v0(
                    attestation,
                    conflicting_attestation,
                )
            ),
        ),
    ]
    expected = {
        "checkpoint_duplicate_same_header": True,
        "checkpoint_conflict_rejected": False,
        "checkpoint_conflict_slashing_evidence": True,
        "watcher_duplicate_same_range": True,
        "watcher_conflict_rejected": False,
        "watcher_conflict_slashing_evidence": True,
    }
    ok = all(case["ok"] is expected[str(case["name"])] for case in cases)
    return {"schema": RESULT_SCHEMA, "ok": ok, "cases": cases}


def main() -> int:
    result = run_check()
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
