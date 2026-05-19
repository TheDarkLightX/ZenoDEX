#!/usr/bin/env python3
"""Replay ZenoLedger dynamic peer admission sample cases."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_dynamic_peers_v0 import (  # noqa: E402
    build_dynamic_peer_admission_v0,
    build_dynamic_peer_candidate_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0  # noqa: E402


RESULT_SCHEMA = "zenodex.zeno_ledger.dynamic_peer_check.v1"
NETWORK_ID = "zeno-ledger-dynamic-peer-checknet-0"
CHAIN_ID = "zeno-ledger-dynamic-peer-checknet-0"


def _root(label: str) -> str:
    return hash_v0("dynamic_peer_check_root", {"label": label})


def _candidate(urls: list[str] | None = None, *, chain_id: str = CHAIN_ID) -> dict[str, object]:
    return build_dynamic_peer_candidate_v0(
        network_id=NETWORK_ID,
        chain_id=chain_id,
        source_node_id="node-a",
        source_peer_url="http://127.0.0.1:8800",
        candidate_peer_urls=urls or ["http://127.0.0.1:8801"],
        observed_at_height=5,
    )


def _peer_check(urls: list[str], *, ok: bool = True, chain_id: str = CHAIN_ID) -> dict[str, object]:
    return {
        "schema": "zenodex.zeno_ledger.node_peer_check_report.v0",
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "node_id": "node-a",
        "network_id": NETWORK_ID,
        "chain_id": chain_id,
        "feature_suite_hash": _root("features"),
        "local_tip": {"height": 5, "header_hash": _root("header-a")},
        "peer_count": len(urls),
        "peers": [
            {
                "peer_url": url,
                "ok": ok,
                "status": "accepted" if ok else "rejected",
                "network_match": ok,
                "chain_match": ok,
                "feature_suite_match": ok,
                "fork_choice_compatible": ok,
            }
            for url in urls
        ],
    }


def _case(name: str, fn: Callable[[], object]) -> dict[str, object]:
    try:
        fn()
        return {"name": name, "ok": True, "status": "accepted", "error": None}
    except Exception as exc:
        return {"name": name, "ok": False, "status": "rejected", "error": str(exc)}


def run_check() -> dict[str, object]:
    candidate = _candidate()
    cases = [
        _case(
            "dynamic_peer_admission_accepts_checked_peer",
            lambda: build_dynamic_peer_admission_v0(
                current_peer_urls=["http://127.0.0.1:8800"],
                candidate=candidate,
                peer_check_report=_peer_check(["http://127.0.0.1:8801"]),
                max_peer_count=4,
            ),
        ),
        _case(
            "dynamic_peer_admission_rejects_failed_peer_check",
            lambda: build_dynamic_peer_admission_v0(
                current_peer_urls=["http://127.0.0.1:8800"],
                candidate=candidate,
                peer_check_report=_peer_check(["http://127.0.0.1:8801"], ok=False),
                max_peer_count=4,
            ),
        ),
        _case(
            "dynamic_peer_admission_rejects_wrong_chain",
            lambda: build_dynamic_peer_admission_v0(
                current_peer_urls=["http://127.0.0.1:8800"],
                candidate=candidate,
                peer_check_report=_peer_check(["http://127.0.0.1:8801"], chain_id="wrong-chain"),
                max_peer_count=4,
            ),
        ),
        _case(
            "dynamic_peer_admission_rejects_cap_overflow",
            lambda: build_dynamic_peer_admission_v0(
                current_peer_urls=["http://127.0.0.1:8800"],
                candidate=_candidate(["http://127.0.0.1:8801", "http://127.0.0.1:8802"]),
                peer_check_report=_peer_check(["http://127.0.0.1:8801", "http://127.0.0.1:8802"]),
                max_peer_count=2,
            ),
        ),
    ]
    expected = {
        "dynamic_peer_admission_accepts_checked_peer": True,
        "dynamic_peer_admission_rejects_failed_peer_check": False,
        "dynamic_peer_admission_rejects_wrong_chain": False,
        "dynamic_peer_admission_rejects_cap_overflow": False,
    }
    ok = all(case["ok"] is expected[str(case["name"])] for case in cases)
    return {"schema": RESULT_SCHEMA, "ok": ok, "cases": cases}


def main() -> int:
    result = run_check()
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
