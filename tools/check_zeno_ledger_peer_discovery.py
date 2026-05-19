#!/usr/bin/env python3
"""Replay ZenoLedger peer discovery registry admission sample cases."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_peer_discovery_v0 import (  # noqa: E402
    build_peer_registry_admission_v0,
    build_peer_registry_v0,
    validate_peer_registry_admission_v0,
    validate_peer_registry_v0,
)


RESULT_SCHEMA = "zenodex.zeno_ledger.peer_discovery_check.v1"
NETWORK_ID = "zeno-ledger-peer-discovery-checknet-0"
CHAIN_ID = "zeno-ledger-peer-discovery-checknet-0"


def _case(name: str, fn: Callable[[], object]) -> dict[str, object]:
    try:
        fn()
        return {"name": name, "ok": True, "status": "accepted", "error": None}
    except Exception as exc:
        return {"name": name, "ok": False, "status": "rejected", "error": str(exc)}


def run_check() -> dict[str, object]:
    registry = build_peer_registry_v0(
        network_id=NETWORK_ID,
        chain_id=CHAIN_ID,
        writer_urls=["http://127.0.0.1:8800"],
        peer_urls=["http://127.0.0.1:8800", "http://127.0.0.1:8801"],
    )
    admission = build_peer_registry_admission_v0(
        network_id=NETWORK_ID,
        chain_id=CHAIN_ID,
        writer_urls=["http://127.0.0.1:8800"],
        peer_urls=["http://127.0.0.1:8800", "http://127.0.0.1:8801"],
        peer_registry=registry,
    )
    tampered_registry = dict(registry)
    tampered_registry["peer_registry_hash"] = "0x" + "22" * 32
    cases = [
        _case("registry_hash_bound", lambda: validate_peer_registry_v0(registry)),
        _case(
            "registry_admission_hash_bound",
            lambda: validate_peer_registry_admission_v0(
                admission=admission,
                network_id=NETWORK_ID,
                chain_id=CHAIN_ID,
                writer_urls=["http://127.0.0.1:8800"],
                peer_urls=["http://127.0.0.1:8800", "http://127.0.0.1:8801"],
                peer_registry=registry,
            ),
        ),
        _case("tampered_registry_rejected", lambda: validate_peer_registry_v0(tampered_registry)),
        _case(
            "config_url_mismatch_rejected",
            lambda: build_peer_registry_admission_v0(
                network_id=NETWORK_ID,
                chain_id=CHAIN_ID,
                writer_urls=["http://127.0.0.1:8800"],
                peer_urls=["http://127.0.0.1:9999"],
                peer_registry=registry,
            ),
        ),
        _case(
            "unsafe_url_rejected",
            lambda: build_peer_registry_v0(
                network_id=NETWORK_ID,
                chain_id=CHAIN_ID,
                writer_urls=["https://user@example.com/node"],
                peer_urls=[],
            ),
        ),
    ]
    expected = {
        "registry_hash_bound": True,
        "registry_admission_hash_bound": True,
        "tampered_registry_rejected": False,
        "config_url_mismatch_rejected": False,
        "unsafe_url_rejected": False,
    }
    ok = all(case["ok"] is expected[str(case["name"])] for case in cases)
    return {"schema": RESULT_SCHEMA, "ok": ok, "cases": cases}


def main() -> int:
    result = run_check()
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
