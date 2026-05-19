#!/usr/bin/env python3
"""Replay ZenoLedger block gossip envelope admission sample cases."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_block_gossip_v0 import (  # noqa: E402
    build_block_gossip_envelope_v0,
    validate_block_gossip_envelope_v0,
)
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    build_checkpoint_v0,
    build_header_v0,
    canonical_body_root_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    hash_v0,
)
from tools.zeno_ledger_make_testnet_bundle import DEFAULT_BOOTSTRAP_SENDER  # noqa: E402
from tools.zeno_ledger_node import _body_for_tx_v0, _empty_evidence_v0  # noqa: E402


RESULT_SCHEMA = "zenodex.zeno_ledger.block_gossip_check.v1"
ZERO_ROOT = "0x" + "00" * 32
CHAIN_ID = "zeno-ledger-block-gossip-checknet-0"


def _root(label: str) -> str:
    return hash_v0("block_gossip_check_root", {"label": label})


def _body(*, height: int = 6, label: str = "a") -> dict[str, object]:
    return _body_for_tx_v0(
        chain_id=CHAIN_ID,
        height=height,
        time_ms=1_778_730_000_000 + height,
        sequencer_id="sequencer-block-gossip-checknet-0",
        tx={
            "tx_id": f"gossip-check-{label}",
            "kind": "ZENODEX_TESTNET_FAUCET",
            "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
            "asset": _root("asset"),
            "amount": 100,
        },
    )


def _header(body: dict[str, object]) -> dict[str, object]:
    height = int(body["height"])
    return build_header_v0(
        chain_id=CHAIN_ID,
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=compute_ingress_root_v0(body["ingress"]),  # type: ignore[arg-type]
        tx_root=compute_tx_root_v0(body["transactions"]),  # type: ignore[arg-type]
        pre_state_root=_root("pre"),
        post_state_root=_root("post"),
        app_hash=_root("app"),
        evidence_root=compute_evidence_root_v0(_empty_evidence_v0()),
        body_root=canonical_body_root_v0(body),
        data_availability_root=ZERO_ROOT,
        proof_journal_hash=ZERO_ROOT,
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _envelope() -> dict[str, object]:
    body = _body()
    header = _header(body)
    checkpoint = build_checkpoint_v0(header)
    return build_block_gossip_envelope_v0(
        header=header,
        body=body,
        checkpoint=checkpoint,
        source_node_id="node-a",
        source_peer_url="http://127.0.0.1:8800",
    )


def _case(name: str, fn: Callable[[], object]) -> dict[str, object]:
    try:
        fn()
        return {"name": name, "ok": True, "status": "accepted", "error": None}
    except Exception as exc:
        return {"name": name, "ok": False, "status": "rejected", "error": str(exc)}


def run_check() -> dict[str, object]:
    envelope = _envelope()
    tampered_hash = dict(envelope)
    tampered_hash["envelope_hash"] = _root("tampered-envelope")
    tampered_body = dict(envelope)
    body = dict(tampered_body["body"])  # type: ignore[arg-type]
    body["height"] = int(body["height"]) + 1
    tampered_body["body"] = body
    cases = [
        _case("gossip_envelope_hash_bound", lambda: validate_block_gossip_envelope_v0(envelope)),
        _case("tampered_envelope_hash_rejected", lambda: validate_block_gossip_envelope_v0(tampered_hash)),
        _case("header_body_mismatch_rejected", lambda: validate_block_gossip_envelope_v0(tampered_body)),
    ]
    expected = {
        "gossip_envelope_hash_bound": True,
        "tampered_envelope_hash_rejected": False,
        "header_body_mismatch_rejected": False,
    }
    ok = all(case["ok"] is expected[str(case["name"])] for case in cases)
    return {"schema": RESULT_SCHEMA, "ok": ok, "cases": cases}


def main() -> int:
    result = run_check()
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
