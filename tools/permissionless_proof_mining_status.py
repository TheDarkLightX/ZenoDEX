#!/usr/bin/env python3
"""Preflight a proof-mining claim locally or via the HTTP API."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any, Mapping
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.integration.proof_mining_claimability import evaluate_proof_mining_claimability  # noqa: E402


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    return _require_mapping(obj, name=str(path))


def _load_text(path: Path | None) -> str:
    if path is None:
        return ""
    return path.read_text(encoding="utf-8")


def _emit(path: Path | None, payload: Mapping[str, Any]) -> None:
    text = json.dumps(dict(payload), indent=2, sort_keys=True) + "\n"
    if path is None:
        sys.stdout.write(text)
        return
    path.write_text(text, encoding="utf-8")


def _api_result_claimable(result: Mapping[str, Any]) -> bool:
    status = result.get("status")
    return result.get("ok") is True and isinstance(status, Mapping) and status.get("claimable") is True


def _call_api(*, api_url: str, payload: Mapping[str, Any], timeout_s: float) -> Mapping[str, Any]:
    body = json.dumps(dict(payload), separators=(",", ":")).encode("utf-8")
    req = Request(
        api_url.rstrip("/") + "/api/dex/proof_mining_status",
        data=body,
        method="POST",
        headers={"Content-Type": "application/json"},
    )
    try:
        with urlopen(req, timeout=float(timeout_s)) as resp:
            return _require_mapping(json.loads(resp.read().decode("utf-8")), name="api response")
    except HTTPError as exc:
        body_bytes = exc.read()
        try:
            obj = json.loads(body_bytes.decode("utf-8")) if body_bytes else {}
        except Exception:
            obj = {"ok": False, "error": f"http_{exc.code}"}
        return _require_mapping(obj, name="api error response")
    except URLError as exc:
        return {"ok": False, "error": "connection_error", "details": str(exc.reason)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Preflight a proof-mining claim locally or via the API")
    parser.add_argument("--claim", required=True, help="Proof-mining claim JSON path")
    parser.add_argument("--chain-balances", required=True, help="Chain balances JSON path")
    parser.add_argument("--tx-sender-pubkey", required=True)
    parser.add_argument("--expected-proposal-hash", required=True)
    parser.add_argument("--app-state", help="Optional app-state JSON file path")
    parser.add_argument("--proof-mining-context", help="Optional verified proof-mining context JSON file path")
    parser.add_argument("--reward-pool-pubkey", default="", help="Local mode override for reward pool pubkey")
    parser.add_argument("--api-url", default="", help="If set, call the API instead of local evaluation")
    parser.add_argument("--timeout-s", type=float, default=5.0)
    parser.add_argument("--output", help="Optional output JSON path")
    args = parser.parse_args(argv)

    claim = _load_json(Path(args.claim))
    chain_balances = _load_json(Path(args.chain_balances))
    app_state_json = _load_text(Path(args.app_state) if args.app_state else None)
    proof_mining_context = _load_json(Path(args.proof_mining_context)) if args.proof_mining_context else None
    output_path = Path(args.output) if args.output else None

    payload = {
        "app_state_json": app_state_json,
        "chain_balances": dict(chain_balances),
        "claim": dict(claim),
        **({"proof_mining_context": dict(proof_mining_context)} if proof_mining_context is not None else {}),
        "tx_sender_pubkey": str(args.tx_sender_pubkey),
        "expected_proposal_hash": str(args.expected_proposal_hash),
    }

    if str(args.api_url).strip():
        result = _call_api(api_url=str(args.api_url), payload=payload, timeout_s=float(args.timeout_s))
        _emit(output_path, result)
        return 0 if _api_result_claimable(result) else 1

    reward_pool_pubkey = str(args.reward_pool_pubkey).strip() or os.environ.get("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "").strip()
    status = evaluate_proof_mining_claimability(
        reward_pool_pubkey=reward_pool_pubkey or None,
        app_state_json=app_state_json,
        chain_balances=chain_balances,
        claim_artifact=claim,
        tx_sender_pubkey=str(args.tx_sender_pubkey),
        expected_proposal_hash=str(args.expected_proposal_hash),
        proof_mining_context_obj=proof_mining_context,
    )
    result = {"ok": True, "status": status.to_public_dict()}
    _emit(output_path, result)
    return 0 if bool(status.claimable) else 1


if __name__ == "__main__":
    raise SystemExit(main())
