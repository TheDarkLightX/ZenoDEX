#!/usr/bin/env python3
"""Append-only public ledger for permissionless solver rounds."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any, Mapping

# Allow `python3 tools/...` from repo root without needing `-m`.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from tools.permissionless_solver_proof_mining_claim import validate_proof_mining_claim_artifact


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _sha256_obj(obj: Mapping[str, Any], *, domain: str) -> str:
    return sha256_hex(domain_sep_bytes(domain, version=1) + canonical_json_bytes(dict(obj)))


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    return _require_mapping(obj, name=str(path))


def _iter_jsonl(path: Path) -> list[Mapping[str, Any]]:
    if not path.exists():
        return []
    rows: list[Mapping[str, Any]] = []
    for i, raw in enumerate(path.read_text(encoding="utf-8").splitlines()):
        line = raw.strip()
        if not line:
            continue
        obj = json.loads(line)
        rows.append(_require_mapping(obj, name=f"ledger[{i}]"))
    return rows


def _record_hash(body: Mapping[str, Any]) -> str:
    return _sha256_obj(body, domain="permissionless_round_ledger_record")


def _payout_plan_hash(body: Mapping[str, Any]) -> str:
    return _sha256_obj(body, domain="permissionless_solver_payout_plan")


def _extract_reward_artifact(reward_artifact: Mapping[str, Any]) -> dict[str, Any]:
    body = _require_mapping(reward_artifact.get("body"), name="reward_artifact.body")
    schema = _require_str(body.get("schema"), name="reward_artifact.body.schema")
    if schema == "zenodex/permissionless_solver_payout_plan/v1":
        artifact_hash = _require_str(reward_artifact.get("plan_hash"), name="reward_artifact.plan_hash")
        if artifact_hash != _payout_plan_hash(body):
            raise ValueError("plan_hash mismatch")
        winner = _require_mapping(body.get("winner"), name="reward_artifact.body.winner")
        budget = _require_mapping(body.get("budget"), name="reward_artifact.body.budget")
        payout_amount = _require_int(winner.get("payout_amount"), name="reward_artifact.body.winner.payout_amount")
        round_id = _require_str(body.get("round_id"), name="reward_artifact.body.round_id")
        job_digest = _require_str(body.get("job_digest"), name="reward_artifact.body.job_digest")
        if bool(_require_mapping(body.get("conditions"), name="reward_artifact.body.conditions").get("round_ok")) is not True:
            raise ValueError("payout plan requires round_ok")
        if payout_amount < 0:
            raise ValueError("payout_amount must be non-negative")
        reward_pool_before = _require_int(budget.get("reward_pool_before"), name="reward_pool_before")
        reward_pool_after = _require_int(budget.get("reward_pool_after"), name="reward_pool_after")
        if reward_pool_before - payout_amount != reward_pool_after or reward_pool_after < 0:
            raise ValueError("budget conservation mismatch")
        return {
            "schema": schema,
            "artifact_hash": artifact_hash,
            "round_id": round_id,
            "job_digest": job_digest,
            "winner": winner,
            "payout_amount": payout_amount,
            "reward_pool_before": reward_pool_before,
            "reward_pool_after": reward_pool_after,
        }
    elif schema == "zenodex/permissionless_solver_proof_mining_claim/v1":
        return validate_proof_mining_claim_artifact(reward_artifact, require_admissible=True)
    else:
        raise ValueError("unsupported reward artifact schema")


def build_round_ledger_record(
    *,
    round_obj: Mapping[str, Any],
    reward_artifact: Mapping[str, Any],
    prev_record_hash: str,
) -> dict[str, Any]:
    if bool(round_obj.get("ok")) is not True:
        raise ValueError("round must be ok")
    winner = _require_mapping(round_obj.get("winner"), name="winner")
    artifact = _extract_reward_artifact(reward_artifact)
    payout_winner = _require_mapping(artifact.get("winner"), name="reward_artifact.body.winner")

    winner_miner = _require_str(winner.get("miner_id"), name="winner.miner_id")
    payout_miner = _require_str(payout_winner.get("miner_id"), name="reward_artifact.body.winner.miner_id")
    if winner_miner != payout_miner:
        raise ValueError("winner miner mismatch")

    winner_improvement = _require_int(winner.get("improvement_u64"), name="winner.improvement_u64")
    payout_improvement = _require_int(payout_winner.get("improvement_u64"), name="reward_artifact.body.winner.improvement_u64")
    if winner_improvement != payout_improvement:
        raise ValueError("winner improvement mismatch")

    winner_witness = _require_str(winner.get("witness_sha256"), name="winner.witness_sha256")
    payout_witness = _require_str(payout_winner.get("witness_sha256"), name="reward_artifact.body.winner.witness_sha256")
    if winner_witness != payout_witness:
        raise ValueError("winner witness mismatch")

    round_job_digest = _require_str(round_obj.get("job_digest"), name="round.job_digest")
    payout_job_digest = _require_str(artifact.get("job_digest"), name="reward_artifact.body.job_digest")
    if round_job_digest != payout_job_digest:
        raise ValueError("job_digest mismatch")

    round_hash = _sha256_obj(round_obj, domain="permissionless_solver_round")
    body = {
        "schema": "zenodex/permissionless_round_ledger_record/v1",
        "round_id": _require_str(artifact.get("round_id"), name="round_id"),
        "job_digest": round_job_digest,
        "winner": {
            "miner_id": winner_miner,
            "witness_sha256": winner_witness,
            "improvement_u64": winner_improvement,
            "payout_amount": _require_int(artifact.get("payout_amount"), name="payout_amount"),
        },
        "budget": {
            "reward_pool_before": _require_int(artifact.get("reward_pool_before"), name="reward_pool_before"),
            "reward_pool_after": _require_int(artifact.get("reward_pool_after"), name="reward_pool_after"),
        },
        "round_hash": round_hash,
        "reward_artifact_schema": _require_str(artifact.get("schema"), name="reward_artifact_schema"),
        "reward_artifact_hash": _require_str(artifact.get("artifact_hash"), name="reward_artifact_hash"),
        "prev_record_hash": str(prev_record_hash),
    }
    return {"body": body, "record_hash": _record_hash(body)}


def verify_ledger_rows(rows: list[Mapping[str, Any]]) -> tuple[bool, str]:
    prev = ""
    prev_pool_after: int | None = None
    seen_round_ids: set[str] = set()
    seen_artifact_hashes: set[str] = set()
    for idx, row in enumerate(rows):
        body = _require_mapping(row.get("body"), name=f"ledger[{idx}].body")
        if row.get("record_hash") != _record_hash(body):
            return False, f"record_hash mismatch at row {idx}"
        got_prev = body.get("prev_record_hash")
        if got_prev != prev:
            return False, f"prev_record_hash mismatch at row {idx}"
        round_id = _require_str(body.get("round_id"), name=f"ledger[{idx}].body.round_id")
        if round_id in seen_round_ids:
            return False, f"duplicate round_id at row {idx}"
        seen_round_ids.add(round_id)
        artifact_hash = _require_str(body.get("reward_artifact_hash"), name=f"ledger[{idx}].body.reward_artifact_hash")
        if artifact_hash in seen_artifact_hashes:
            return False, f"duplicate reward_artifact_hash at row {idx}"
        seen_artifact_hashes.add(artifact_hash)
        reward_pool_before = _require_int(_require_mapping(body.get("budget"), name=f"ledger[{idx}].body.budget").get("reward_pool_before"), name=f"ledger[{idx}].body.budget.reward_pool_before")
        reward_pool_after = _require_int(_require_mapping(body.get("budget"), name=f"ledger[{idx}].body.budget").get("reward_pool_after"), name=f"ledger[{idx}].body.budget.reward_pool_after")
        payout_amount = _require_int(_require_mapping(body.get("winner"), name=f"ledger[{idx}].body.winner").get("payout_amount"), name=f"ledger[{idx}].body.winner.payout_amount")
        if reward_pool_before - payout_amount != reward_pool_after or reward_pool_after < 0:
            return False, f"budget conservation mismatch at row {idx}"
        if prev_pool_after is not None and reward_pool_before != prev_pool_after:
            return False, f"reward pool continuity mismatch at row {idx}"
        prev_pool_after = reward_pool_after
        prev = _require_str(row.get("record_hash"), name=f"ledger[{idx}].record_hash")
    return True, "ok"


def append_round_record(*, ledger_path: Path, record: Mapping[str, Any]) -> None:
    ledger_path.parent.mkdir(parents=True, exist_ok=True)
    with ledger_path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Append or verify a permissionless round ledger")
    parser.add_argument("--ledger", required=True, help="Ledger JSONL path")
    parser.add_argument("--round", default="", help="Round JSON path for append mode")
    parser.add_argument("--payout-plan", default="", help="Payout-plan JSON path for append mode")
    parser.add_argument("--proof-mining-claim", default="", help="Proof-mining-claim JSON path for append mode")
    parser.add_argument("--verify-only", action="store_true")
    parser.add_argument("--json", action="store_true", help="Emit JSON status for verify-only mode")
    args = parser.parse_args(argv)

    ledger_path = Path(args.ledger).resolve()
    rows = _iter_jsonl(ledger_path)

    if bool(args.verify_only):
        ok, msg = verify_ledger_rows(rows)
        payload = {"schema": "zenodex/permissionless_round_ledger_verify/v1", "ok": ok, "message": msg, "rows": len(rows)}
        if args.json:
            print(json.dumps(payload, sort_keys=True, indent=2))
        else:
            print(msg)
        return 0 if ok else 1

    round_path = Path(str(args.round))
    payout_path = Path(str(args.payout_plan))
    claim_path = Path(str(args.proof_mining_claim))
    if not str(args.round).strip():
        raise SystemExit("--round is required unless --verify-only is set")
    has_payout = bool(str(args.payout_plan).strip())
    has_claim = bool(str(args.proof_mining_claim).strip())
    if has_payout == has_claim:
        raise SystemExit("exactly one of --payout-plan or --proof-mining-claim is required")

    ok, msg = verify_ledger_rows(rows)
    if not ok:
        raise SystemExit(f"existing ledger invalid: {msg}")
    prev = _require_str(rows[-1].get("record_hash"), name="last.record_hash") if rows else ""
    reward_artifact = _load_json(payout_path if has_payout else claim_path)
    record = build_round_ledger_record(
        round_obj=_load_json(round_path),
        reward_artifact=reward_artifact,
        prev_record_hash=prev,
    )
    append_round_record(ledger_path=ledger_path, record=record)
    print(str(ledger_path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
