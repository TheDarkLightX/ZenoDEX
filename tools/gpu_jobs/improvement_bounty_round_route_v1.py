#!/usr/bin/env python3
"""
Improvement bounty round (route improvement v1).

This is an *internal* harness to:
- collect multiple miner submissions (witness files),
- verify each deterministically (fail-closed replay),
- compute a deterministic improvement key,
- and optionally emit a Tau-checkable argmax-stream certificate selecting the
  winning submission by a total key:
    (improvement_u64 DESC, tie_break_index ASC).

Notes:
- This round tool does NOT assume miners are honest.
- It does NOT trust GPU computation: only deterministic verification matters.
- It is a prototype for "useful work" token distribution or fee rebates.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

# Allow `python3 tools/gpu_jobs/...` from repo root without needing `-m`.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex  # noqa: E402
from tools.proof_verifiers.route_improvement_v1 import verify_route_improvement_witness  # noqa: E402


U64_MAX = 0xFFFFFFFFFFFFFFFF
U32_MAX = 0xFFFFFFFF
BPS_DENOM = 10_000


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return "sha256:" + h.hexdigest()


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _require_list(value: Any, *, name: str) -> List[Any]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return list(value)


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _job_digest(payload: Mapping[str, Any]) -> str:
    job = _require_mapping(payload.get("job"), name="job")
    pools = _require_list(payload.get("pools"), name="pools")
    pools_norm: List[Mapping[str, Any]] = []
    for i, p in enumerate(pools):
        pools_norm.append(_require_mapping(p, name=f"pools[{i}]"))
    pools_norm.sort(key=lambda d: str(d.get("pool_id", "")))
    data = {"job": dict(job), "pools": [dict(p) for p in pools_norm]}
    return sha256_hex(domain_sep_bytes("improvement_bounty_job", version=1) + canonical_json_bytes(data))


def _route_tiebreak_key(proposal_route: Sequence[Mapping[str, Any]], *, miner_id: str) -> Tuple[int, Tuple[str, ...], str, str]:
    # Reuse the routing module’s tie-break spirit:
    # (hop_count, pool_id sequence, intermediate_asset) + miner_id to break duplicates deterministically.
    hops = list(proposal_route)
    hop_n = int(len(hops))
    pool_ids = tuple(str(_require_mapping(h, name="hop").get("pool_id", "")) for h in hops)
    mid = ""
    if hop_n == 2:
        mid = str(_require_mapping(hops[0], name="hop0").get("asset_out", ""))
    return (hop_n, pool_ids, mid, str(miner_id))


@dataclass(frozen=True)
class Submission:
    miner_id: str
    witness_path: str
    witness_sha256: str
    ok: bool
    error: str
    job_digest: str
    improvement_u64: int
    tiebreak_key: Tuple[int, Tuple[str, ...], str, str]


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise TypeError("witness must be a JSON object")
    return obj


def _parse_submission(arg: str, *, default_miner: str) -> Tuple[str, Path]:
    # Format: miner_id=PATH  (miner_id optional; if missing, uses default_miner)
    s = str(arg)
    if "=" in s:
        miner, p = s.split("=", 1)
        miner_id = miner.strip()
        path_s = p.strip()
        if not miner_id:
            miner_id = default_miner
        return miner_id, Path(path_s)
    return default_miner, Path(s)


def _mk_submission(*, miner_id: str, path: Path) -> Submission:
    payload = _load_json(path)
    job_d = ""
    improvement = 0
    tiebreak = (0, tuple(), "", miner_id)
    ok, err = verify_route_improvement_witness(payload)
    if not ok:
        return Submission(
            miner_id=str(miner_id),
            witness_path=str(path),
            witness_sha256=_sha256_file(path),
            ok=False,
            error=str(err or "rejected"),
            job_digest="",
            improvement_u64=0,
            tiebreak_key=tiebreak,
        )

    job_d = _job_digest(payload)

    baseline = _require_mapping(payload.get("baseline"), name="baseline")
    proposal = _require_mapping(payload.get("proposal"), name="proposal")
    base_out = _require_int(baseline.get("amount_out"), name="baseline.amount_out")
    prop_out = _require_int(proposal.get("amount_out"), name="proposal.amount_out")
    if prop_out < base_out:
        return Submission(
            miner_id=str(miner_id),
            witness_path=str(path),
            witness_sha256=_sha256_file(path),
            ok=False,
            error="proposal.amount_out < baseline.amount_out (should be impossible if verifier passed)",
            job_digest=str(job_d),
            improvement_u64=0,
            tiebreak_key=tiebreak,
        )
    improvement = int(prop_out) - int(base_out)
    if improvement < 0 or improvement > U64_MAX:
        return Submission(
            miner_id=str(miner_id),
            witness_path=str(path),
            witness_sha256=_sha256_file(path),
            ok=False,
            error=f"improvement out of u64 range: {improvement}",
            job_digest=str(job_d),
            improvement_u64=0,
            tiebreak_key=tiebreak,
        )

    proposal_route = _require_list(proposal.get("route"), name="proposal.route")
    tiebreak = _route_tiebreak_key([_require_mapping(h, name="hop") for h in proposal_route], miner_id=str(miner_id))

    return Submission(
        miner_id=str(miner_id),
        witness_path=str(path),
        witness_sha256=_sha256_file(path),
        ok=True,
        error="",
        job_digest=str(job_d),
        improvement_u64=int(improvement),
        tiebreak_key=tiebreak,
    )


def _select_winner(subs: Sequence[Submission]) -> Optional[int]:
    # Winner among verified submissions only.
    valid = [i for i, s in enumerate(subs) if s.ok]
    if not valid:
        return None

    # Canonical ordering for tie-break indices (index asc).
    valid_sorted = sorted(valid, key=lambda i: subs[i].tiebreak_key)
    idx_of: Dict[int, int] = {orig_i: new_idx for new_idx, orig_i in enumerate(valid_sorted)}

    # Max by (improvement_u64, -index)  <=> max key, then smallest index.
    best_i = valid_sorted[0]
    for i in valid_sorted[1:]:
        a = subs[best_i]
        b = subs[i]
        if b.improvement_u64 > a.improvement_u64:
            best_i = i
            continue
        if b.improvement_u64 == a.improvement_u64 and idx_of[i] < idx_of[best_i]:
            best_i = i
    return best_i


def _emit_argmax_stream_cert(
    subs: Sequence[Submission],
    *,
    winner_i: int,
) -> Dict[str, Any]:
    import tools.gpu_argmax_certificate as cert

    valid = [i for i, s in enumerate(subs) if s.ok]
    valid_sorted = sorted(valid, key=lambda i: subs[i].tiebreak_key)
    idx_of: Dict[int, int] = {orig_i: new_idx for new_idx, orig_i in enumerate(valid_sorted)}

    cands: List[cert.Candidate] = []
    for orig_i in valid_sorted:
        idx = int(idx_of[orig_i])
        if idx < 0 or idx > U32_MAX:
            raise ValueError("too many candidates for u32 index")
        key = int(subs[orig_i].improvement_u64)
        if key < 0 or key > U64_MAX:
            raise ValueError("candidate key out of u64 range")
        cands.append(cert.Candidate(key_u64=key, index_u32=idx))

    winner_idx = int(idx_of[winner_i])
    expected_winner = cert.Candidate(key_u64=int(subs[winner_i].improvement_u64), index_u32=winner_idx)

    # Deterministic selection under (key desc, index asc).
    computed = cert._argmax_cpu(cands)
    if computed != expected_winner:
        raise RuntimeError(f"argmax mismatch: computed={computed} expected={expected_winner}")

    steps = cert._emit_steps(winner=computed, cands=cands)
    return {
        "spec_id": "argmax_stream_certificate_v1",
        "winner": {"key": int(computed.key_u64), "index": int(computed.index_u32)},
        "candidates": [{"key": int(c.key_u64), "index": int(c.index_u32)} for c in cands],
        "steps": steps,
    }


def _compute_payout_amount(
    *,
    improvement_u64: int,
    reward_pool_before: int,
    base_reward: int,
    improvement_reward_bps: int,
    max_reward: int,
) -> int:
    for value, name in (
        (improvement_u64, "improvement_u64"),
        (reward_pool_before, "reward_pool_before"),
        (base_reward, "base_reward"),
        (improvement_reward_bps, "improvement_reward_bps"),
        (max_reward, "max_reward"),
    ):
        if not isinstance(value, int) or isinstance(value, bool):
            raise TypeError(f"{name} must be an int")
        if value < 0:
            raise ValueError(f"{name} must be non-negative")
    if improvement_reward_bps > BPS_DENOM:
        raise ValueError("improvement_reward_bps out of range")
    if max_reward < base_reward:
        raise ValueError("max_reward must be >= base_reward")
    if improvement_u64 <= 0 or reward_pool_before <= 0:
        return 0

    variable_reward = (int(improvement_u64) * int(improvement_reward_bps)) // int(BPS_DENOM)
    reward = int(base_reward) + int(variable_reward)
    if reward > int(max_reward):
        reward = int(max_reward)
    if reward > int(reward_pool_before):
        reward = int(reward_pool_before)
    return int(reward)


def _build_payout_plan(
    *,
    round_obj: Mapping[str, Any],
    round_id: str,
    reward_pool_before: int,
    base_reward: int,
    improvement_reward_bps: int,
    max_reward: int,
) -> Dict[str, Any]:
    if not isinstance(round_id, str) or not round_id:
        raise ValueError("round_id must be non-empty")
    if not bool(round_obj.get("ok")):
        raise ValueError("round must be ok")

    winner = _require_mapping(round_obj.get("winner"), name="winner")
    improvement_u64 = _require_int(winner.get("improvement_u64"), name="winner.improvement_u64")
    payout_amount = _compute_payout_amount(
        improvement_u64=improvement_u64,
        reward_pool_before=int(reward_pool_before),
        base_reward=int(base_reward),
        improvement_reward_bps=int(improvement_reward_bps),
        max_reward=int(max_reward),
    )
    payout_body = {
        "schema": "zenodex/permissionless_solver_payout_plan/v1",
        "round_id": str(round_id),
        "job_digest": str(round_obj.get("job_digest") or ""),
        "winner": {
            "miner_id": _require_str(winner.get("miner_id"), name="winner.miner_id"),
            "witness_sha256": _require_str(winner.get("witness_sha256"), name="winner.witness_sha256"),
            "improvement_u64": int(improvement_u64),
            "payout_amount": int(payout_amount),
        },
        "budget": {
            "reward_pool_before": int(reward_pool_before),
            "reward_pool_after": int(int(reward_pool_before) - int(payout_amount)),
            "base_reward": int(base_reward),
            "improvement_reward_bps": int(improvement_reward_bps),
            "max_reward": int(max_reward),
        },
        "conditions": {
            "round_ok": True,
            "positive_improvement": bool(improvement_u64 > 0),
            "winner_only": True,
        },
    }
    payout_hash = sha256_hex(domain_sep_bytes("permissionless_solver_payout_plan", version=1) + canonical_json_bytes(payout_body))
    return {"body": payout_body, "plan_hash": payout_hash}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--submission",
        action="append",
        default=[],
        help="Submission in form miner_id=PATH (miner_id optional). Can be repeated.",
    )
    ap.add_argument("--output", required=True, help="Path to write round result JSON.")
    ap.add_argument("--emit-argmax-steps", default="", help="Optional path to write argmax-stream certificate JSON.")
    ap.add_argument("--emit-payout-plan", default="", help="Optional path to write solver payout plan JSON.")
    ap.add_argument("--round-id", default="", help="Required when --emit-payout-plan is used.")
    ap.add_argument("--reward-pool-before", type=int, default=0, help="Available reward budget before payout planning.")
    ap.add_argument("--base-reward", type=int, default=0, help="Fixed winner reward component.")
    ap.add_argument("--improvement-reward-bps", type=int, default=0, help="Variable winner reward component per improvement unit, scaled by 1e4.")
    ap.add_argument("--max-reward", type=int, default=0, help="Hard cap on winner reward.")
    ap.add_argument(
        "--require-positive-improvement",
        action="store_true",
        help="If set, fail unless winner has improvement_u64 > 0.",
    )
    args = ap.parse_args()

    if not args.submission:
        raise SystemExit("need at least one --submission")

    subs: List[Submission] = []
    for i, raw in enumerate(list(args.submission)):
        miner_id, path = _parse_submission(raw, default_miner=f"miner_{i}")
        subs.append(_mk_submission(miner_id=str(miner_id), path=Path(path)))

    # Enforce single job digest across OK submissions (different jobs are invalid for this round).
    job_digest: str | None = None
    for idx, s in enumerate(list(subs)):
        if not bool(s.ok):
            continue
        if job_digest is None:
            job_digest = s.job_digest
        elif s.job_digest != job_digest:
            # Mark as invalid (job mismatch).
            subs[idx] = Submission(
                miner_id=s.miner_id,
                witness_path=s.witness_path,
                witness_sha256=s.witness_sha256,
                ok=False,
                error="job_digest mismatch vs round job",
                job_digest=s.job_digest,
                improvement_u64=0,
                tiebreak_key=s.tiebreak_key,
            )

    winner_i = _select_winner(subs)
    if winner_i is None:
        out_obj = {
            "schema": "zenodex/improvement_bounty_round/v1",
            "ok": False,
            "error": "no valid submissions",
            "job_digest": job_digest or "",
            "candidates": [
                {
                    "miner_id": s.miner_id,
                    "witness_path": s.witness_path,
                    "witness_sha256": s.witness_sha256,
                    "ok": s.ok,
                    "error": s.error,
                    "improvement_u64": int(s.improvement_u64),
                }
                for s in subs
            ],
        }
        Path(args.output).write_text(json.dumps(out_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        return

    winner = subs[int(winner_i)]
    if bool(args.require_positive_improvement) and int(winner.improvement_u64) <= 0:
        raise SystemExit("winner improvement is not positive")

    cert_obj: Dict[str, Any] = {}
    if str(args.emit_argmax_steps).strip():
        cert_obj = _emit_argmax_stream_cert(subs, winner_i=int(winner_i))
        Path(str(args.emit_argmax_steps)).write_text(json.dumps(cert_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    out_obj = {
        "schema": "zenodex/improvement_bounty_round/v1",
        "ok": True,
        "job_digest": str(job_digest or winner.job_digest),
        "winner": {
            "miner_id": winner.miner_id,
            "witness_path": winner.witness_path,
            "witness_sha256": winner.witness_sha256,
            "improvement_u64": int(winner.improvement_u64),
        },
        "candidates": [
            {
                "miner_id": s.miner_id,
                "witness_path": s.witness_path,
                "witness_sha256": s.witness_sha256,
                "ok": s.ok,
                "error": s.error,
                "job_digest": s.job_digest,
                "improvement_u64": int(s.improvement_u64),
            }
            for s in subs
        ],
        "argmax_certificate": cert_obj or None,
    }
    Path(args.output).write_text(json.dumps(out_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if str(args.emit_payout_plan).strip():
        payout_plan = _build_payout_plan(
            round_obj=out_obj,
            round_id=str(args.round_id),
            reward_pool_before=int(args.reward_pool_before),
            base_reward=int(args.base_reward),
            improvement_reward_bps=int(args.improvement_reward_bps),
            max_reward=int(args.max_reward),
        )
        Path(str(args.emit_payout_plan)).write_text(json.dumps(payout_plan, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
