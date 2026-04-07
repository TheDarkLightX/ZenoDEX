#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
import random
import statistics
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


def _read_json(path: Path, default: Any = None) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _safe_token(text: str, max_len: int = 96) -> str:
    out: list[str] = []
    for ch in str(text):
        if ch.isalnum() or ch in "._-":
            out.append(ch)
        else:
            out.append("_")
    token = "".join(out).strip("._").lower()
    if not token:
        token = "x"
    return token[:max_len]


def _parse_int_list(raw: str) -> list[int]:
    out: list[int] = []
    for chunk in str(raw or "").split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        out.append(int(chunk))
    return out


def _regret_bps(ref_out: int, actual_out: int) -> int:
    ref = int(max(1, ref_out))
    actual = int(max(0, actual_out))
    if actual >= ref:
        return 0
    return int(((ref - actual) * 10_000) // ref)


@dataclass(frozen=True)
class PolicyProfile:
    name: str
    require_route_cert: bool
    require_oracle_fresh: bool
    require_not_expired: bool


@dataclass(frozen=True)
class Candidate:
    cid: str
    max_slippage_bps: int
    max_impact_bps: int
    max_quote_age_s: int
    max_hops: int
    profile: PolicyProfile


_DEFAULT_PROFILES: tuple[PolicyProfile, ...] = (
    PolicyProfile("strict", True, True, True),
    PolicyProfile("no_route_cert", False, True, True),
    PolicyProfile("no_oracle_fresh", True, False, True),
    PolicyProfile("no_deadline", True, True, False),
    PolicyProfile("proofs_only", True, False, False),
    PolicyProfile("throughput", False, False, False),
)


def _policy_profiles(selected: list[str] | None) -> list[PolicyProfile]:
    if not selected:
        return list(_DEFAULT_PROFILES)
    by_name = {p.name: p for p in _DEFAULT_PROFILES}
    out: list[PolicyProfile] = []
    for name in selected:
        key = str(name).strip()
        if key in by_name:
            out.append(by_name[key])
    if not out:
        raise ValueError("no valid policy profiles selected")
    return out


def _candidate_space(
    *,
    max_slippage_bps: list[int],
    max_impact_bps: list[int],
    max_quote_age_s: list[int],
    max_hops: list[int],
    profiles: list[PolicyProfile],
) -> list[Candidate]:
    out: list[Candidate] = []
    for slip, impact, age, hops, profile in itertools.product(
        sorted(set(max_slippage_bps)),
        sorted(set(max_impact_bps)),
        sorted(set(max_quote_age_s)),
        sorted(set(max_hops)),
        profiles,
    ):
        if slip <= 0 or impact <= 0 or age <= 0 or hops <= 0:
            continue
        cid = _safe_token(f"r{slip}_i{impact}_a{age}_h{hops}_{profile.name}")
        out.append(
            Candidate(
                cid=cid,
                max_slippage_bps=int(slip),
                max_impact_bps=int(impact),
                max_quote_age_s=int(age),
                max_hops=int(hops),
                profile=profile,
            )
        )
    return out


def _sample_candidates(cands: list[Candidate], *, max_candidates: int, seed: int) -> list[Candidate]:
    if len(cands) <= max_candidates:
        return sorted(cands, key=lambda c: c.cid)
    rng = random.Random(int(seed))
    picks = list(cands)
    rng.shuffle(picks)
    return sorted(picks[: int(max_candidates)], key=lambda c: c.cid)


def _render_candidate_spec(c: Candidate) -> str:
    req_route = "1:sbf" if c.profile.require_route_cert else "0:sbf"
    req_fresh = "1:sbf" if c.profile.require_oracle_fresh else "0:sbf"
    req_expiry = "1:sbf" if c.profile.require_not_expired else "0:sbf"
    slip_hex = f"#x{int(c.max_slippage_bps):08X}"
    impact_hex = f"#x{int(c.max_impact_bps):08X}"
    age_hex = f"#x{int(c.max_quote_age_s):08X}"
    hops_hex = f"#x{int(c.max_hops):08X}"

    return f"""# Tau Frontier Candidate - Regret-Minimizing Swap Gate
# Candidate: {c.cid}
# Profile: {c.profile.name}
# max_slippage_bps={c.max_slippage_bps}, max_impact_bps={c.max_impact_bps}, max_quote_age_s={c.max_quote_age_s}, max_hops={c.max_hops}
#
# Stream mapping:
# i1 = observed_regret_bps (bv[32])
# i2 = observed_impact_bps (bv[32])
# i3 = quote_age_s (bv[32])
# i4 = hop_count (bv[32])
# i5 = route_cert_ok (sbf)
# i6 = oracle_fresh_ok (sbf)
# i7 = not_expired_ok (sbf)
# i8 = binding_ok (sbf)
# o1 = params_ok
# o2 = regret_ok
# o3 = freshness_ok
# o4 = path_ok
# o5 = certs_ok
# o6 = execute_ok

set charvar off

max_safe_32() := {{ #x00068DB8 }}:bv[32].
max_bps() := {{ #x00002710 }}:bv[32].
slip_bps() := {{ {slip_hex} }}:bv[32].
impact_bps() := {{ {impact_hex} }}:bv[32].
max_age_s() := {{ {age_hex} }}:bv[32].
max_hops() := {{ {hops_hex} }}:bv[32].

safe_ok(v : bv[32]) := v <= max_safe_32().
rate_ok(v : bv[32]) := v <= max_bps().
params_ok(obs_regret_bps : bv[32], obs_impact_bps : bv[32], age_s : bv[32], hops : bv[32]) := safe_ok(obs_regret_bps) && safe_ok(obs_impact_bps) && rate_ok(obs_regret_bps) && rate_ok(obs_impact_bps) && rate_ok(slip_bps()) && rate_ok(impact_bps()) && (hops > {{ #x00000000 }}:bv[32]).
regret_ok(obs_regret_bps : bv[32], obs_impact_bps : bv[32]) := (obs_regret_bps <= slip_bps()) && (obs_impact_bps <= impact_bps()).
freshness_ok(age_s : bv[32]) := age_s <= max_age_s().
path_ok(hops : bv[32]) := hops <= max_hops().
flag_ok(req : sbf, flag : sbf) := (req = 0:sbf) || (flag = 1:sbf).
certs_ok(route_cert_ok : sbf, oracle_fresh_ok : sbf, not_expired_ok : sbf, binding_ok : sbf) := flag_ok({req_route}, route_cert_ok) && flag_ok({req_fresh}, oracle_fresh_ok) && flag_ok({req_expiry}, not_expired_ok) && (binding_ok = 1:sbf).
execute_ok(obs_regret_bps : bv[32], obs_impact_bps : bv[32], age_s : bv[32], hops : bv[32], route_cert_ok : sbf, oracle_fresh_ok : sbf, not_expired_ok : sbf, binding_ok : sbf) := params_ok(obs_regret_bps, obs_impact_bps, age_s, hops) && regret_ok(obs_regret_bps, obs_impact_bps) && freshness_ok(age_s) && path_ok(hops) && certs_ok(route_cert_ok, oracle_fresh_ok, not_expired_ok, binding_ok).

always
  (o1[t]:sbf = 1:sbf <-> params_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])) &&
  (o2[t]:sbf = 1:sbf <-> regret_ok(i1[t]:bv[32], i2[t]:bv[32])) &&
  (o3[t]:sbf = 1:sbf <-> freshness_ok(i3[t]:bv[32])) &&
  (o4[t]:sbf = 1:sbf <-> path_ok(i4[t]:bv[32])) &&
  (o5[t]:sbf = 1:sbf <-> certs_ok(i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf)) &&
  (o6[t]:sbf = 1:sbf <-> execute_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32], i5[t]:sbf, i6[t]:sbf, i7[t]:sbf, i8[t]:sbf)).
"""


def _make_default_scenario(*, n: int, seed: int) -> list[dict[str, int]]:
    rng = random.Random(int(seed))
    out: list[dict[str, int]] = []
    for _ in range(int(max(1, n))):
        expected = rng.randint(100, 60_000)
        ref = max(1, (expected * rng.randint(9600, 10400)) // 10_000)
        mode = rng.random()
        if mode < 0.68:
            actual = max(1, (ref * rng.randint(9850, 10_100)) // 10_000)
        elif mode < 0.90:
            actual = max(1, (ref * rng.randint(8500, 9849)) // 10_000)
        else:
            actual = max(1, (ref * rng.randint(10_101, 11_000)) // 10_000)

        quote_age = rng.randint(0, 600)
        hops = rng.randint(1, 4)

        route_cert_ok = 1 if rng.random() < 0.92 else 0
        oracle_fresh_ok = 1 if (quote_age <= 120 and rng.random() < 0.97) or (quote_age > 120 and rng.random() < 0.15) else 0
        not_expired_ok = 1 if rng.random() < 0.93 else 0
        binding_ok = 1 if rng.random() < 0.98 else 0

        out.append(
            {
                "expected_out": int(expected),
                "actual_out": int(actual),
                "ref_out": int(ref),
                "observed_regret_bps": int(_regret_bps(ref, actual)),
                "observed_impact_bps": int(abs((expected - actual) * 10_000) // max(1, expected)),
                "quote_age_s": int(quote_age),
                "hop_count": int(hops),
                "route_cert_ok": int(route_cert_ok),
                "oracle_fresh_ok": int(oracle_fresh_ok),
                "not_expired_ok": int(not_expired_ok),
                "binding_ok": int(binding_ok),
            }
        )
    return out


def _load_scenario(path: Path | None, *, n: int, seed: int) -> list[dict[str, int]]:
    if path is None:
        return _make_default_scenario(n=n, seed=seed)
    obj = _read_json(path, default=[])
    if not isinstance(obj, list):
        raise ValueError("scenario file must contain a list")
    out: list[dict[str, int]] = []
    for idx, row in enumerate(obj):
        if not isinstance(row, dict):
            raise ValueError(f"scenario row {idx} must be an object")
        out.append(
            {
                "expected_out": int(row.get("expected_out", 0)),
                "actual_out": int(row.get("actual_out", 0)),
                "ref_out": int(row.get("ref_out", 0)),
                "observed_regret_bps": int(row.get("observed_regret_bps", 0)),
                "observed_impact_bps": int(row.get("observed_impact_bps", 0)),
                "quote_age_s": int(row.get("quote_age_s", 0)),
                "hop_count": int(row.get("hop_count", 0)),
                "route_cert_ok": int(row.get("route_cert_ok", 0)),
                "oracle_fresh_ok": int(row.get("oracle_fresh_ok", 0)),
                "not_expired_ok": int(row.get("not_expired_ok", 0)),
                "binding_ok": int(row.get("binding_ok", 0)),
            }
        )
    if not out:
        raise ValueError("scenario is empty")
    return out


def _to_tau_steps(rows: Iterable[dict[str, int]]) -> list[dict[str, int]]:
    out: list[dict[str, int]] = []
    for r in rows:
        out.append(
            {
                "i1": int(r["observed_regret_bps"]),
                "i2": int(r["observed_impact_bps"]),
                "i3": int(r["quote_age_s"]),
                "i4": int(r["hop_count"]),
                "i5": int(r["route_cert_ok"]),
                "i6": int(r["oracle_fresh_ok"]),
                "i7": int(r["not_expired_ok"]),
                "i8": int(r["binding_ok"]),
            }
        )
    return out


def _p95(values: list[int]) -> int:
    if not values:
        return 0
    vals = sorted(int(v) for v in values)
    idx = int(round((len(vals) - 1) * 0.95))
    return int(vals[min(max(idx, 0), len(vals) - 1)])


def _complexity_score(spec_text: str) -> tuple[int, dict[str, int]]:
    line_count = len([ln for ln in spec_text.splitlines() if ln.strip()])
    char_count = len(spec_text)
    and_count = spec_text.count("&&")
    or_count = spec_text.count("||")
    implication_count = spec_text.count("->")
    complexity = line_count + and_count + or_count + implication_count + (char_count // 40)
    score = int(round(10_000 / (1.0 + (complexity / 80.0))))
    return score, {
        "line_count": int(line_count),
        "char_count": int(char_count),
        "and_count": int(and_count),
        "or_count": int(or_count),
        "implication_count": int(implication_count),
        "complexity_units": int(complexity),
    }


def _dominates(a: list[int], b: list[int]) -> bool:
    ge = all(int(x) >= int(y) for x, y in zip(a, b))
    gt = any(int(x) > int(y) for x, y in zip(a, b))
    return ge and gt


def _frontier(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for i, r in enumerate(rows):
        if not r.get("ok"):
            continue
        rv = [int(x) for x in r.get("vector", [])]
        dominated = False
        for j, o in enumerate(rows):
            if i == j or not o.get("ok"):
                continue
            ov = [int(x) for x in o.get("vector", [])]
            if _dominates(ov, rv):
                dominated = True
                break
        if not dominated:
            out.append(r)
    out.sort(key=lambda x: (float(x.get("objective", 0.0)), str(x.get("candidate_id", ""))), reverse=True)
    return out


def _execute_policy_python(row: dict[str, int], c: Candidate) -> bool:
    obs_regret = int(row["observed_regret_bps"])
    obs_impact = int(row["observed_impact_bps"])
    age = int(row["quote_age_s"])
    hops = int(row["hop_count"])
    route_ok = int(row["route_cert_ok"]) == 1
    fresh_ok = int(row["oracle_fresh_ok"]) == 1
    expiry_ok = int(row["not_expired_ok"]) == 1
    binding_ok = int(row["binding_ok"]) == 1

    params_ok = (0 <= obs_regret <= 10_000) and (0 <= obs_impact <= 10_000) and (hops > 0)
    regret_ok = (obs_regret <= int(c.max_slippage_bps)) and (obs_impact <= int(c.max_impact_bps))
    freshness_ok = age <= int(c.max_quote_age_s)
    path_ok = hops <= int(c.max_hops)
    certs_ok = (
        (route_ok or (not bool(c.profile.require_route_cert)))
        and (fresh_ok or (not bool(c.profile.require_oracle_fresh)))
        and (expiry_ok or (not bool(c.profile.require_not_expired)))
        and binding_ok
    )
    return bool(params_ok and regret_ok and freshness_ok and path_ok and certs_ok)


def _evaluate_candidate(
    *,
    spec_path: Path,
    candidate: Candidate,
    scenario: list[dict[str, int]],
) -> dict[str, Any]:
    spec_text = spec_path.read_text(encoding="utf-8")
    complexity_score, complexity_meta = _complexity_score(spec_text)

    started = time.time()
    accepts = 0
    unsafe_accepts = 0
    accepted_regrets: list[int] = []

    stale_accepts = 0
    route_bad_accepts = 0
    expired_accepts = 0
    unbound_accepts = 0

    for row in scenario:
        execute_ok = _execute_policy_python(row, candidate)
        if not execute_ok:
            continue
        accepts += 1
        regret = _regret_bps(int(row["ref_out"]), int(row["actual_out"]))
        accepted_regrets.append(int(regret))

        unsafe = False
        if int(row["route_cert_ok"]) != 1:
            route_bad_accepts += 1
            unsafe = True
        if int(row["oracle_fresh_ok"]) != 1:
            stale_accepts += 1
            unsafe = True
        if int(row["not_expired_ok"]) != 1:
            expired_accepts += 1
            unsafe = True
        if int(row["binding_ok"]) != 1:
            unbound_accepts += 1
            unsafe = True
        if unsafe:
            unsafe_accepts += 1

    elapsed_s = float(time.time() - started)

    total = int(len(scenario))
    accept_rate = float(accepts) / float(total) if total > 0 else 0.0
    unsafe_rate = float(unsafe_accepts) / float(max(1, accepts))
    avg_regret = float(statistics.mean(accepted_regrets)) if accepted_regrets else float("inf")
    p95_regret = int(_p95(accepted_regrets)) if accepted_regrets else 10_000

    safety_score = int(round(10_000.0 * max(0.0, 1.0 - unsafe_rate)))
    regret_score = 0 if not accepted_regrets else int(round(max(0.0, 10_000.0 - min(10_000.0, avg_regret))))
    fill_score = int(round(10_000.0 * accept_rate))
    per_step_us = (elapsed_s * 1_000_000.0) / float(max(1, total))
    speed_score = int(round(10_000.0 / (1.0 + (per_step_us / 70.0))))

    vector = [
        int(safety_score),
        int(regret_score),
        int(fill_score),
        int(speed_score),
        int(complexity_score),
    ]

    objective = (
        0.40 * float(safety_score)
        + 0.25 * float(regret_score)
        + 0.20 * float(fill_score)
        + 0.10 * float(speed_score)
        + 0.05 * float(complexity_score)
    )

    return {
        "ok": True,
        "candidate_id": candidate.cid,
        "spec_path": str(spec_path),
        "profile": candidate.profile.name,
        "eval_mode": "python_oracle",
        "params": {
            "max_slippage_bps": int(candidate.max_slippage_bps),
            "max_impact_bps": int(candidate.max_impact_bps),
            "max_quote_age_s": int(candidate.max_quote_age_s),
            "max_hops": int(candidate.max_hops),
            "require_route_cert": bool(candidate.profile.require_route_cert),
            "require_oracle_fresh": bool(candidate.profile.require_oracle_fresh),
            "require_not_expired": bool(candidate.profile.require_not_expired),
        },
        "metrics": {
            "steps": int(total),
            "accept_count": int(accepts),
            "accept_rate": float(accept_rate),
            "unsafe_accept_count": int(unsafe_accepts),
            "unsafe_accept_rate": float(unsafe_rate),
            "avg_regret_bps_accepted": (None if not accepted_regrets else float(avg_regret)),
            "p95_regret_bps_accepted": int(p95_regret),
            "stale_accept_count": int(stale_accepts),
            "route_bad_accept_count": int(route_bad_accepts),
            "expired_accept_count": int(expired_accepts),
            "unbound_accept_count": int(unbound_accepts),
            "elapsed_s": float(elapsed_s),
            "per_step_us": float(per_step_us),
        },
        "scores": {
            "safety": int(safety_score),
            "regret": int(regret_score),
            "fill": int(fill_score),
            "speed": int(speed_score),
            "simplicity": int(complexity_score),
        },
        "vector": vector,
        "objective": float(objective),
        "complexity": complexity_meta,
    }


def _tau_probe_candidate(
    *,
    tau_bin: str,
    spec_path: Path,
    candidate: Candidate,
    scenario: list[dict[str, int]],
    timeout_s: float,
) -> dict[str, Any]:
    steps = _to_tau_steps(scenario)
    started = time.time()
    try:
        outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=float(timeout_s))
    except Exception as exc:
        return {
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
            "elapsed_s": float(time.time() - started),
        }

    matches = 0
    total = len(steps)
    mismatches: list[dict[str, Any]] = []
    for idx, row in enumerate(scenario):
        py_execute = _execute_policy_python(row, candidate)
        tau_execute = int(outputs.get(idx, {}).get("o6", 0)) == 1
        if py_execute == tau_execute:
            matches += 1
            continue
        mismatches.append(
            {
                "step": int(idx),
                "python_execute_ok": bool(py_execute),
                "tau_execute_ok": bool(tau_execute),
                "row": dict(row),
                "tau_outputs": dict(outputs.get(idx, {})),
            }
        )
    return {
        "ok": True,
        "steps": int(total),
        "matches": int(matches),
        "mismatches": int(total - matches),
        "agreement_rate": (float(matches) / float(total)) if total > 0 else 1.0,
        "mismatch_examples": mismatches[:5],
        "elapsed_s": float(time.time() - started),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Tau frontier explorer for regret-focused spec search.")
    ap.add_argument("--out-dir", type=Path, default=Path("runs/tau_frontier_explorer/latest"))
    ap.add_argument("--scenario-json", type=Path, default=None, help="Optional scenario rows JSON (list of objects).")
    ap.add_argument("--scenario-size", type=int, default=256)
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--max-candidates", type=int, default=48)

    ap.add_argument("--max-slippage-bps", type=str, default="25,50,75,100,150,200")
    ap.add_argument("--max-impact-bps", type=str, default="50,100,150,200,300")
    ap.add_argument("--max-quote-age-s", type=str, default="20,60,120,300")
    ap.add_argument("--max-hops", type=str, default="1,2,3")

    ap.add_argument("--tau-probe-top-k", type=int, default=0, help="Optional: run real Tau evaluation on top-K frontier candidates.")
    ap.add_argument("--tau-probe-steps", type=int, default=1, help="Scenario prefix length for Tau probe runs.")
    ap.add_argument("--tau-probe-timeout-s", type=float, default=45.0, help="Timeout per Tau-probed candidate.")

    ap.add_argument(
        "--profile",
        action="append",
        default=[],
        help=(
            "Optional profile(s): strict,no_route_cert,no_oracle_fresh,no_deadline,proofs_only,throughput. "
            "Repeatable. Default uses all."
        ),
    )
    args = ap.parse_args()

    out_dir = (ROOT / args.out_dir).resolve() if not args.out_dir.is_absolute() else args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    tau_bin = find_tau_bin(ROOT)

    scenario_path = None
    if args.scenario_json is not None:
        scenario_path = (ROOT / args.scenario_json).resolve() if not args.scenario_json.is_absolute() else args.scenario_json

    scenario = _load_scenario(scenario_path, n=int(args.scenario_size), seed=int(args.seed))
    _write_json(out_dir / "scenario.json", scenario)

    profiles = _policy_profiles([str(x) for x in list(args.profile or [])])
    cands_all = _candidate_space(
        max_slippage_bps=_parse_int_list(args.max_slippage_bps),
        max_impact_bps=_parse_int_list(args.max_impact_bps),
        max_quote_age_s=_parse_int_list(args.max_quote_age_s),
        max_hops=_parse_int_list(args.max_hops),
        profiles=profiles,
    )
    candidates = _sample_candidates(cands_all, max_candidates=int(max(1, args.max_candidates)), seed=int(args.seed))

    cand_dir = out_dir / "candidates"
    cand_dir.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, Any]] = []
    started = time.time()
    for i, cand in enumerate(candidates, start=1):
        spec_text = _render_candidate_spec(cand)
        spec_path = cand_dir / f"{cand.cid}.tau"
        spec_path.write_text(spec_text, encoding="utf-8")

        rec = _evaluate_candidate(spec_path=spec_path, candidate=cand, scenario=scenario)
        rec["index"] = int(i)
        rows.append(rec)

    frontier = _frontier(rows)

    if int(args.tau_probe_top_k) > 0:
        if not tau_bin:
            for row in frontier[: int(max(0, args.tau_probe_top_k))]:
                row["tau_probe"] = {"ok": False, "error": "tau_binary_not_found"}
        else:
            for row in frontier[: int(max(0, args.tau_probe_top_k))]:
                cid = str(row.get("candidate_id", ""))
                cand = next((c for c in candidates if c.cid == cid), None)
                if cand is None:
                    row["tau_probe"] = {"ok": False, "error": "candidate_not_found"}
                    continue
                probe_steps = scenario[: int(max(1, args.tau_probe_steps))]
                row["tau_probe"] = _tau_probe_candidate(
                    tau_bin=str(tau_bin),
                    spec_path=cand_dir / f"{cid}.tau",
                    candidate=cand,
                    scenario=probe_steps,
                    timeout_s=float(args.tau_probe_timeout_s),
                )

    pack = {
        "schema": "zenodex/tau-frontier-explorer/v1",
        "created_at": int(time.time()),
        "tau_bin": (None if not tau_bin else str(tau_bin)),
        "config": {
            "seed": int(args.seed),
            "scenario_size": int(len(scenario)),
            "scenario_json": (None if scenario_path is None else str(scenario_path)),
            "max_candidates": int(args.max_candidates),
            "search_space_size": int(len(cands_all)),
            "profiles": [p.name for p in profiles],
            "max_slippage_bps": _parse_int_list(args.max_slippage_bps),
            "max_impact_bps": _parse_int_list(args.max_impact_bps),
            "max_quote_age_s": _parse_int_list(args.max_quote_age_s),
            "max_hops": _parse_int_list(args.max_hops),
            "tau_probe_top_k": int(args.tau_probe_top_k),
            "tau_probe_steps": int(args.tau_probe_steps),
            "tau_probe_timeout_s": float(args.tau_probe_timeout_s),
        },
        "counts": {
            "evaluated": int(len(rows)),
            "ok": int(sum(1 for r in rows if r.get("ok"))),
            "errors": int(sum(1 for r in rows if not r.get("ok"))),
            "frontier": int(len(frontier)),
        },
        "elapsed_s": float(time.time() - started),
        "results": rows,
        "frontier": frontier,
    }

    _write_json(out_dir / "tau_frontier_report.json", pack)
    _write_json(out_dir / "tau_frontier_frontier.json", frontier)

    summary = {
        "ok": True,
        "out_dir": str(out_dir),
        "evaluated": int(len(rows)),
        "frontier": int(len(frontier)),
        "best": (None if not frontier else frontier[0].get("candidate_id")),
    }
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
