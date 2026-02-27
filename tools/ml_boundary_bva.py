#!/usr/bin/env python3
"""
Machine learning-driven boundary value analysis (ML-BVA) for ESSO kernels.

This tool generates a replayable boundary-focused test suite by combining:
- deterministic boundary candidate construction
- online UCB1 bandit selection (adaptive candidate prioritization)
- kernel interpreter feedback (success/error boundary behavior)

Output is JSON with concrete `{pre_state, action, params, expected}` cases.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

import yaml

try:
    from esso_gpu_semantics import ensure_esso_on_path
except Exception:  # pragma: no cover - best effort path setup
    ensure_esso_on_path = None  # type: ignore[assignment]


@dataclass(frozen=True)
class Candidate:
    action_id: str
    params: dict[str, int | bool | str]
    boundary_score: float
    boundary_tags: tuple[str, ...]

    def signature(self) -> tuple[str, tuple[tuple[str, object], ...]]:
        return (str(self.action_id), tuple(sorted((str(k), self.params[k]) for k in self.params.keys())))


@dataclass(frozen=True)
class EvalRecord:
    reward: float
    pre_state: dict[str, object]
    action: str
    params: dict[str, object]
    expected: dict[str, object]
    boundary_score: float
    boundary_tags: tuple[str, ...]
    outcome_key: str
    next_state: dict[str, object] | None


def _json_dumps(obj: object) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def _state_sig(state: Mapping[str, object]) -> str:
    return _json_dumps({str(k): state[k] for k in sorted(state.keys(), key=str)})


def int_boundary_points(*, low: int, high: int) -> list[int]:
    if int(low) > int(high):
        raise ValueError("low must be <= high")
    pts: list[int] = []
    for v in (
        int(low),
        int(low) + 1,
        int(high) - 1,
        int(high),
        0,
        1,
        -1,
        (int(low) + int(high)) // 2,
    ):
        if int(low) <= int(v) <= int(high):
            pts.append(int(v))
    out: list[int] = []
    seen: set[int] = set()
    for p in pts:
        if p in seen:
            continue
        seen.add(p)
        out.append(int(p))
    return out


def _int_boundary_tag(*, value: int, low: int, high: int) -> str:
    if int(value) == int(low) - 1:
        return "min-1"
    if int(value) == int(high) + 1:
        return "max+1"
    if int(value) == int(low):
        return "min"
    if int(value) == int(high):
        return "max"
    if int(value) == int(low) + 1 and int(low) + 1 <= int(high):
        return "min+1"
    if int(value) == int(high) - 1 and int(high) - 1 >= int(low):
        return "max-1"
    if int(value) == 0:
        return "zero"
    if int(value) == 1:
        return "+1"
    if int(value) == -1:
        return "-1"
    return "mid"


def _baseline_for_param(*, param_id: str, t: Any) -> int | bool | str:
    kind = str(getattr(t, "kind", ""))
    if kind == "bool":
        return bool(param_id == "auth_ok")
    if kind == "enum":
        syms = list(getattr(t, "symbols", None) or ())
        if not syms:
            raise ValueError(f"empty enum domain: {param_id}")
        return str(syms[0])
    if kind == "int":
        lo = int(getattr(t, "min", 0))
        hi = int(getattr(t, "max", 0))
        if lo <= 0 <= hi:
            return 0
        if lo <= 1 <= hi:
            return 1
        if lo <= -1 <= hi:
            return -1
        return int(lo)
    raise ValueError(f"unsupported param kind: {param_id} -> {kind!r}")


def _boundary_values_for_param(*, t: Any, include_outside: bool = True) -> list[int | bool | str]:
    kind = str(getattr(t, "kind", ""))
    if kind == "bool":
        return [True, False]
    if kind == "enum":
        syms = list(getattr(t, "symbols", None) or ())
        if not syms:
            return []
        return [str(s) for s in syms]
    if kind == "int":
        lo = int(getattr(t, "min", 0))
        hi = int(getattr(t, "max", 0))
        vals = [int(x) for x in int_boundary_points(low=lo, high=hi)]
        if bool(include_outside):
            vals = [int(lo - 1), *vals, int(hi + 1)]
        out: list[int] = []
        seen: set[int] = set()
        for v in vals:
            if v in seen:
                continue
            seen.add(v)
            out.append(v)
        return out
    return []


def _boundary_feature_for_param(*, param_id: str, value: int | bool | str, t: Any) -> tuple[float, str]:
    kind = str(getattr(t, "kind", ""))
    if kind == "bool":
        return (0.35 if bool(value) else 0.2, f"{param_id}=bool:{value}")
    if kind == "enum":
        return (0.3, f"{param_id}=enum:{value}")
    if kind == "int":
        lo = int(getattr(t, "min", 0))
        hi = int(getattr(t, "max", 0))
        iv = int(value)
        tag = _int_boundary_tag(value=iv, low=lo, high=hi)
        score = 0.25
        if tag in {"min", "max"}:
            score = 1.0
        elif tag in {"min+1", "max-1"}:
            score = 0.8
        elif tag in {"zero", "+1", "-1"}:
            score = 0.5
        return (score, f"{param_id}={tag}")
    return (0.0, f"{param_id}=unsupported")


def _build_candidates_for_action(action: Any, *, named_types: Mapping[str, Any], max_candidates: int) -> list[Candidate]:
    params = list(getattr(action, "params", None) or ())
    if not params:
        return [Candidate(action_id=str(action.id), params={}, boundary_score=0.0, boundary_tags=tuple())]

    resolved: dict[str, Any] = {}
    baseline: dict[str, int | bool | str] = {}
    for p in params:
        t = p.type.resolved(named_types) if p.type.kind == "ref" else p.type
        resolved[str(p.id)] = t
        baseline[str(p.id)] = _baseline_for_param(param_id=str(p.id), t=t)

    candidates: list[Candidate] = []
    seen: set[tuple[str, tuple[tuple[str, object], ...]]] = set()

    def add_candidate(param_values: Mapping[str, int | bool | str]) -> None:
        params_obj = {str(k): param_values[k] for k in sorted(param_values.keys(), key=str)}
        sig = (str(action.id), tuple((k, params_obj[k]) for k in params_obj.keys()))
        if sig in seen:
            return
        seen.add(sig)
        scores: list[float] = []
        tags: list[str] = []
        for pid, val in params_obj.items():
            sc, tg = _boundary_feature_for_param(param_id=pid, value=val, t=resolved[pid])
            scores.append(float(sc))
            tags.append(str(tg))
        bscore = (sum(scores) / float(len(scores))) if scores else 0.0
        candidates.append(
            Candidate(
                action_id=str(action.id),
                params=params_obj,
                boundary_score=float(bscore),
                boundary_tags=tuple(sorted(tags)),
            )
        )

    add_candidate(baseline)

    for p in params:
        pid = str(p.id)
        t = resolved[pid]
        vals = _boundary_values_for_param(t=t, include_outside=True)
        for v in vals:
            d = dict(baseline)
            d[pid] = v
            add_candidate(d)

    int_param_ids = [str(p.id) for p in params if str(getattr(resolved[str(p.id)], "kind", "")) == "int"]
    for i in range(len(int_param_ids)):
        for j in range(i + 1, len(int_param_ids)):
            a = int_param_ids[i]
            b = int_param_ids[j]
            ta = resolved[a]
            tb = resolved[b]
            av = int_boundary_points(low=int(getattr(ta, "min", 0)), high=int(getattr(ta, "max", 0)))
            bv = int_boundary_points(low=int(getattr(tb, "min", 0)), high=int(getattr(tb, "max", 0)))
            edge_a = av[:2] + av[-2:]
            edge_b = bv[:2] + bv[-2:]
            for va in edge_a:
                for vb in edge_b:
                    d = dict(baseline)
                    d[a] = int(va)
                    d[b] = int(vb)
                    add_candidate(d)

    candidates.sort(key=lambda c: (float(c.boundary_score), c.signature()), reverse=True)
    if len(candidates) > int(max_candidates):
        candidates = candidates[: int(max_candidates)]
    return candidates


def _state_type_map(ir: Any) -> dict[str, Any]:
    nt = ir.named_types()
    out: dict[str, Any] = {}
    for v in ir.state_vars:
        t = v.type.resolved(nt) if v.type.kind == "ref" else v.type
        out[str(v.id)] = t
    return out


def _state_boundary_hits(state: Mapping[str, object], state_types: Mapping[str, Any]) -> int:
    hits = 0
    for k, t in state_types.items():
        if str(getattr(t, "kind", "")) != "int":
            continue
        lo = getattr(t, "min", None)
        hi = getattr(t, "max", None)
        if lo is None or hi is None:
            continue
        v = state.get(k)
        if not isinstance(v, int) or isinstance(v, bool):
            continue
        if int(v) in {int(lo), int(lo) + 1, int(hi) - 1, int(hi)}:
            hits += 1
    return int(hits)


def _evaluate_candidate(
    *,
    ir: Any,
    ctx: Any,
    state: Mapping[str, object],
    candidate: Candidate,
    state_types: Mapping[str, Any],
) -> EvalRecord:
    from ESSO.kernel.interpreter import Command, StepError, step_ctx  # type: ignore

    pre_state = {str(k): state[k] for k in sorted(state.keys(), key=str)}
    cmd = Command(tag=str(candidate.action_id), args=dict(candidate.params))
    res = step_ctx(dict(pre_state), cmd, ctx)

    reward = float(candidate.boundary_score) * 0.4
    expected: dict[str, object]
    next_state: dict[str, object] | None = None
    outcome_key: str

    if isinstance(res, StepError):
        code = str(res.code)
        expected = {"ok": False, "code": code}
        outcome_key = f"err:{code}"
        if code == "GuardFalse":
            reward += 0.25
        elif code in {"InvalidState", "StateType", "ParamType", "StateShape", "ParamShape"}:
            reward += 0.9
        else:
            reward += 1.1
    else:
        next_state = {str(k): res.state[k] for k in sorted(res.state.keys(), key=str)}
        next_effects = {str(k): res.effects[k] for k in sorted(res.effects.keys(), key=str)}
        expected = {"ok": True, "state": next_state, "effects": next_effects}
        outcome_key = "ok"
        hits = _state_boundary_hits(next_state, state_types)
        reward += 0.8 + 0.12 * float(hits)

    return EvalRecord(
        reward=float(reward),
        pre_state=pre_state,
        action=str(candidate.action_id),
        params={str(k): candidate.params[k] for k in sorted(candidate.params.keys(), key=str)},
        expected=expected,
        boundary_score=float(candidate.boundary_score),
        boundary_tags=tuple(candidate.boundary_tags),
        outcome_key=outcome_key,
        next_state=next_state,
    )


def _select_cases_with_coverage(records: list[EvalRecord], *, want: int) -> list[EvalRecord]:
    rows = sorted(records, key=lambda r: (float(r.reward), float(r.boundary_score)), reverse=True)
    picked: list[EvalRecord] = []
    covered: set[str] = set()
    covered_outcomes: set[str] = set()
    covered_states: set[str] = set()

    for r in rows:
        if len(picked) >= int(want):
            break
        adds_tag = any(t not in covered for t in r.boundary_tags)
        adds_outcome = str(r.outcome_key) not in covered_outcomes
        if not adds_tag and not adds_outcome:
            continue
        picked.append(r)
        for t in r.boundary_tags:
            covered.add(t)
        covered_outcomes.add(str(r.outcome_key))
        covered_states.add(_state_sig(r.pre_state))

    for r in rows:
        if len(picked) >= int(want):
            break
        if r in picked:
            continue
        sig = _state_sig(r.pre_state)
        if sig in covered_states:
            continue
        picked.append(r)
        covered_states.add(sig)

    for r in rows:
        if len(picked) >= int(want):
            break
        if r in picked:
            continue
        picked.append(r)

    return picked[: int(want)]


def _param_l1_distance(a: Mapping[str, object], b: Mapping[str, object]) -> float:
    keys = set(a.keys()) | set(b.keys())
    dist = 0.0
    for k in keys:
        va = a.get(k)
        vb = b.get(k)
        if isinstance(va, bool) or isinstance(vb, bool):
            dist += 0.0 if bool(va) == bool(vb) else 1.0
            continue
        if isinstance(va, int) and not isinstance(va, bool) and isinstance(vb, int) and not isinstance(vb, bool):
            dist += float(abs(int(va) - int(vb)))
            continue
        dist += 0.0 if va == vb else 1.0
    return float(dist)


def _ucb_generate_for_action(
    *,
    ir: Any,
    ctx: Any,
    action: Any,
    initial_state: Mapping[str, object],
    state_types: Mapping[str, Any],
    cases_per_action: int,
    iterations_per_action: int,
    max_candidates_per_action: int,
    max_states: int,
    alpha: float,
    seed: int,
) -> tuple[list[EvalRecord], dict[str, object]]:
    candidates = _build_candidates_for_action(action, named_types=ir.named_types(), max_candidates=max_candidates_per_action)
    if not candidates:
        return [], {"candidate_count": 0, "state_pool_size": 1}

    pulls = [0 for _ in candidates]
    means = [0.0 for _ in candidates]
    total = 0
    gathered: list[EvalRecord] = []
    novelty_seen: set[tuple[str, str, str]] = set()
    seen_outcomes_by_state: dict[str, list[tuple[dict[str, object], str]]] = {}
    rng = random.Random(int(seed))

    s0 = {str(k): initial_state[k] for k in sorted(initial_state.keys(), key=str)}
    state_pool: list[dict[str, object]] = [s0]
    state_seen: set[str] = {_state_sig(s0)}

    iters = max(int(iterations_per_action), int(cases_per_action) * 4, len(candidates) * 2)
    for i in range(iters):
        idx = -1
        zero_pull = [j for j, n in enumerate(pulls) if n == 0]
        if zero_pull:
            best_score = -1e18
            tied: list[int] = []
            for j in zero_pull:
                sc = float(candidates[j].boundary_score)
                if sc > best_score + 1e-12:
                    best_score = sc
                    tied = [j]
                elif abs(sc - best_score) <= 1e-12:
                    tied.append(j)
            idx = tied[int(rng.randrange(len(tied)))]
        if idx < 0:
            best_val = -1e18
            tied = []
            for j in range(len(candidates)):
                exploit = float(means[j])
                explore = float(alpha) * math.sqrt(math.log(float(total) + 1.0) / float(pulls[j]))
                v = exploit + explore
                if v > best_val + 1e-12:
                    best_val = v
                    tied = [j]
                elif abs(v - best_val) <= 1e-12:
                    tied.append(j)
            idx = tied[int(rng.randrange(len(tied)))]

        cand = candidates[idx]
        st = state_pool[int(rng.randrange(len(state_pool)))]
        rec = _evaluate_candidate(ir=ir, ctx=ctx, state=st, candidate=cand, state_types=state_types)

        nov_key = (
            _json_dumps({"a": rec.action, "p": rec.params}),
            str(rec.outcome_key),
            _state_sig(rec.pre_state),
        )
        novelty_bonus = 0.0
        if nov_key not in novelty_seen:
            novelty_seen.add(nov_key)
            novelty_bonus = 0.35
            gathered.append(rec)

        pair_density_bonus = 0.0
        pre_sig = _state_sig(rec.pre_state)
        prior = seen_outcomes_by_state.get(pre_sig, [])
        nearest = None
        nearest_dist = 1e18
        for prior_params, prior_outcome in prior:
            if str(prior_outcome) == str(rec.outcome_key):
                continue
            d = _param_l1_distance(prior_params, rec.params)
            if d < nearest_dist:
                nearest_dist = d
                nearest = d
        if nearest is not None:
            # Reward close-by input pairs that cross outcome boundaries.
            pair_density_bonus = 0.6 / (1.0 + float(nearest))
        seen_outcomes_by_state.setdefault(pre_sig, []).append((dict(rec.params), str(rec.outcome_key)))

        observed = float(rec.reward) + float(novelty_bonus) + float(pair_density_bonus)
        total += 1
        pulls[idx] += 1
        means[idx] += (observed - means[idx]) / float(pulls[idx])

        if rec.next_state is not None and len(state_pool) < int(max_states):
            sig = _state_sig(rec.next_state)
            if sig not in state_seen:
                state_seen.add(sig)
                state_pool.append(dict(rec.next_state))

    selected = _select_cases_with_coverage(gathered, want=int(cases_per_action))
    summary = {
        "candidate_count": int(len(candidates)),
        "iterations": int(iters),
        "state_pool_size": int(len(state_pool)),
        "raw_record_count": int(len(gathered)),
    }
    return selected, summary


def generate_ml_bva_suite(
    *,
    model_path: Path,
    cases_per_action: int,
    iterations_per_action: int,
    max_candidates_per_action: int,
    max_states: int,
    alpha: float,
    seed: int,
) -> dict[str, object]:
    if int(cases_per_action) <= 0:
        raise ValueError("cases_per_action must be > 0")
    if int(iterations_per_action) <= 0:
        raise ValueError("iterations_per_action must be > 0")
    if int(max_candidates_per_action) <= 0:
        raise ValueError("max_candidates_per_action must be > 0")
    if int(max_states) <= 0:
        raise ValueError("max_states must be > 0")
    if float(alpha) <= 0.0:
        raise ValueError("alpha must be > 0")

    if ensure_esso_on_path is not None:
        ensure_esso_on_path()

    try:
        from ESSO.ir.schema import CandidateIR  # type: ignore
        from ESSO.kernel.interpreter import StepError, prepare_step_context  # type: ignore
        from ESSO.kernel.simulate import initial_state  # type: ignore
    except Exception as exc:
        raise RuntimeError("ESSO is required to generate ML-BVA suites") from exc

    obj = yaml.safe_load(model_path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"model YAML is not a mapping: {model_path}")

    ir = CandidateIR.from_json_dict(obj).canonicalized()
    ctx = prepare_step_context(ir)
    if isinstance(ctx, StepError):
        raise RuntimeError(f"invalid model step context: {ctx.code}: {ctx.message}")

    s0 = dict(initial_state(ir))
    state_types = _state_type_map(ir)

    all_cases: list[dict[str, object]] = []
    per_action: dict[str, object] = {}
    for action in list(ir.actions):
        action_id = str(action.id)
        selected, summary = _ucb_generate_for_action(
            ir=ir,
            ctx=ctx,
            action=action,
            initial_state=s0,
            state_types=state_types,
            cases_per_action=int(cases_per_action),
            iterations_per_action=int(iterations_per_action),
            max_candidates_per_action=int(max_candidates_per_action),
            max_states=int(max_states),
            alpha=float(alpha),
            seed=int(seed) + int(sum(ord(ch) for ch in action_id)),
        )
        per_action[action_id] = {"selected": int(len(selected)), **summary}
        for r in selected:
            all_cases.append(
                {
                    "action": r.action,
                    "params": r.params,
                    "pre_state": r.pre_state,
                    "expected": r.expected,
                    "reward": round(float(r.reward), 6),
                    "boundary_score": round(float(r.boundary_score), 6),
                    "boundary_tags": list(r.boundary_tags),
                    "generator": "ml_bva_ucb1",
                }
            )

    out = {
        "schema": "zenodex/ml-boundary-bva/v1",
        "model_path": str(model_path),
        "seed": int(seed),
        "algorithm": {
            "name": "ucb1_boundary_sampler",
            "alpha": float(alpha),
            "cases_per_action": int(cases_per_action),
            "iterations_per_action": int(iterations_per_action),
            "max_candidates_per_action": int(max_candidates_per_action),
            "max_states": int(max_states),
            "pair_density_bonus": True,
            "outside_boundary_candidates": True,
        },
        "summary": {
            "action_count": int(len(per_action)),
            "total_cases": int(len(all_cases)),
            "per_action": per_action,
        },
        "cases": all_cases,
    }
    return out


def _write_json(path: Path, obj: object, *, pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if pretty:
        txt = json.dumps(obj, sort_keys=True, indent=2) + "\n"
    else:
        txt = _json_dumps(obj) + "\n"
    path.write_text(txt, encoding="utf-8")


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--model", type=Path, default=Path("src/kernels/dex/perp_epoch_isolated_v3.yaml"))
    ap.add_argument("--out-json", type=Path, default=Path("tests/kernels/data/perp_epoch_isolated_v3_ml_bva_cases.json"))
    ap.add_argument("--cases-per-action", type=int, default=12)
    ap.add_argument("--iterations-per-action", type=int, default=220)
    ap.add_argument("--max-candidates-per-action", type=int, default=400)
    ap.add_argument("--max-states", type=int, default=128)
    ap.add_argument("--alpha", type=float, default=1.25, help="UCB exploration coefficient.")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    suite = generate_ml_bva_suite(
        model_path=args.model.expanduser().resolve(),
        cases_per_action=int(args.cases_per_action),
        iterations_per_action=int(args.iterations_per_action),
        max_candidates_per_action=int(args.max_candidates_per_action),
        max_states=int(args.max_states),
        alpha=float(args.alpha),
        seed=int(args.seed),
    )
    _write_json(args.out_json.expanduser().resolve(), suite, pretty=bool(args.pretty))
    print(json.dumps(suite["summary"], sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
