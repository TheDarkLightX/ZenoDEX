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
import hashlib
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
    is_baseline: bool = False

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


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _portable_path(path: Path) -> str:
    """
    Return a path string stable across machines when possible.

    If `path` is inside the repo, emit a repo-relative POSIX path; otherwise keep
    the original user-supplied path string.
    """
    p = path.expanduser()
    if not p.is_absolute():
        return p.as_posix()
    try:
        rel = p.resolve().relative_to(_repo_root())
        return rel.as_posix()
    except Exception:
        return p.as_posix()


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
        add_baseline = param_values == baseline
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
                is_baseline=bool(add_baseline),
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
        baseline = None
        for c in candidates:
            if c.is_baseline:
                baseline = c
                break
        candidates = candidates[: int(max_candidates)]
        if baseline is not None and baseline not in candidates:
            # Preserve the baseline candidate for reachability exploration.
            candidates[-1] = baseline
    return candidates


def _state_type_map(ir: Any) -> dict[str, Any]:
    nt = ir.named_types()
    out: dict[str, Any] = {}
    for v in ir.state_vars:
        t = v.type.resolved(nt) if v.type.kind == "ref" else v.type
        out[str(v.id)] = t
    return out


def _state_boundary_values_for_var(t: Any) -> list[int | bool | str]:
    kind = str(getattr(t, "kind", ""))
    if kind == "bool":
        return [True, False]
    if kind == "enum":
        syms = list(getattr(t, "symbols", None) or ())
        return [str(s) for s in syms]
    if kind == "int":
        lo = int(getattr(t, "min", 0))
        hi = int(getattr(t, "max", 0))
        # State seeds must remain in-domain; outside points are filtered later via
        # interpreter errors, but in-domain seeding avoids needless rejects.
        return [int(x) for x in int_boundary_points(low=lo, high=hi)]
    return []


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


def _best_baseline_candidate(candidates: list[Candidate]) -> Candidate:
    for c in candidates:
        if c.is_baseline:
            return c
    # Should never happen (baseline is always added), but fail-closed if it does.
    return candidates[0]


def _state_pool_replace(
    *,
    pool: list[dict[str, object]],
    pool_scores: list[int],
    new_state: dict[str, object],
    new_score: int,
    seed_rng: random.Random,
) -> None:
    """
    Replace a state in a fixed-size pool to keep boundary-dense states.

    Deterministic posture:
    - Replace the lowest-score state; tie-break by lexicographic state signature.
    """
    if not pool:
        pool.append(dict(new_state))
        pool_scores.append(int(new_score))
        return
    min_score = min(pool_scores)
    if int(new_score) < int(min_score):
        # Not better; keep pool stable.
        return

    # Find all lowest-score indices.
    lows = [i for i, sc in enumerate(pool_scores) if int(sc) == int(min_score)]
    if len(lows) == 1:
        idx = lows[0]
    else:
        # Break ties deterministically using state sig, and as a last resort
        # a seeded RNG (to avoid quadratic scans when many ties exist).
        best_sig = None
        best_idx = lows[0]
        for i in lows:
            sig = _state_sig(pool[i])
            if best_sig is None or sig < best_sig:
                best_sig = sig
                best_idx = i
        idx = best_idx
        # If new state is identical to the best tie, don't churn.
        if _state_sig(pool[idx]) == _state_sig(new_state):
            return

    pool[idx] = dict(new_state)
    pool_scores[idx] = int(new_score)


def _seed_state_pool_via_boundary_mutations(
    *,
    ir: Any,
    ctx: Any,
    initial: Mapping[str, object],
    state_types: Mapping[str, Any],
    validator_action_id: str,
    validator_candidate: Candidate,
    max_states: int,
    seed_steps: int,
    seed_width: int,
    seed: int,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    """
    Seed a state pool by mutating *state variables* to boundary values.

    This is primarily useful for "calculator" kernels whose actions do not
    transition state (updates=[]), so reachability-based MCMC cannot explore
    alternative pre-states.

    We validate candidate states by attempting a single interpreter step with a
    known-good (baseline) command; any state that triggers a state-shape/type
    error is rejected.
    """
    rng = random.Random(int(seed))
    s0 = {str(k): initial[k] for k in sorted(initial.keys(), key=str)}
    pool: list[dict[str, object]] = [dict(s0)]
    pool_scores: list[int] = [_state_boundary_hits(s0, state_types)]
    seen: set[str] = {_state_sig(s0)}

    # Candidate variables to mutate.
    var_ids: list[str] = []
    values_by_var: dict[str, list[int | bool | str]] = {}
    for vid in sorted(state_types.keys(), key=str):
        t = state_types[vid]
        vals = _state_boundary_values_for_var(t)
        if not vals:
            continue
        var_ids.append(str(vid))
        values_by_var[str(vid)] = vals

    accepted = 0
    rejected = 0
    if not var_ids or int(seed_steps) <= 0:
        return pool, {
            "enabled": True,
            "seed_steps": int(seed_steps),
            "seed_width": int(seed_width),
            "candidate_var_count": int(len(var_ids)),
            "accepted": int(accepted),
            "rejected": int(rejected),
        }

    width = max(1, min(int(seed_width), len(var_ids)))
    for _t in range(int(seed_steps)):
        if len(pool) >= int(max_states):
            break
        picked = rng.sample(var_ids, k=width) if width < len(var_ids) else list(var_ids)
        st = dict(s0)
        for vid in picked:
            vals = values_by_var.get(str(vid), [])
            if not vals:
                continue
            st[str(vid)] = vals[int(rng.randrange(len(vals)))]

        rec = _evaluate_candidate(ir=ir, ctx=ctx, state=st, candidate=validator_candidate, state_types=state_types)
        if rec.expected.get("ok", False):
            ok = True
        else:
            code = str(rec.expected.get("code", ""))
            ok = code not in {"InvalidState", "StateType", "StateShape"}
        if not ok:
            rejected += 1
            continue

        sig = _state_sig(st)
        if sig in seen:
            continue
        seen.add(sig)
        accepted += 1

        score = _state_boundary_hits(st, state_types)
        if len(pool) < int(max_states):
            pool.append(dict(st))
            pool_scores.append(int(score))
        else:
            _state_pool_replace(pool=pool, pool_scores=pool_scores, new_state=st, new_score=score, seed_rng=rng)

    summary = {
        "enabled": True,
        "seed_steps": int(seed_steps),
        "seed_width": int(seed_width),
        "candidate_var_count": int(len(var_ids)),
        "accepted": int(accepted),
        "rejected": int(rejected),
        "state_pool_size": int(len(pool)),
        "unique_states_seen": int(len(seen)),
        "validator_action_id": str(validator_action_id),
    }
    return pool, summary


def _build_global_state_pool_mcmc(
    *,
    ir: Any,
    ctx: Any,
    initial_state: Mapping[str, object],
    state_types: Mapping[str, Any],
    candidates_by_action: Mapping[str, list[Candidate]],
    max_states: int,
    seed_state_boundaries: bool,
    state_seed_steps: int,
    state_seed_width: int,
    walk_steps: int,
    reset_prob: float,
    baseline_prob: float,
    top_k_candidates: int,
    seed: int,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    """
    Build a global pre-state pool via a deterministic Markov-chain random walk.

    Motivation:
    Some actions are only reachable after other actions (e.g. settle_epoch after
    publish_clearing_price). Per-action sampling from only the kernel init state
    misses these success paths.
    """
    rng = random.Random(int(seed))

    s0 = {str(k): initial_state[k] for k in sorted(initial_state.keys(), key=str)}

    # Pick a deterministic validator action + baseline candidate for state seeding.
    action_ids_sorted = sorted([str(a.id) for a in list(ir.actions)])
    if not action_ids_sorted:
        raise ValueError("kernel has no actions; cannot build state pool")
    validator_action_id = action_ids_sorted[0]
    validator_candidate = _best_baseline_candidate(list(candidates_by_action.get(validator_action_id, [])))

    if bool(seed_state_boundaries):
        pool, seed_summary = _seed_state_pool_via_boundary_mutations(
            ir=ir,
            ctx=ctx,
            initial=s0,
            state_types=state_types,
            validator_action_id=str(validator_action_id),
            validator_candidate=validator_candidate,
            max_states=int(max_states),
            seed_steps=int(state_seed_steps),
            seed_width=int(state_seed_width),
            seed=int(seed),
        )
        pool_scores = [_state_boundary_hits(st, state_types) for st in pool]
        seen = {_state_sig(st) for st in pool}
    else:
        pool = [s0]
        pool_scores = [_state_boundary_hits(s0, state_types)]
        seen = {_state_sig(s0)}
        seed_summary = {"enabled": False}

    # Walk over the state graph; current state is part of the Markov chain.
    cur = dict(s0)

    action_ids = list(action_ids_sorted)
    action_pulls: dict[str, int] = {aid: 0 for aid in action_ids}
    action_accepts: dict[str, int] = {aid: 0 for aid in action_ids}

    for _t in range(int(walk_steps)):
        if rng.random() < float(reset_prob):
            cur = dict(pool[int(rng.randrange(len(pool)))])

        # Prefer under-explored actions to keep the pool diverse.
        min_pull = min(action_pulls.values()) if action_pulls else 0
        low_actions = [aid for aid, n in action_pulls.items() if int(n) == int(min_pull)]
        if low_actions:
            aid = low_actions[int(rng.randrange(len(low_actions)))]
        else:
            aid = action_ids[int(rng.randrange(len(action_ids)))]
        action_pulls[aid] = int(action_pulls.get(aid, 0)) + 1

        cands = list(candidates_by_action.get(aid, []))
        if not cands:
            continue
        baseline = _best_baseline_candidate(cands)
        cands.sort(key=lambda c: (float(c.boundary_score), c.signature()), reverse=True)
        cands = cands[: max(1, int(top_k_candidates))]
        if baseline not in cands:
            cands.append(baseline)

        if rng.random() < float(baseline_prob):
            cand = baseline
        else:
            cand = cands[int(rng.randrange(len(cands)))]

        rec = _evaluate_candidate(ir=ir, ctx=ctx, state=cur, candidate=cand, state_types=state_types)
        if rec.next_state is None:
            continue

        action_accepts[aid] = int(action_accepts.get(aid, 0)) + 1
        cur = dict(rec.next_state)

        sig = _state_sig(cur)
        if sig in seen:
            continue
        seen.add(sig)

        score = _state_boundary_hits(cur, state_types)
        if len(pool) < int(max_states):
            pool.append(dict(cur))
            pool_scores.append(int(score))
        else:
            _state_pool_replace(pool=pool, pool_scores=pool_scores, new_state=cur, new_score=score, seed_rng=rng)

    summary = {
        "max_states": int(max_states),
        "seed_state_boundaries": dict(seed_summary),
        "walk_steps": int(walk_steps),
        "reset_prob": float(reset_prob),
        "baseline_prob": float(baseline_prob),
        "top_k_candidates": int(top_k_candidates),
        "state_pool_size": int(len(pool)),
        "unique_states_seen": int(len(seen)),
        "action_pulls": {k: int(action_pulls[k]) for k in sorted(action_pulls.keys())},
        "action_accepts": {k: int(action_accepts[k]) for k in sorted(action_accepts.keys())},
    }
    return pool, summary


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


def _action_param_type_map(*, action: Any, named_types: Mapping[str, Any]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for p in list(getattr(action, "params", None) or ()):
        t = p.type.resolved(named_types) if p.type.kind == "ref" else p.type
        out[str(p.id)] = t
    return out


def _candidate_from_params(
    *,
    action_id: str,
    params: Mapping[str, object],
    param_types: Mapping[str, Any],
    extra_tags: tuple[str, ...] = tuple(),
    boundary_score_boost: float = 0.0,
) -> Candidate:
    params_obj: dict[str, int | bool | str] = {}
    for k in sorted(params.keys(), key=str):
        v = params[k]
        if isinstance(v, bool):
            params_obj[str(k)] = bool(v)
        elif isinstance(v, int) and not isinstance(v, bool):
            params_obj[str(k)] = int(v)
        elif isinstance(v, str):
            params_obj[str(k)] = str(v)
        else:
            raise ValueError(f"unsupported param value type for {k!r}: {type(v).__name__}")

    scores: list[float] = []
    tags: list[str] = []
    for pid, val in params_obj.items():
        t = param_types.get(pid)
        if t is None:
            # Fail-closed; action/param types should be available.
            raise ValueError(f"missing param type for {pid!r}")
        sc, tg = _boundary_feature_for_param(param_id=pid, value=val, t=t)
        scores.append(float(sc))
        tags.append(str(tg))
    bscore = (sum(scores) / float(len(scores))) if scores else 0.0
    bscore = max(0.0, min(1.0, float(bscore) + float(boundary_score_boost)))
    all_tags = tuple(sorted(set(tuple(tags) + tuple(extra_tags))))
    return Candidate(
        action_id=str(action_id),
        params=params_obj,
        boundary_score=float(bscore),
        boundary_tags=all_tags,
        is_baseline=False,
    )


def _evalrecord_with_reward_and_tags(
    rec: EvalRecord, *, reward_add: float, extra_tags: tuple[str, ...]
) -> EvalRecord:
    tags = tuple(sorted(set(tuple(rec.boundary_tags) + tuple(extra_tags))))
    return EvalRecord(
        reward=float(rec.reward) + float(reward_add),
        pre_state=dict(rec.pre_state),
        action=str(rec.action),
        params=dict(rec.params),
        expected=dict(rec.expected),
        boundary_score=float(rec.boundary_score),
        boundary_tags=tags,
        outcome_key=str(rec.outcome_key),
        next_state=(dict(rec.next_state) if rec.next_state is not None else None),
    )


def _refine_pair_bisection(
    *,
    ir: Any,
    ctx: Any,
    pre_state: Mapping[str, object],
    action_id: str,
    param_types: Mapping[str, Any],
    state_types: Mapping[str, Any],
    a_params: Mapping[str, object],
    a_outcome: str,
    b_params: Mapping[str, object],
    b_outcome: str,
    max_steps: int,
    boundary_tag: str,
) -> list[EvalRecord]:
    """
    Refine a discovered outcome boundary via deterministic integer bisection.

    We keep one endpoint fixed to outcome `a_outcome` and shrink the segment to
    the nearest boundary along the line between the two parameter vectors.
    """
    if int(max_steps) <= 0:
        return []

    # Only bisect when int params differ; keep non-int params from a.
    int_keys: list[str] = []
    for k, t in param_types.items():
        if str(getattr(t, "kind", "")) != "int":
            continue
        va = a_params.get(k)
        vb = b_params.get(k)
        if isinstance(va, int) and not isinstance(va, bool) and isinstance(vb, int) and not isinstance(vb, bool):
            if int(va) != int(vb):
                int_keys.append(str(k))
    int_keys.sort()
    if not int_keys:
        return []

    pa = {str(k): a_params[k] for k in sorted(a_params.keys(), key=str)}
    pb = {str(k): b_params[k] for k in sorted(b_params.keys(), key=str)}

    refined: list[EvalRecord] = []
    for _i in range(int(max_steps)):
        d = _param_l1_distance(pa, pb)
        if d <= 1.0:
            break

        mid = dict(pa)
        progressed = False
        for k in int_keys:
            ta = param_types[k]
            lo = int(getattr(ta, "min", 0))
            hi = int(getattr(ta, "max", 0))
            a = int(pa[k])
            b = int(pb[k])
            if a == b:
                continue
            progressed = True
            m = (a + b) // 2
            # Allow the classic BVA "just outside" points, but don't drift.
            m = max(int(lo) - 1, min(int(hi) + 1, int(m)))
            mid[k] = int(m)
        if not progressed:
            break
        if _json_dumps(mid) == _json_dumps(pa) or _json_dumps(mid) == _json_dumps(pb):
            break

        cand = _candidate_from_params(
            action_id=str(action_id),
            params=mid,
            param_types=param_types,
            extra_tags=(str(boundary_tag),),
            # Boost so refined cases are not starved by coverage selection.
            boundary_score_boost=0.35,
        )
        rec = _evaluate_candidate(ir=ir, ctx=ctx, state=pre_state, candidate=cand, state_types=state_types)

        # The closer we get to the boundary, the higher the bonus.
        bonus = 0.85 / (1.0 + float(d))
        rec2 = _evalrecord_with_reward_and_tags(rec, reward_add=float(bonus), extra_tags=(str(boundary_tag),))
        refined.append(rec2)

        if str(rec.outcome_key) == str(a_outcome):
            pa = dict(mid)
        else:
            pb = dict(mid)

    return refined


def _ucb_generate_for_action(
    *,
    ir: Any,
    ctx: Any,
    action: Any,
    candidates: list[Candidate],
    state_pool_seed: list[dict[str, object]],
    state_types: Mapping[str, Any],
    cases_per_action: int,
    iterations_per_action: int,
    max_candidates_per_action: int,
    max_states: int,
    alpha: float,
    seed: int,
    refine_pairs_per_action: int,
    refine_max_steps: int,
) -> tuple[list[EvalRecord], dict[str, object]]:
    if not candidates:
        return [], {"candidate_count": 0, "state_pool_size": 1}
    candidates = list(candidates)
    if len(candidates) > int(max_candidates_per_action):
        candidates = candidates[: int(max_candidates_per_action)]

    pulls = [0 for _ in candidates]
    means = [0.0 for _ in candidates]
    total = 0
    gathered: list[EvalRecord] = []
    novelty_seen: set[tuple[str, str, str]] = set()
    seen_outcomes_by_state: dict[str, list[tuple[dict[str, object], str]]] = {}
    pre_state_by_sig: dict[str, dict[str, object]] = {}
    rng = random.Random(int(seed))

    if not state_pool_seed:
        raise ValueError("state_pool_seed must be non-empty")
    seed_pool = [{str(k): st[k] for k in sorted(st.keys(), key=str)} for st in state_pool_seed]
    # Deduplicate while preserving deterministic order.
    state_pool: list[dict[str, object]] = []
    state_seen: set[str] = set()
    for st in seed_pool:
        sig = _state_sig(st)
        if sig in state_seen:
            continue
        state_seen.add(sig)
        state_pool.append(st)
    if not state_pool:
        raise ValueError("state_pool_seed produced empty pool")

    # Pre-compute viable pre-states: those where the baseline candidate is accepted.
    viable_states: list[dict[str, object]] = []
    baseline = _best_baseline_candidate(candidates)
    for st in state_pool:
        rec0 = _evaluate_candidate(ir=ir, ctx=ctx, state=st, candidate=baseline, state_types=state_types)
        if rec0.next_state is not None:
            viable_states.append(st)

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
        if viable_states and rng.random() < 0.75:
            st = viable_states[int(rng.randrange(len(viable_states)))]
        else:
            st = state_pool[int(rng.randrange(len(state_pool)))]
        rec = _evaluate_candidate(ir=ir, ctx=ctx, state=st, candidate=cand, state_types=state_types)
        pre_state_by_sig.setdefault(_state_sig(rec.pre_state), dict(rec.pre_state))

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

    named_types = ir.named_types()
    param_types = _action_param_type_map(action=action, named_types=named_types)

    if int(refine_pairs_per_action) > 0 and int(refine_max_steps) > 0:
        # Build a small set of (close) outcome-crossing pairs per pre-state, then bisect.
        pairs: list[tuple[float, str, str, str, dict[str, object], str, dict[str, object], str]] = []
        for pre_sig in sorted(seen_outcomes_by_state.keys(), key=str):
            entries = list(seen_outcomes_by_state.get(pre_sig, []))
            # Unique by (params_sig, outcome_key) to keep O(n^2) bounded.
            uniq: dict[tuple[str, str], dict[str, object]] = {}
            for params_obj, outcome_key in entries:
                psig = _json_dumps({str(k): params_obj[k] for k in sorted(params_obj.keys(), key=str)})
                uniq.setdefault((psig, str(outcome_key)), dict(params_obj))
            uniq_entries: list[tuple[str, dict[str, object], str]] = []
            for (psig, outcome_key), params_obj in sorted(uniq.items(), key=lambda x: (x[0][0], x[0][1])):
                uniq_entries.append((psig, params_obj, str(outcome_key)))
            for i in range(len(uniq_entries)):
                psig_a, pa, oa = uniq_entries[i]
                for j in range(i + 1, len(uniq_entries)):
                    psig_b, pb, ob = uniq_entries[j]
                    if oa == ob:
                        continue
                    dist = _param_l1_distance(pa, pb)
                    pairs.append((float(dist), str(pre_sig), str(psig_a), str(oa), pa, str(psig_b), pb, str(ob)))
        pairs.sort(key=lambda t: (float(t[0]), str(t[1]), str(t[2]), str(t[3]), str(t[5]), str(t[7])))
        for dist, pre_sig, psig_a, oa, pa, psig_b, pb, ob in pairs[: int(refine_pairs_per_action)]:
            pre_state = pre_state_by_sig.get(str(pre_sig))
            if pre_state is None:
                continue
            boundary_tag = f"refine:bisect:{oa}->{ob}"
            refined = _refine_pair_bisection(
                ir=ir,
                ctx=ctx,
                pre_state=pre_state,
                action_id=str(action.id),
                param_types=param_types,
                state_types=state_types,
                a_params=pa,
                a_outcome=str(oa),
                b_params=pb,
                b_outcome=str(ob),
                max_steps=int(refine_max_steps),
                boundary_tag=str(boundary_tag),
            )
            for rec in refined:
                nov_key = (
                    _json_dumps({"a": rec.action, "p": rec.params}),
                    str(rec.outcome_key),
                    _state_sig(rec.pre_state),
                )
                if nov_key in novelty_seen:
                    continue
                novelty_seen.add(nov_key)
                gathered.append(rec)

    selected = _select_cases_with_coverage(gathered, want=int(cases_per_action))
    summary = {
        "candidate_count": int(len(candidates)),
        "iterations": int(iters),
        "state_pool_size": int(len(state_pool)),
        "raw_record_count": int(len(gathered)),
        "refine_pairs_per_action": int(refine_pairs_per_action),
        "refine_max_steps": int(refine_max_steps),
    }
    return selected, summary


def generate_ml_bva_suite(
    *,
    model_path: Path,
    cases_per_action: int,
    iterations_per_action: int,
    max_candidates_per_action: int,
    max_states: int,
    global_walk_steps: int,
    global_reset_prob: float,
    global_baseline_prob: float,
    global_top_k_candidates: int,
    seed_state_boundaries: bool = False,
    state_seed_steps: int = 500,
    state_seed_width: int = 2,
    refine_pairs_per_action: int,
    refine_max_steps: int,
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
    if int(global_walk_steps) <= 0:
        raise ValueError("global_walk_steps must be > 0")
    if float(global_reset_prob) < 0.0 or float(global_reset_prob) > 1.0:
        raise ValueError("global_reset_prob must be in [0,1]")
    if float(global_baseline_prob) < 0.0 or float(global_baseline_prob) > 1.0:
        raise ValueError("global_baseline_prob must be in [0,1]")
    if int(global_top_k_candidates) <= 0:
        raise ValueError("global_top_k_candidates must be > 0")
    if int(state_seed_steps) < 0:
        raise ValueError("state_seed_steps must be >= 0")
    if int(state_seed_width) <= 0:
        raise ValueError("state_seed_width must be > 0")
    if int(refine_pairs_per_action) < 0:
        raise ValueError("refine_pairs_per_action must be >= 0")
    if int(refine_max_steps) < 0:
        raise ValueError("refine_max_steps must be >= 0")
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

    model_fs_path = model_path.expanduser()
    obj = yaml.safe_load(model_fs_path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"model YAML is not a mapping: {model_fs_path}")

    ir = CandidateIR.from_json_dict(obj).canonicalized()
    ctx = prepare_step_context(ir)
    if isinstance(ctx, StepError):
        raise RuntimeError(f"invalid model step context: {ctx.code}: {ctx.message}")

    s0 = dict(initial_state(ir))
    state_types = _state_type_map(ir)

    # Precompute boundary candidates per action and build a global state pool
    # with cross-action reachability (Markov-chain walk).
    candidates_by_action: dict[str, list[Candidate]] = {}
    actions_sorted = sorted(list(ir.actions), key=lambda a: str(a.id))
    named_types = ir.named_types()
    for action in actions_sorted:
        action_id = str(action.id)
        candidates_by_action[action_id] = _build_candidates_for_action(
            action,
            named_types=named_types,
            max_candidates=int(max_candidates_per_action),
        )
    global_states, global_summary = _build_global_state_pool_mcmc(
        ir=ir,
        ctx=ctx,
        initial_state=s0,
        state_types=state_types,
        candidates_by_action=candidates_by_action,
        max_states=int(max_states),
        seed_state_boundaries=bool(seed_state_boundaries),
        state_seed_steps=int(state_seed_steps),
        state_seed_width=int(state_seed_width),
        walk_steps=int(global_walk_steps),
        reset_prob=float(global_reset_prob),
        baseline_prob=float(global_baseline_prob),
        top_k_candidates=int(global_top_k_candidates),
        seed=int(seed),
    )

    all_cases: list[dict[str, object]] = []
    per_action: dict[str, object] = {}
    for action in actions_sorted:
        action_id = str(action.id)
        selected, summary = _ucb_generate_for_action(
            ir=ir,
            ctx=ctx,
            action=action,
            candidates=candidates_by_action[action_id],
            state_pool_seed=global_states,
            state_types=state_types,
            cases_per_action=int(cases_per_action),
            iterations_per_action=int(iterations_per_action),
            max_candidates_per_action=int(max_candidates_per_action),
            max_states=int(max_states),
            alpha=float(alpha),
            seed=int(seed) + int(sum(ord(ch) for ch in action_id)),
            refine_pairs_per_action=int(refine_pairs_per_action),
            refine_max_steps=int(refine_max_steps),
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
        "model_path": _portable_path(model_path),
        "model_sha256": hashlib.sha256(model_fs_path.read_bytes()).hexdigest(),
        "seed": int(seed),
        "algorithm": {
            "name": "ucb1_boundary_sampler",
            "alpha": float(alpha),
            "cases_per_action": int(cases_per_action),
            "iterations_per_action": int(iterations_per_action),
            "max_candidates_per_action": int(max_candidates_per_action),
            "max_states": int(max_states),
            "global_state_pool": dict(global_summary),
            "refine_pairs_per_action": int(refine_pairs_per_action),
            "refine_max_steps": int(refine_max_steps),
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
    ap.add_argument("--global-walk-steps", type=int, default=800)
    ap.add_argument("--global-reset-prob", type=float, default=0.15)
    ap.add_argument("--global-baseline-prob", type=float, default=0.25)
    ap.add_argument("--global-top-k-candidates", type=int, default=40)
    ap.add_argument(
        "--seed-state-boundaries",
        action="store_true",
        help="Seed the global pre-state pool by mutating state vars to boundary values (useful for calculator kernels).",
    )
    ap.add_argument("--state-seed-steps", type=int, default=500)
    ap.add_argument("--state-seed-width", type=int, default=2, help="How many state vars to mutate per seed proposal.")
    ap.add_argument("--refine-pairs-per-action", type=int, default=12)
    ap.add_argument("--refine-max-steps", type=int, default=6)
    ap.add_argument("--alpha", type=float, default=1.25, help="UCB exploration coefficient.")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    suite = generate_ml_bva_suite(
        model_path=args.model,
        cases_per_action=int(args.cases_per_action),
        iterations_per_action=int(args.iterations_per_action),
        max_candidates_per_action=int(args.max_candidates_per_action),
        max_states=int(args.max_states),
        global_walk_steps=int(args.global_walk_steps),
        global_reset_prob=float(args.global_reset_prob),
        global_baseline_prob=float(args.global_baseline_prob),
        global_top_k_candidates=int(args.global_top_k_candidates),
        seed_state_boundaries=bool(args.seed_state_boundaries),
        state_seed_steps=int(args.state_seed_steps),
        state_seed_width=int(args.state_seed_width),
        refine_pairs_per_action=int(args.refine_pairs_per_action),
        refine_max_steps=int(args.refine_max_steps),
        alpha=float(args.alpha),
        seed=int(args.seed),
    )
    _write_json(args.out_json.expanduser().resolve(), suite, pretty=bool(args.pretty))
    print(json.dumps(suite["summary"], sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
