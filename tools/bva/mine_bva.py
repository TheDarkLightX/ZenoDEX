from __future__ import annotations

import argparse
import importlib.util
import json
import os
import random
import sys
import time
from typing import Any, Hashable

# Allow `python3 tools/bva/mine_bva.py ...` from repo root without needing `-m`.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from tools.bva.spec import IntDomain, Scenario  # noqa: E402
from tools.bva.tracing import trace_path_signature  # noqa: E402


def _load_scenario(path: str) -> Scenario:
    abspath = os.path.abspath(path)
    spec = importlib.util.spec_from_file_location("bva_scenario", abspath)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"failed to load scenario from: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["bva_scenario"] = module
    spec.loader.exec_module(module)

    if hasattr(module, "get_scenario"):
        scenario = module.get_scenario()
    elif hasattr(module, "SCENARIO"):
        scenario = getattr(module, "SCENARIO")
    else:
        raise RuntimeError("scenario module must define SCENARIO or get_scenario()")

    if not isinstance(scenario, Scenario):
        raise TypeError(f"scenario is not tools.bva.spec.Scenario: {type(scenario)}")
    return scenario


def _uniq_keep_order(xs: list[Any]) -> list[Any]:
    out: list[Any] = []
    seen: set[Any] = set()
    for x in xs:
        key = x
        if key in seen:
            continue
        seen.add(key)
        out.append(x)
    return out


def _in_range(dom: IntDomain, v: int) -> bool:
    return int(dom.min_value) <= int(v) <= int(dom.max_value)


def _static_bva_groups_for_int_domain(name: str, dom: IntDomain) -> list[dict[str, Any]]:
    """Return static BVA groups for a single IntDomain."""
    mn = int(dom.min_value)
    mx = int(dom.max_value)

    groups: list[dict[str, Any]] = []

    # Min boundary: (mn-1), mn, (mn+1)
    min_cases: list[dict[str, Any]] = []
    if dom.include_oob:
        min_cases.append({"value": mn - 1, "reason": f"{name}: just-below min (out-of-domain)"})
    min_cases.append({"value": mn, "reason": f"{name}: exactly at min boundary"})
    if mn + 1 <= mx:
        min_cases.append({"value": mn + 1, "reason": f"{name}: just-above min boundary"})
    groups.append({"group": "min boundary", "cases": min_cases})

    # Max boundary: (mx-1), mx, (mx+1)
    max_cases: list[dict[str, Any]] = []
    if mx - 1 >= mn:
        max_cases.append({"value": mx - 1, "reason": f"{name}: just-below max boundary"})
    max_cases.append({"value": mx, "reason": f"{name}: exactly at max boundary"})
    if dom.include_oob:
        max_cases.append({"value": mx + 1, "reason": f"{name}: just-above max (out-of-domain)"})
    groups.append({"group": "max boundary", "cases": max_cases})

    specials: list[Any] = []
    if dom.include_bool:
        specials.extend([False, True])
    if dom.include_none:
        specials.append(None)

    specials.extend([-1, 0, 1])
    specials.extend([mn, mx])
    specials.extend(list(dom.specials))

    # Keep only in-range (and non-int types) for the static "special" group; OOB is already covered above.
    special_cases: list[dict[str, Any]] = []
    for v in _uniq_keep_order(specials):
        if v is None or isinstance(v, bool):
            special_cases.append({"value": v, "reason": f"{name}: special type boundary"})
            continue
        if not isinstance(v, int):
            continue
        if _in_range(dom, int(v)):
            special_cases.append({"value": int(v), "reason": f"{name}: special value"})
    groups.append({"group": "special values", "cases": special_cases})

    mid = (mn + mx) // 2
    mid_cases = [{"value": mid, "reason": f"{name}: mid-point sanity value"}]
    groups.append({"group": "mid-point", "cases": mid_cases})
    return groups


def _eval_label(s: Scenario, *, kwargs: dict[str, Any]) -> Hashable:
    if s.constraint is not None and not bool(s.constraint(dict(kwargs))):
        return "constraint_violation"

    try:
        if s.trace_paths:
            out, sig = trace_path_signature(s.fn, kwargs=dict(kwargs), trace_paths=s.trace_paths)
            if s.label_fn is None:
                return ("pathsig", sig)
            return ("label+pathsig", s.label_fn(out), sig)
        out = s.fn(**kwargs)
    except Exception as e:  # noqa: BLE001 - boundary discovery is explicitly exception-aware
        return ("exc", type(e).__name__)

    if s.label_fn is not None:
        try:
            return ("label", s.label_fn(out))
        except Exception as e:  # noqa: BLE001
            return ("label_exc", type(e).__name__)
    return ("repr", repr(out))


def _representatives(dom: IntDomain) -> list[int]:
    mn = int(dom.min_value)
    mx = int(dom.max_value)
    reps: list[int] = [mn, mx]
    if mn + 1 <= mx:
        reps.append(mn + 1)
    if mx - 1 >= mn:
        reps.append(mx - 1)
    reps.append((mn + mx) // 2)
    reps.extend(int(v) for v in dom.specials if isinstance(v, int))
    reps = [int(v) for v in _uniq_keep_order(reps) if _in_range(dom, int(v))]
    reps.sort()
    return reps


def _iter_contexts(s: Scenario, *, focus_param: str, rng: random.Random | None = None) -> list[dict[str, Any]]:
    others = [p for p in s.domains.keys() if p != focus_param]
    if not others:
        return [{}]

    rep_lists: list[list[int]] = []
    for p in others:
        reps = _representatives(s.domains[p])
        if not reps:
            reps = [int(s.domains[p].min_value)]
        # Keep at most 3 per param: min/mid/max.
        if len(reps) > 3:
            reps = [reps[0], reps[len(reps) // 2], reps[-1]]
        rep_lists.append(reps)

    # Deterministic cartesian product truncation.
    contexts: list[dict[str, Any]] = []

    def _recurse(i: int, cur: dict[str, Any]) -> None:
        if len(contexts) >= int(s.max_contexts):
            return
        if i >= len(others):
            contexts.append(dict(cur))
            return
        p = others[i]
        for v in rep_lists[i]:
            cur[p] = int(v)
            _recurse(i + 1, cur)
            if len(contexts) >= int(s.max_contexts):
                return
        cur.pop(p, None)

    _recurse(0, {})
    if not contexts:
        contexts = [{}]

    # Optional: enrich with random contexts to avoid missing cross-field boundary regimes.
    if int(s.random_contexts) > 0 and rng is not None and others:
        existing = {tuple(sorted(c.items())) for c in contexts}
        # Precompute candidate lists for each other param.
        candidates: dict[str, list[int]] = {}
        for p in others:
            dom = s.domains[p]
            cands = _sample_values(dom, rng=rng, budget=int(s.random_context_budget))
            if not cands:
                cands = [int(dom.min_value)]
            candidates[p] = list(cands)

        tries = 0
        while len(contexts) < int(s.max_contexts) + int(s.random_contexts) and tries < int(s.random_contexts) * 10:
            tries += 1
            ctx: dict[str, Any] = {}
            for p in others:
                c = candidates[p]
                ctx[p] = int(c[rng.randrange(0, len(c))])
            key = tuple(sorted(ctx.items()))
            if key in existing:
                continue
            existing.add(key)
            contexts.append(ctx)

    return contexts


def _sample_values(dom: IntDomain, *, rng: random.Random, budget: int) -> list[int]:
    mn = int(dom.min_value)
    mx = int(dom.max_value)
    values: list[int] = []
    values.extend([mn, mx, (mn + mx) // 2])
    if mn + 1 <= mx:
        values.append(mn + 1)
    if mx - 1 >= mn:
        values.append(mx - 1)
    values.extend(int(v) for v in dom.specials if isinstance(v, int))

    # Add a few "classic" specials if they fall in range.
    for v in [-1, 0, 1, 2, 10, 100, 1000, 10_000]:
        if _in_range(dom, int(v)):
            values.append(int(v))

    # Random fill.
    width = mx - mn
    if width > 0:
        for _ in range(max(0, int(budget) - len(values))):
            values.append(mn + int(rng.randint(0, width)))

    values = [int(v) for v in _uniq_keep_order(values) if _in_range(dom, int(v))]
    values.sort()
    return values


def _scan_interval_for_boundaries(
    s: Scenario,
    *,
    param: str,
    context: dict[str, Any],
    lo: int,
    hi: int,
    eval_cache: dict[int, Hashable],
) -> list[tuple[int, int, Hashable, Hashable]]:
    """Scan [lo, hi] exhaustively (integers step=1) and return adjacent flip boundaries."""
    out: list[tuple[int, int, Hashable, Hashable]] = []
    prev_v = None
    prev_l = None
    for v in range(int(lo), int(hi) + 1):
        if v in eval_cache:
            lbl = eval_cache[v]
        else:
            kwargs = dict(s.fixed_kwargs)
            kwargs.update(context)
            kwargs[param] = int(v)
            lbl = _eval_label(s, kwargs=kwargs)
            eval_cache[int(v)] = lbl
        if prev_v is not None and prev_l is not None and lbl != prev_l:
            out.append((int(prev_v), int(v), prev_l, lbl))
        prev_v = int(v)
        prev_l = lbl
    return out


def _refine_boundaries_in_interval(
    s: Scenario,
    *,
    param: str,
    context: dict[str, Any],
    lo: int,
    hi: int,
    label_lo: Hashable,
    label_hi: Hashable,
    eval_cache: dict[int, Hashable],
    max_steps: int = 4096,
) -> list[tuple[int, int, Hashable, Hashable]]:
    """Refine an interval known to contain at least one label flip.

    This is heuristic: it tries to end in small scan windows where we can
    exhaustively enumerate flips, but it will stop if budgets are exhausted.
    """
    if label_lo == label_hi:
        return []

    threshold = int(s.refine_scan_threshold)
    boundaries: list[tuple[int, int, Hashable, Hashable]] = []
    steps = 0
    stack: list[tuple[int, int, Hashable, Hashable]] = [(int(lo), int(hi), label_lo, label_hi)]
    while stack and steps < int(max_steps):
        a, b, la, lb = stack.pop()
        if la == lb:
            continue
        if b - a <= threshold:
            boundaries.extend(
                _scan_interval_for_boundaries(
                    s,
                    param=param,
                    context=context,
                    lo=a,
                    hi=b,
                    eval_cache=eval_cache,
                )
            )
            continue

        mid = (int(a) + int(b)) // 2
        if mid in eval_cache:
            lm = eval_cache[mid]
        else:
            kwargs = dict(s.fixed_kwargs)
            kwargs.update(context)
            kwargs[param] = int(mid)
            lm = _eval_label(s, kwargs=kwargs)
            eval_cache[int(mid)] = lm

        if lm == la:
            stack.append((mid, b, lm, lb))
        elif lm == lb:
            stack.append((a, mid, la, lm))
        else:
            # New label discovered: split both halves.
            stack.append((a, mid, la, lm))
            stack.append((mid, b, lm, lb))
        steps += 1

    # Deduplicate (overlapping scans can produce repeats).
    uniq: dict[tuple[int, int, Hashable, Hashable], None] = {}
    for t in boundaries:
        uniq[t] = None
    return list(uniq.keys())


def mine_dynamic_boundaries(s: Scenario) -> dict[str, Any]:
    rng = random.Random(int(s.seed))
    all_groups: list[dict[str, Any]] = []
    labels_seen: dict[str, list[str]] = {}
    global_groups: list[dict[str, Any]] = []

    for param, dom in s.domains.items():
        contexts = _iter_contexts(s, focus_param=param, rng=rng)

        for ctx_i, ctx in enumerate(contexts):
            mn = int(dom.min_value)
            mx = int(dom.max_value)
            width = mx - mn
            eval_cache: dict[int, Hashable] = {}

            if width <= int(s.exhaustive_threshold):
                # Full scan to find all adjacent flips.
                boundaries = _scan_interval_for_boundaries(
                    s,
                    param=param,
                    context=ctx,
                    lo=mn,
                    hi=mx,
                    eval_cache=eval_cache,
                )
            else:
                samples = _sample_values(dom, rng=rng, budget=int(s.samples_per_context))
                labeled: list[tuple[int, Hashable]] = []
                for v in samples:
                    kwargs = dict(s.fixed_kwargs)
                    kwargs.update(ctx)
                    kwargs[param] = int(v)
                    lbl = _eval_label(s, kwargs=kwargs)
                    eval_cache[int(v)] = lbl
                    labeled.append((int(v), lbl))
                labeled.sort(key=lambda t: t[0])

                # Refine only where adjacent sampled labels differ.
                boundaries = []
                for (v0, l0), (v1, l1) in zip(labeled, labeled[1:]):
                    if l0 == l1:
                        continue
                    boundaries.extend(
                        _refine_boundaries_in_interval(
                            s,
                            param=param,
                            context=ctx,
                            lo=v0,
                            hi=v1,
                            label_lo=l0,
                            label_hi=l1,
                            eval_cache=eval_cache,
                        )
                    )

            # Record labels seen (stringified for JSON stability).
            key = f"{param}:ctx{ctx_i}"
            labels_seen[key] = sorted({_stable_label_str(x) for x in eval_cache.values()})

            for lower, upper, l_lo, l_hi in sorted(boundaries, key=lambda t: (t[0], t[1])):
                boundary_value = int(upper)
                cases: list[dict[str, Any]] = []
                for tag, v in [
                    ("just_below", boundary_value - 1),
                    ("at", boundary_value),
                    ("just_above", boundary_value + 1),
                ]:
                    if not _in_range(dom, int(v)) and not bool(dom.include_oob):
                        continue
                    kw = dict(s.fixed_kwargs)
                    kw.update(ctx)
                    kw[param] = int(v)
                    cases.append(
                        {
                            "id": f"{param}__ctx{ctx_i}__b{boundary_value}__{tag}",
                            "params": kw,
                            "reason": (
                                f"Label flip near {param}={boundary_value} (ctx={ctx_i}): "
                                f"{_stable_label_str(l_lo)} -> {_stable_label_str(l_hi)}"
                            ),
                        }
                    )
                all_groups.append(
                    {
                        "param": param,
                        "context_id": int(ctx_i),
                        "context": ctx,
                        "lower": int(lower),
                        "upper": int(upper),
                        "boundary_value": int(boundary_value),
                        "label_lower": _stable_label_str(l_lo),
                        "label_upper": _stable_label_str(l_hi),
                        "cases": cases,
                    }
                )

    # Optional: global (multi-parameter) boundary mining.
    if int(s.global_samples) > 0:
        global_groups = _mine_global_flip_pairs(s, rng=rng)

    return {
        "schema": "tools.bva.boundary_mining.v1",
        "scenario": s.name,
        "time_unix_s": int(time.time()),
        "static_bva": {
            p: _static_bva_groups_for_int_domain(p, d) for p, d in sorted(s.domains.items())
        },
        "dynamic_boundaries": all_groups,
        "global_boundaries": global_groups,
        "labels_seen": labels_seen,
    }


def _kwargs_key(s: Scenario, kwargs: dict[str, Any]) -> tuple[tuple[str, Any], ...]:
    # Stable key for caching; we key over fixed kwargs plus declared domain params.
    #
    # Note: fixed kwargs may include lists/dicts (e.g., slippage option lists), so we
    # freeze them into hashable tuples.

    def _freeze(v: Any) -> Any:
        if v is None or isinstance(v, (int, bool, str)):
            return v
        if isinstance(v, tuple):
            return tuple(_freeze(x) for x in v)
        if isinstance(v, list):
            return tuple(_freeze(x) for x in v)
        if isinstance(v, dict):
            return tuple(sorted((str(k), _freeze(val)) for k, val in v.items()))
        # Last resort: stable-ish string.
        return repr(v)

    items: list[tuple[str, Any]] = []
    for p in sorted(s.fixed_kwargs.keys()):
        items.append((str(p), _freeze(kwargs.get(p))))
    for p in sorted(s.domains.keys()):
        items.append((str(p), _freeze(kwargs.get(p))))
    return tuple(items)


def _eval_label_cached(
    s: Scenario,
    *,
    kwargs: dict[str, Any],
    eval_cache: dict[tuple[tuple[str, Any], ...], Hashable],
) -> Hashable:
    k = _kwargs_key(s, kwargs)
    if k in eval_cache:
        return eval_cache[k]
    lbl = _eval_label(s, kwargs=dict(kwargs))
    eval_cache[k] = lbl
    return lbl


def _mutate_point_local(
    s: Scenario,
    *,
    base: dict[str, Any],
    rng: random.Random,
    mutate_two_params_prob: float = 0.20,
    large_step_prob: float = 0.30,
    large_step_max_pow: int = 8,
) -> dict[str, Any]:
    """Local proposal step for MCMC over integer domains (best-effort).

    We keep proposals in-range; constraints are handled by the labeler
    (constraint violations are just another label).
    """
    out = dict(base)
    params = list(s.domains.keys())
    if not params:
        return out

    def _mutate_one(p: str) -> None:
        dom = s.domains[p]
        mn = int(dom.min_value)
        mx = int(dom.max_value)
        cur = out.get(p, mn)
        if not isinstance(cur, int) or isinstance(cur, bool):
            cur = mn

        step = int(dom.step)
        if rng.random() < float(large_step_prob):
            k = int(rng.randrange(0, max(1, int(large_step_max_pow) + 1)))
            mag = step * (1 << k)
        else:
            mag = step
        mag = max(step, int(mag))

        sign = -1 if rng.random() < 0.5 else 1
        cand = int(cur) + int(sign) * int(mag)
        if cand < mn:
            cand = mn
        if cand > mx:
            cand = mx
        out[p] = int(cand)

    p1 = str(params[rng.randrange(0, len(params))])
    _mutate_one(p1)

    if len(params) > 1 and rng.random() < float(mutate_two_params_prob):
        p2 = str(params[rng.randrange(0, len(params))])
        if p2 != p1:
            _mutate_one(p2)

    return out


def _pair_distance_l1(s: Scenario, a: dict[str, Any], b: dict[str, Any]) -> int:
    # Keep it simple and integer: sum abs diffs over declared domain params.
    d = 0
    for p in s.domains.keys():
        va = a.get(p, 0)
        vb = b.get(p, 0)
        if not isinstance(va, int) or isinstance(va, bool):
            va = 0
        if not isinstance(vb, int) or isinstance(vb, bool):
            vb = 0
        d += abs(int(va) - int(vb))
    return int(d)


def _canonical_pair(
    s: Scenario,
    *,
    a: dict[str, Any],
    la: Hashable,
    b: dict[str, Any],
    lb: Hashable,
) -> tuple[dict[str, Any], Hashable, dict[str, Any], Hashable]:
    # Deterministic ordering to dedupe pairs regardless of discovery direction.
    ka = (_stable_label_str(la), _kwargs_key(s, a))
    kb = (_stable_label_str(lb), _kwargs_key(s, b))
    if ka <= kb:
        return dict(a), la, dict(b), lb
    return dict(b), lb, dict(a), la


def _ddmin_pair_hamming(
    s: Scenario,
    *,
    a: dict[str, Any],
    la: Hashable,
    b: dict[str, Any],
    lb: Hashable,
    eval_cache: dict[tuple[tuple[str, Any], ...], Hashable],
    max_rounds: int = 8,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Try to reduce the number of differing params while preserving label difference."""
    aa = dict(a)
    bb = dict(b)

    # Deterministic param order.
    params = list(sorted(s.domains.keys()))

    for _ in range(int(max_rounds)):
        changed = False
        for p in params:
            if aa.get(p) == bb.get(p):
                continue
            cand = dict(aa)
            cand[p] = bb.get(p)
            lc = _eval_label_cached(s, kwargs=cand, eval_cache=eval_cache)
            if lc == la:
                aa = cand
                changed = True
        for p in params:
            if aa.get(p) == bb.get(p):
                continue
            cand = dict(bb)
            cand[p] = aa.get(p)
            lc = _eval_label_cached(s, kwargs=cand, eval_cache=eval_cache)
            if lc == lb:
                bb = cand
                changed = True
        if not changed:
            break
    return aa, bb


def _axis_boundaries_from_pair_path(
    s: Scenario,
    *,
    a: dict[str, Any],
    la: Hashable,
    b: dict[str, Any],
    lb: Hashable,
    eval_cache: dict[tuple[tuple[str, Any], ...], Hashable],
    pair_idx: int,
    max_boundaries: int = 2,
) -> list[dict[str, Any]]:
    """Extract axis boundaries by walking from a -> b one param at a time.

    Even if a/b differ in multiple params, the discrete label along a single-param
    update path must flip somewhere if la != lb. This turns multi-param interaction
    witnesses into at least one axis-aligned boundary triple under an intermediate
    cross-field context.
    """
    cur = dict(a)
    cur_lbl = la
    out: list[dict[str, Any]] = []

    diffs = [p for p in sorted(s.domains.keys()) if cur.get(p) != b.get(p)]
    for step_i, param in enumerate(diffs):
        nxt = dict(cur)
        nxt[param] = b.get(param)
        nxt_lbl = _eval_label_cached(s, kwargs=nxt, eval_cache=eval_cache)

        if nxt_lbl != cur_lbl:
            dom = s.domains[param]
            v0 = cur.get(param)
            v1 = nxt.get(param)
            if isinstance(v0, int) and not isinstance(v0, bool) and isinstance(v1, int) and not isinstance(v1, bool):
                if int(v0) < int(v1):
                    lo, hi = int(v0), int(v1)
                    l_lo, l_hi = cur_lbl, nxt_lbl
                else:
                    lo, hi = int(v1), int(v0)
                    l_lo, l_hi = nxt_lbl, cur_lbl

                ctx = {p: cur.get(p) for p in s.domains.keys() if p != param}
                eval_cache_1d: dict[int, Hashable] = {}
                bounds = _refine_boundaries_in_interval(
                    s,
                    param=str(param),
                    context=ctx,
                    lo=int(lo),
                    hi=int(hi),
                    label_lo=l_lo,
                    label_hi=l_hi,
                    eval_cache=eval_cache_1d,
                    max_steps=4096,
                )
                if bounds:
                    lower, upper, l0, l1 = sorted(bounds, key=lambda t: (t[1] - t[0], t[1], t[0]))[0]
                    boundary_value = int(upper)
                    cases: list[dict[str, Any]] = []
                    for tag, v in [
                        ("just_below", boundary_value - 1),
                        ("at", boundary_value),
                        ("just_above", boundary_value + 1),
                    ]:
                        if not _in_range(dom, int(v)) and not bool(dom.include_oob):
                            continue
                        kw = dict(s.fixed_kwargs)
                        kw.update(ctx)
                        kw[param] = int(v)
                        cases.append(
                            {
                                "id": f"mcmc_path_{pair_idx}_{step_i}__{param}__b{boundary_value}__{tag}",
                                "params": kw,
                                "reason": (
                                    f"MCMC pair path boundary near {param}={boundary_value}: "
                                    f"{_stable_label_str(l0)} -> {_stable_label_str(l1)}"
                                ),
                            }
                        )
                    out.append(
                        {
                            "param": str(param),
                            "context_id": int(pair_idx),
                            "context": ctx,
                            "lower": int(lower),
                            "upper": int(upper),
                            "boundary_value": int(boundary_value),
                            "label_lower": _stable_label_str(l0),
                            "label_upper": _stable_label_str(l1),
                            "cases": cases,
                            "source_pair": {"distance_l1": _pair_distance_l1(s, a, b), "kind": "path"},
                        }
                    )
                    if len(out) >= int(max_boundaries):
                        return out

        cur = nxt
        cur_lbl = nxt_lbl

    _ = lb  # documentation: end-label used only for the existence argument above
    return out


def _shrink_pair_l1_coordinate_descent(
    s: Scenario,
    *,
    a: dict[str, Any],
    la: Hashable,
    b: dict[str, Any],
    lb: Hashable,
    eval_cache: dict[tuple[tuple[str, Any], ...], Hashable],
    max_rounds: int = 16,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Try to reduce L1 distance between a/b while preserving their labels.

    This is a light-weight "binary shrink" that nudges each differing coordinate
    toward the midpoint when possible (accepting only if the label is preserved).
    """
    aa = dict(a)
    bb = dict(b)
    params = list(sorted(s.domains.keys()))

    for _ in range(int(max_rounds)):
        changed = False
        for p in params:
            va = aa.get(p, None)
            vb = bb.get(p, None)
            if not isinstance(va, int) or isinstance(va, bool):
                continue
            if not isinstance(vb, int) or isinstance(vb, bool):
                continue
            if int(va) == int(vb):
                continue

            lo = min(int(va), int(vb))
            hi = max(int(va), int(vb))
            mid = (int(lo) + int(hi)) // 2

            # Move side A toward B if it keeps label la.
            if int(va) != int(mid):
                cand = dict(aa)
                cand[p] = int(mid)
                lc = _eval_label_cached(s, kwargs=cand, eval_cache=eval_cache)
                if lc == la:
                    aa = cand
                    changed = True
                    continue

            # Otherwise try moving side B toward A if it keeps label lb.
            if int(vb) != int(mid):
                cand = dict(bb)
                cand[p] = int(mid)
                lc = _eval_label_cached(s, kwargs=cand, eval_cache=eval_cache)
                if lc == lb:
                    bb = cand
                    changed = True
                    continue

        if not changed:
            break

    return aa, bb


def mine_mcmc_boundaries(
    s: Scenario,
    *,
    chains: int,
    steps: int,
    max_pairs: int = 12,
    seed: int | None = None,
) -> dict[str, Any]:
    """Mine close-by opposite-label pairs using a pair-density MCMC walk.

    This is inspired by the "pairDensity + MCMC" style from the referenced paper:
    we bias sampling toward pairs with different labels and small L1 distance.
    """
    rng = random.Random(int(seed) if seed is not None else (int(s.seed) + 1337))
    eval_cache: dict[tuple[tuple[str, Any], ...], Hashable] = {}

    # Bootstrap a small labeled pool so we can seed chains with differing labels.
    pool: list[tuple[dict[str, Any], Hashable]] = []
    labels_to_points: dict[str, list[dict[str, Any]]] = {}

    bootstrap = max(32, 2 * int(chains))
    for _ in range(int(bootstrap)):
        kw = _sample_full_kwargs(s, rng=rng)
        lbl = _eval_label_cached(s, kwargs=kw, eval_cache=eval_cache)
        pool.append((dict(kw), lbl))
        labels_to_points.setdefault(_stable_label_str(lbl), []).append(dict(kw))

    if len(labels_to_points) < 2:
        return {
            "schema": "tools.bva.mcmc_boundary_mining.v1",
            "scenario": s.name,
            "seed": int(seed) if seed is not None else (int(s.seed) + 1337),
            "chains": int(chains),
            "steps": int(steps),
            "status": "inconclusive_single_label",
            "labels_seen": sorted(labels_to_points.keys()),
            "label_counts_bootstrap": {k: len(v) for k, v in sorted(labels_to_points.items(), key=lambda kv: kv[0])},
            "pairs": [],
            "axis_boundaries": [],
        }

    label_keys = sorted(labels_to_points.keys())

    # Record best pairs by (distance, stable tiebreak).
    best: dict[tuple[int, str, tuple[tuple[str, Any], ...], str, tuple[tuple[str, Any], ...]], dict[str, Any]] = {}

    def _record_pair(a: dict[str, Any], la: Hashable, b: dict[str, Any], lb: Hashable, *, reason: str) -> None:
        aa, lla, bb, llb = _canonical_pair(s, a=a, la=la, b=b, lb=lb)
        dist = _pair_distance_l1(s, aa, bb)
        k = (
            int(dist),
            _stable_label_str(lla),
            _kwargs_key(s, aa),
            _stable_label_str(llb),
            _kwargs_key(s, bb),
        )
        if k in best:
            return
        best[k] = {
            "distance_l1": int(dist),
            "label_a": _stable_label_str(lla),
            "label_b": _stable_label_str(llb),
            "a_params": aa,
            "b_params": bb,
            "reason": str(reason),
        }

    # Seed each chain with two labels and points from each.
    proposals = 0
    accepted = 0
    flip_steps = 0
    for chain_i in range(int(chains)):
        lk0 = str(label_keys[rng.randrange(0, len(label_keys))])
        lk1 = str(label_keys[rng.randrange(0, len(label_keys))])
        if lk0 == lk1:
            lk1 = str(label_keys[(label_keys.index(lk0) + 1) % len(label_keys)])

        a = dict(labels_to_points[lk0][rng.randrange(0, len(labels_to_points[lk0]))])
        b = dict(labels_to_points[lk1][rng.randrange(0, len(labels_to_points[lk1]))])

        la = _eval_label_cached(s, kwargs=a, eval_cache=eval_cache)
        lb = _eval_label_cached(s, kwargs=b, eval_cache=eval_cache)
        if la == lb:
            # Fall back to random points if the pool drifted.
            for _ in range(64):
                a = _sample_full_kwargs(s, rng=rng)
                b = _sample_full_kwargs(s, rng=rng)
                la = _eval_label_cached(s, kwargs=a, eval_cache=eval_cache)
                lb = _eval_label_cached(s, kwargs=b, eval_cache=eval_cache)
                if la != lb:
                    break
        if la == lb:
            continue

        cur_a, cur_la, cur_b, cur_lb = dict(a), la, dict(b), lb
        cur_dist = _pair_distance_l1(s, cur_a, cur_b)
        _record_pair(cur_a, cur_la, cur_b, cur_lb, reason=f"seed_chain_{chain_i}")

        for step_i in range(int(steps)):
            # Mutate one side.
            mutate_left = bool(rng.random() < 0.5)
            if mutate_left:
                base = cur_a
                base_lbl = cur_la
                other = cur_b
                other_lbl = cur_lb
            else:
                base = cur_b
                base_lbl = cur_lb
                other = cur_a
                other_lbl = cur_la

            prop = _mutate_point_local(s, base=base, rng=rng)
            prop_lbl = _eval_label_cached(s, kwargs=prop, eval_cache=eval_cache)

            # Maintain a differing-label pair. If we flipped into the other label,
            # use the (old, new) pair which is usually very close.
            if prop_lbl == other_lbl:
                cand_a, cand_la = dict(base), base_lbl
                cand_b, cand_lb = dict(prop), prop_lbl
                reason = f"flip_step_{chain_i}_{step_i}"
                flip_steps += 1
            else:
                cand_a, cand_la = dict(prop), prop_lbl
                cand_b, cand_lb = dict(other), other_lbl
                reason = f"walk_step_{chain_i}_{step_i}"

            if cand_la == cand_lb:
                continue

            cand_dist = _pair_distance_l1(s, cand_a, cand_b)

            # Metropolis-style acceptance using pair density ~ 1/(1+dist).
            # Accept always if improved; otherwise accept with probability ratio.
            accept = False
            if cand_dist <= cur_dist:
                accept = True
            else:
                num = 1.0 / (1.0 + float(cand_dist))
                den = 1.0 / (1.0 + float(cur_dist))
                ratio = 1.0 if den <= 0 else min(1.0, float(num / den))
                accept = bool(rng.random() < float(ratio))

            _record_pair(cand_a, cand_la, cand_b, cand_lb, reason=reason)

            proposals += 1
            if accept:
                accepted += 1
                # Keep the same left/right ordering to avoid oscillation.
                if mutate_left:
                    cur_a, cur_la = dict(cand_a), cand_la
                    cur_b, cur_lb = dict(cand_b), cand_lb
                else:
                    cur_b, cur_lb = dict(cand_a), cand_la
                    cur_a, cur_la = dict(cand_b), cand_lb
                cur_dist = int(cand_dist)

    # Select best pairs (lowest distance) and attempt to turn them into axis-aligned boundaries via ddmin+refine.
    best_items = [best[k] for k in sorted(best.keys())]
    if int(max_pairs) > 0:
        best_items = best_items[: int(max_pairs)]

    pair_cases: list[dict[str, Any]] = []
    for i, it in enumerate(best_items):
        a = dict(it.get("a_params", {}))
        b = dict(it.get("b_params", {}))
        pair_cases.append(
            {
                "id": f"mcmc_pair_{i}__a",
                "params": a,
                "reason": f"MCMC opposite-label pair endpoint A (dist={int(it.get('distance_l1', 0))})",
            }
        )
        pair_cases.append(
            {
                "id": f"mcmc_pair_{i}__b",
                "params": b,
                "reason": f"MCMC opposite-label pair endpoint B (dist={int(it.get('distance_l1', 0))})",
            }
        )

    axis_boundaries: list[dict[str, Any]] = []
    for idx, it in enumerate(best_items):
        a = dict(it["a_params"])
        b = dict(it["b_params"])
        la = _eval_label_cached(s, kwargs=a, eval_cache=eval_cache)
        lb = _eval_label_cached(s, kwargs=b, eval_cache=eval_cache)
        if la == lb:
            continue

        # First, shrink the pair in L1 (coordinate-wise) so boundary refinement is cheaper
        # and the witness is closer to "just around" the interaction region.
        a, b = _shrink_pair_l1_coordinate_descent(s, a=a, la=la, b=b, lb=lb, eval_cache=eval_cache)

        a2, b2 = _ddmin_pair_hamming(s, a=a, la=la, b=b, lb=lb, eval_cache=eval_cache)
        diffs = [p for p in sorted(s.domains.keys()) if a2.get(p) != b2.get(p)]
        if len(diffs) != 1:
            axis_boundaries.extend(
                _axis_boundaries_from_pair_path(
                    s,
                    a=a2,
                    la=la,
                    b=b2,
                    lb=lb,
                    eval_cache=eval_cache,
                    pair_idx=int(idx),
                )
            )
            continue

        param = str(diffs[0])
        dom = s.domains[param]

        va = int(a2.get(param))
        vb = int(b2.get(param))
        lo = int(min(va, vb))
        hi = int(max(va, vb))

        # Build context with the agreed values for all other params.
        ctx = {p: a2.get(p) for p in s.domains.keys() if p != param}

        # Refine to adjacent flip boundaries under this context (if possible).
        eval_cache_1d: dict[int, Hashable] = {}
        kwargs_lo = dict(s.fixed_kwargs)
        kwargs_lo.update(ctx)
        kwargs_lo[param] = int(lo)
        l_lo = _eval_label_cached(s, kwargs=kwargs_lo, eval_cache=eval_cache)
        kwargs_hi = dict(s.fixed_kwargs)
        kwargs_hi.update(ctx)
        kwargs_hi[param] = int(hi)
        l_hi = _eval_label_cached(s, kwargs=kwargs_hi, eval_cache=eval_cache)
        if l_lo == l_hi:
            continue

        bounds = _refine_boundaries_in_interval(
            s,
            param=param,
            context=ctx,
            lo=lo,
            hi=hi,
            label_lo=l_lo,
            label_hi=l_hi,
            eval_cache=eval_cache_1d,
            max_steps=4096,
        )
        if not bounds:
            continue

        # Use the smallest upper bound (closest flip) deterministically.
        lower, upper, l0, l1 = sorted(bounds, key=lambda t: (t[1] - t[0], t[1], t[0]))[0]
        boundary_value = int(upper)
        cases: list[dict[str, Any]] = []
        for tag, v in [
            ("just_below", boundary_value - 1),
            ("at", boundary_value),
            ("just_above", boundary_value + 1),
        ]:
            if not _in_range(dom, int(v)) and not bool(dom.include_oob):
                continue
            kw = dict(s.fixed_kwargs)
            kw.update(ctx)
            kw[param] = int(v)
            cases.append(
                {
                    "id": f"mcmc_{idx}__{param}__b{boundary_value}__{tag}",
                    "params": kw,
                    "reason": (
                        f"MCMC pair -> ddmin axis boundary near {param}={boundary_value}: "
                        f"{_stable_label_str(l0)} -> {_stable_label_str(l1)}"
                    ),
                }
            )
        axis_boundaries.append(
            {
                "param": param,
                "context_id": int(idx),
                "context": ctx,
                "lower": int(lower),
                "upper": int(upper),
                "boundary_value": int(boundary_value),
                "label_lower": _stable_label_str(l0),
                "label_upper": _stable_label_str(l1),
                "cases": cases,
                "source_pair": {
                    "distance_l1": int(it["distance_l1"]),
                    "label_a": str(it["label_a"]),
                    "label_b": str(it["label_b"]),
                },
            }
        )

    return {
        "schema": "tools.bva.mcmc_boundary_mining.v1",
        "scenario": s.name,
        "seed": int(seed) if seed is not None else (int(s.seed) + 1337),
        "chains": int(chains),
        "steps": int(steps),
        "status": "ok",
        "labels_seen": sorted(labels_to_points.keys()),
        "label_counts_bootstrap": {k: len(v) for k, v in sorted(labels_to_points.items(), key=lambda kv: kv[0])},
        "stats": {
            "bootstrap_points": int(bootstrap),
            "unique_evals": int(len(eval_cache)),
            "pairs_recorded": int(len(best_items)),
            "proposals": int(proposals),
            "accepted": int(accepted),
            "accept_rate": (float(accepted) / float(proposals)) if proposals > 0 else None,
            "flip_steps": int(flip_steps),
        },
        "pairs": best_items,
        "pair_cases": pair_cases,
        "axis_boundaries": axis_boundaries,
    }


def _stable_label_str(lbl: Hashable) -> str:
    """Make labels JSON-friendly and stable-ish across runs."""
    try:
        return json.dumps(lbl, sort_keys=True, default=str)
    except Exception:  # noqa: BLE001
        return str(lbl)


def _print_static_bva(s: Scenario) -> None:
    print(f"Scenario: {s.name}")
    for p, d in sorted(s.domains.items()):
        print()
        print(f"[{p}] domain = [{d.min_value}, {d.max_value}]")
        for g in _static_bva_groups_for_int_domain(p, d):
            print(f"  - {g['group']}:")
            for c in g["cases"]:
                print(f"    * {c['value']!r}: {c['reason']}")


def _sample_full_kwargs(s: Scenario, *, rng: random.Random) -> dict[str, Any]:
    """Sample a full kwargs assignment within declared domains (best-effort)."""
    kw: dict[str, Any] = dict(s.fixed_kwargs)
    for p, dom in s.domains.items():
        mn = int(dom.min_value)
        mx = int(dom.max_value)
        if mn == mx:
            kw[p] = mn
            continue
        candidates: list[int] = [mn, mx, (mn + mx) // 2]
        if mn + 1 <= mx:
            candidates.append(mn + 1)
        if mx - 1 >= mn:
            candidates.append(mx - 1)
        candidates.extend(int(v) for v in dom.specials if isinstance(v, int))
        candidates = [int(v) for v in _uniq_keep_order(candidates) if _in_range(dom, int(v))]
        if candidates and rng.random() < 0.65:
            kw[p] = int(candidates[rng.randrange(0, len(candidates))])
        else:
            kw[p] = int(rng.randint(mn, mx))
    return kw


def _l1_distance_over_domains(s: Scenario, a: dict[str, Any], b: dict[str, Any]) -> int | None:
    d = 0
    for p in s.domains.keys():
        va = a.get(p, None)
        vb = b.get(p, None)
        if not isinstance(va, int) or isinstance(va, bool):
            return None
        if not isinstance(vb, int) or isinstance(vb, bool):
            return None
        d += abs(int(va) - int(vb))
    return int(d)


def _mine_global_flip_pairs(s: Scenario, *, rng: random.Random) -> list[dict[str, Any]]:
    """Mine close-by pairs of full assignments with different labels.

    This is a lightweight analogue of "equivalence-class discrimination" in the paper:
    we treat the scenario label (or label+pathsig) as the class, and look for small
    L1-distance flips between classes.
    """
    n = int(s.global_samples)
    if n <= 0:
        return []
    points: list[tuple[dict[str, Any], Hashable]] = []
    for _ in range(n):
        kw = _sample_full_kwargs(s, rng=rng)
        lbl = _eval_label(s, kwargs=dict(kw))
        points.append((kw, lbl))

    pairs: list[tuple[int, int, int]] = []
    for i in range(len(points)):
        a, la = points[i]
        for j in range(i + 1, len(points)):
            b, lb = points[j]
            if la == lb:
                continue
            dist = _l1_distance_over_domains(s, a, b)
            if dist is None:
                continue
            pairs.append((int(dist), int(i), int(j)))
    pairs.sort()

    out: list[dict[str, Any]] = []
    max_pairs = 12
    for k, (dist, i, j) in enumerate(pairs[:max_pairs]):
        a, la = points[i]
        b, lb = points[j]
        diffs: list[dict[str, Any]] = []
        for p in s.domains.keys():
            va = a.get(p)
            vb = b.get(p)
            if va != vb:
                diffs.append({"param": p, "a": va, "b": vb, "abs_diff": abs(int(va) - int(vb))})
        out.append(
            {
                "id": f"pair_{k}",
                "distance_l1": int(dist),
                "label_a": _stable_label_str(la),
                "label_b": _stable_label_str(lb),
                "a_params": a,
                "b_params": b,
                "diffs": diffs,
                "reason": "global random-sample flip pair (budgeted; heuristic)",
            }
        )
    return out


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scenario", required=True, help="Path to a Python scenario module.")
    ap.add_argument("--print-bva", action="store_true", help="Print static BVA suggestions.")
    ap.add_argument("--mine-boundaries", action="store_true", help="Mine dynamic label/path boundaries.")
    ap.add_argument("--mine-mcmc", action="store_true", help="Mine boundaries using pair-density MCMC (global, budgeted).")
    ap.add_argument("--mcmc-chains", type=int, default=8, help="MCMC chains (global mining).")
    ap.add_argument("--mcmc-steps", type=int, default=512, help="MCMC steps per chain (global mining).")
    ap.add_argument("--mcmc-max-pairs", type=int, default=12, help="Max best pairs to keep (global mining).")
    ap.add_argument("--mcmc-seed", type=int, default=-1, help="MCMC RNG seed override (-1 uses scenario.seed+1337).")
    ap.add_argument("--out", default="", help="Output JSON path (default: internal/bva/<scenario>.json)")
    args = ap.parse_args(argv)

    s = _load_scenario(args.scenario)

    if args.print_bva:
        _print_static_bva(s)

    if not args.mine_boundaries and not args.mine_mcmc:
        return 0

    out: dict[str, Any]
    if args.mine_boundaries:
        out = mine_dynamic_boundaries(s)
    else:
        out = {
            "schema": "tools.bva.boundary_mining.v1",
            "scenario": s.name,
            "time_unix_s": int(time.time()),
            "static_bva": {
                p: _static_bva_groups_for_int_domain(p, d) for p, d in sorted(s.domains.items())
            },
            "dynamic_boundaries": [],
            "global_boundaries": [],
            "labels_seen": {},
        }

    if args.mine_mcmc:
        mcmc_seed = None if int(args.mcmc_seed) < 0 else int(args.mcmc_seed)
        out["mcmc"] = mine_mcmc_boundaries(
            s,
            chains=int(args.mcmc_chains),
            steps=int(args.mcmc_steps),
            max_pairs=int(args.mcmc_max_pairs),
            seed=mcmc_seed,
        )

    out_path = str(args.out).strip()
    if not out_path:
        safe_name = "".join(ch if ch.isalnum() or ch in ("-", "_") else "_" for ch in s.name)
        out_path = os.path.join("internal", "bva", f"{safe_name}.json")

    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2, sort_keys=True)
        f.write("\n")
    print(f"Wrote: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
