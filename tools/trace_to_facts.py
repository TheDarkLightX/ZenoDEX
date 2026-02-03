#!/usr/bin/env python3
"""
Relational decomposition helper for counterexamples / traces.

This converts a (pre_state, post_state) pair into a set of simple `in/3`, `out/3`,
and optional `delta/3` facts (Prolog/ILP-friendly). The intent is to make it easy
to learn *small relational lemmas* from traces (e.g., per-variable updates) and
then re-compose them into a verified whole.

Input format:
  - JSON object mapping string keys -> primitive values (int/bool/str)

Example:
  python3 tools/trace_to_facts.py --id ex1 --pre pre.json --post post.json --delta
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


Value = bool | int | str


class FactError(Exception):
    pass


def _require_mapping(obj: Any, *, name: str) -> dict[str, Any]:
    if not isinstance(obj, dict):
        raise FactError(f"{name} must be a JSON object")
    return obj


def _require_value(obj: Any, *, name: str) -> Value:
    if isinstance(obj, bool):
        return obj
    if isinstance(obj, int):
        return obj
    if isinstance(obj, str):
        return obj
    raise FactError(f"{name} must be a bool|int|string")


def _load_state(path: Path) -> dict[str, Value]:
    raw = path.read_text(encoding="utf-8")
    obj = json.loads(raw)
    data = _require_mapping(obj, name=str(path))
    out: dict[str, Value] = {}
    for k, v in data.items():
        if not isinstance(k, str) or not k:
            raise FactError(f"{path}: keys must be non-empty strings")
        out[k] = _require_value(v, name=f"{path}:{k}")
    return out


def _q_atom(text: str) -> str:
    # Prolog quoted atom using single quotes, escaping `'` by doubling it.
    return "'" + text.replace("'", "''") + "'"


def _render_value(v: Value) -> str:
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        return _q_atom(v)
    raise TypeError("unreachable")


def _emit_fact(*, pred: str, ex_id: str, key: str, value: str) -> str:
    return f"{pred}({_q_atom(ex_id)},{_q_atom(key)},{value})."


def state_pair_to_facts(
    *,
    ex_id: str,
    pre: dict[str, Value],
    post: dict[str, Value],
    include_delta: bool,
    only_changed: bool,
) -> list[str]:
    facts: list[str] = []
    keys = sorted(set(pre.keys()) | set(post.keys()))
    for k in keys:
        pre_has = k in pre
        post_has = k in post
        pre_v = pre.get(k)
        post_v = post.get(k)
        changed = (pre_has != post_has) or (pre_has and post_has and pre_v != post_v)
        if only_changed and not changed:
            continue
        if pre_has:
            facts.append(_emit_fact(pred="in", ex_id=ex_id, key=k, value=_render_value(pre_v)))  # type: ignore[arg-type]
        if post_has:
            facts.append(_emit_fact(pred="out", ex_id=ex_id, key=k, value=_render_value(post_v)))  # type: ignore[arg-type]
        if include_delta and pre_has and post_has and isinstance(pre_v, int) and isinstance(post_v, int) and not isinstance(pre_v, bool) and not isinstance(post_v, bool):
            d = post_v - pre_v
            facts.append(_emit_fact(pred="delta", ex_id=ex_id, key=k, value=str(d)))
    return facts


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description="Convert pre/post JSON states into ILP-friendly facts.")
    p.add_argument("--id", default="ex1", help="Example/trace id for facts (default: ex1)")
    p.add_argument("--pre", required=True, type=Path, help="Path to pre-state JSON object")
    p.add_argument("--post", required=True, type=Path, help="Path to post-state JSON object")
    p.add_argument("--delta", action="store_true", help="Emit delta/3 facts for integer-valued keys present in both states")
    p.add_argument("--only-changed", action="store_true", help="Emit facts only for keys whose values changed or were added/removed")
    args = p.parse_args(argv)

    try:
        pre = _load_state(args.pre)
        post = _load_state(args.post)
        facts = state_pair_to_facts(ex_id=str(args.id), pre=pre, post=post, include_delta=bool(args.delta), only_changed=bool(args.only_changed))
    except (OSError, json.JSONDecodeError, FactError) as exc:
        print(f"trace_to_facts error: {exc}", file=sys.stderr)
        return 2

    for line in facts:
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

