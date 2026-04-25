from __future__ import annotations

"""
Deterministic boundary-path explorer for state validators.

This is an offline discovery tool for branchy canonicalization and replay-
protection boundaries. It records distinct outcome/path-signature pairs for a
small set of high-value validators and explores a bounded frontier of payload
mutations while keeping the validator surface deterministic.
"""

import argparse
import copy
import hashlib
import heapq
import json
import sys
from dataclasses import asdict, dataclass, is_dataclass
from pathlib import Path
from typing import Any, Callable, Sequence

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from src.state.canonical import bounded_json_utf8_size, canonical_hex_fixed_allow_0x, domain_sep_bytes
from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch


OutcomeFn = Callable[[object], str]
MutationFn = Callable[[object], object]


def _intent(*, sender: str, nonce: int | None) -> Intent:
    fields: dict[str, Any] = {
        "pool_id": "0x" + "aa" * 32,
        "asset_in": "0x" + "01" * 32,
        "asset_out": "0x" + "02" * 32,
        "amount_in": 1,
        "min_amount_out": 0,
    }
    if nonce is not None:
        fields["nonce"] = nonce
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "33" * 32,
        sender_pubkey=sender,
        deadline=1,
        fields=fields,
    )


def _nonce_table_with_last(pubkey: str, last_nonce: int) -> NonceTable:
    table = NonceTable()
    table.set_last(pubkey, last_nonce)
    return table


PK_48B = "0x" + "11" * 48


@dataclass(frozen=True)
class Mutation:
    name: str
    apply: MutationFn


@dataclass(frozen=True)
class Target:
    name: str
    trace_files: tuple[Path, ...]
    valid_seed: object
    outcome: OutcomeFn
    mutations: tuple[Mutation, ...]


@dataclass(frozen=True)
class BoundaryCase:
    mutation: str
    depth: int
    outcome_label: str
    path_id: str
    path_length: int


@dataclass(frozen=True)
class BoundaryTargetReport:
    target: str
    total_cases: int
    unique_outcome_count: int
    unique_path_count: int
    cases: tuple[BoundaryCase, ...]


CANONICAL_FILE = (ROOT_DIR / "src/state/canonical.py").resolve()
NONCES_FILE = (ROOT_DIR / "src/state/nonces.py").resolve()


def _hex_outcome(payload: object) -> str:
    args = payload
    try:
        result = canonical_hex_fixed_allow_0x(args["hex_str"], nbytes=args["nbytes"], name=args["name"])
        return f"ok:{result}"
    except Exception as exc:
        return f"{type(exc).__name__}:{exc}"


def _domain_sep_outcome(payload: object) -> str:
    args = payload
    try:
        result = domain_sep_bytes(args["label"], version=args["version"])
        return f"ok:{result!r}"
    except Exception as exc:
        return f"{type(exc).__name__}:{exc}"


def _bounded_json_outcome(payload: object) -> str:
    args = payload
    try:
        result = bounded_json_utf8_size(
            args["value"],
            max_bytes=args["max_bytes"],
            max_depth=args["max_depth"],
            max_items=args["max_items"],
        )
        return f"ok:{result}"
    except Exception as exc:
        return f"{type(exc).__name__}:{exc}"


def _nonce_batch_outcome(payload: object) -> str:
    args = payload
    ok, err, updated = validate_and_apply_intent_nonce_batch(
        nonces=args["nonces"],
        intents=args["intents"],
        require_all_nonces=args["require_all_nonces"],
    )
    if ok:
        assert updated is not None
        return f"ok:last={updated.get_last(PK_48B)}"
    return f"reject:{err}"


TARGETS: tuple[Target, ...] = (
    Target(
        name="canonical_hex_fixed_allow_0x",
        trace_files=(CANONICAL_FILE,),
        valid_seed={"hex_str": "0x" + "aa" * 32, "nbytes": 32, "name": "x"},
        outcome=_hex_outcome,
        mutations=(
            Mutation("missing_prefix_raw_ok", lambda seed: {**copy.deepcopy(seed), "hex_str": "AA" * 32}),
            Mutation("uppercase_prefixed_ok", lambda seed: {**copy.deepcopy(seed), "hex_str": "0X" + "AA" * 32}),
            Mutation("bad_len", lambda seed: {**copy.deepcopy(seed), "hex_str": "0x1"}),
            Mutation("bad_chars", lambda seed: {**copy.deepcopy(seed), "hex_str": "0x" + "gg" * 32}),
            Mutation("non_str_hex", lambda seed: {**copy.deepcopy(seed), "hex_str": None}),
            Mutation("bad_nbytes", lambda seed: {**copy.deepcopy(seed), "nbytes": 0}),
        ),
    ),
    Target(
        name="domain_sep_bytes",
        trace_files=(CANONICAL_FILE,),
        valid_seed={"label": "abc", "version": 1},
        outcome=_domain_sep_outcome,
        mutations=(
            Mutation("nul", lambda seed: {**copy.deepcopy(seed), "label": "a\x00b"}),
            Mutation("nonascii", lambda seed: {**copy.deepcopy(seed), "label": "é"}),
            Mutation("empty", lambda seed: {**copy.deepcopy(seed), "label": ""}),
            Mutation("non_str", lambda seed: {**copy.deepcopy(seed), "label": None}),
            Mutation("bad_version", lambda seed: {**copy.deepcopy(seed), "version": 0}),
        ),
    ),
    Target(
        name="bounded_json_utf8_size",
        trace_files=(CANONICAL_FILE,),
        valid_seed={"value": {"a": [1, 2]}, "max_bytes": 100, "max_depth": 10, "max_items": 10},
        outcome=_bounded_json_outcome,
        mutations=(
            Mutation(
                "depth_exceeded",
                lambda seed: {**copy.deepcopy(seed), "value": {"a": {"b": {"c": 1}}}, "max_depth": 2},
            ),
            Mutation("items_exceeded", lambda seed: {**copy.deepcopy(seed), "value": [1, 2, 3], "max_items": 2}),
            Mutation("bytes_exceeded", lambda seed: {**copy.deepcopy(seed), "value": {"a": "x" * 200}, "max_bytes": 10}),
            Mutation("bad_max_depth", lambda seed: {**copy.deepcopy(seed), "max_depth": 0}),
            Mutation("bad_max_items", lambda seed: {**copy.deepcopy(seed), "max_items": 0}),
            Mutation("bad_limits", lambda seed: {**copy.deepcopy(seed), "max_bytes": 0}),
            Mutation("non_str_dict_key", lambda seed: {**copy.deepcopy(seed), "value": {1: "x"}}),
            Mutation("unsupported_float", lambda seed: {**copy.deepcopy(seed), "value": 1.5}),
        ),
    ),
    Target(
        name="validate_and_apply_intent_nonce_batch",
        trace_files=(NONCES_FILE, CANONICAL_FILE),
        valid_seed={
            "nonces": NonceTable(),
            "intents": [_intent(sender=PK_48B, nonce=1), _intent(sender=PK_48B, nonce=2)],
            "require_all_nonces": True,
        },
        outcome=_nonce_batch_outcome,
        mutations=(
            Mutation("empty_batch_ok", lambda seed: {**copy.deepcopy(seed), "intents": []}),
            Mutation("missing_nonce", lambda seed: {**copy.deepcopy(seed), "intents": [_intent(sender=PK_48B, nonce=None)]}),
            Mutation(
                "mixed_presence",
                lambda seed: {
                    **copy.deepcopy(seed),
                    "intents": [_intent(sender=PK_48B, nonce=1), _intent(sender="0x" + "22" * 48, nonce=None)],
                    "require_all_nonces": False,
                },
            ),
            Mutation(
                "duplicate_nonce",
                lambda seed: {
                    **copy.deepcopy(seed),
                    "intents": [_intent(sender=PK_48B, nonce=1), _intent(sender=PK_48B, nonce=1)],
                },
            ),
            Mutation(
                "nonce_gap",
                lambda seed: {
                    **copy.deepcopy(seed),
                    "intents": [_intent(sender=PK_48B, nonce=1), _intent(sender=PK_48B, nonce=3)],
                },
            ),
            Mutation(
                "seeded_nonce_table_ok",
                lambda seed: {
                    **copy.deepcopy(seed),
                    "nonces": _nonce_table_with_last(PK_48B, 5),
                    "intents": [_intent(sender=PK_48B, nonce=6), _intent(sender=PK_48B, nonce=7)],
                },
            ),
            Mutation(
                "bad_sender",
                lambda seed: {**copy.deepcopy(seed), "intents": [_intent(sender="not-hex", nonce=1)]},
            ),
        ),
    ),
)

TARGET_INDEX = {target.name: target for target in TARGETS}


def _hash_lines(lines: Sequence[str]) -> str:
    return hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()[:16]


def _stable_jsonable(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if is_dataclass(value):
        return _stable_jsonable(asdict(value))
    if isinstance(value, dict):
        return {str(key): _stable_jsonable(val) for key, val in sorted(value.items(), key=lambda item: str(item[0]))}
    if isinstance(value, (list, tuple)):
        return [_stable_jsonable(item) for item in value]
    if isinstance(value, set):
        return sorted(_stable_jsonable(item) for item in value)
    return repr(value)


def _payload_signature(payload: object) -> str:
    canonical = json.dumps(_stable_jsonable(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:16]


def _payload_expandable(target: Target, payload: object) -> bool:
    if target.name in {"canonical_hex_fixed_allow_0x", "domain_sep_bytes", "bounded_json_utf8_size"}:
        return isinstance(payload, dict)
    if target.name == "validate_and_apply_intent_nonce_batch":
        return isinstance(payload, dict) and isinstance(payload.get("intents"), list)
    return False


def _trace_outcome(target: Target, payload: object) -> tuple[str, str, int]:
    trace_names = {str(path.resolve()) for path in target.trace_files}
    lines: list[str] = []
    last_loc: str | None = None

    def tracer(frame, event, arg):  # type: ignore[no-untyped-def]
        nonlocal last_loc
        if event == "line":
            filename = str(Path(frame.f_code.co_filename).resolve())
            if filename in trace_names:
                loc = f"{Path(filename).name}:{frame.f_lineno}"
                if loc != last_loc:
                    lines.append(loc)
                    last_loc = loc
        return tracer

    previous = sys.gettrace()
    try:
        sys.settrace(tracer)
        outcome = target.outcome(payload)
    finally:
        sys.settrace(previous)
    return outcome, _hash_lines(lines), len(lines)


def explore_target(name: str, *, max_depth: int = 2, max_frontier: int = 256) -> BoundaryTargetReport:
    target = TARGET_INDEX[name]
    cases: list[BoundaryCase] = []
    seen_pairs: set[tuple[str, str]] = set()
    seen_outcomes: set[str] = set()
    seen_paths: set[str] = set()
    seen_payloads: set[str] = {_payload_signature(target.valid_seed)}
    frontier: list[tuple[int, int, int, str, object]] = [(0, 0, 0, "valid_seed", copy.deepcopy(target.valid_seed))]
    explored = 0
    schedule_seq = 1

    while frontier and explored < max_frontier:
        _priority, depth, _seq, mutation_name, payload = heapq.heappop(frontier)
        explored += 1
        outcome, path_id, path_length = _trace_outcome(target, payload)
        pair = (outcome, path_id)
        if pair not in seen_pairs:
            seen_pairs.add(pair)
            seen_outcomes.add(outcome)
            seen_paths.add(path_id)
            cases.append(
                BoundaryCase(
                    mutation=mutation_name,
                    depth=depth,
                    outcome_label=outcome,
                    path_id=path_id,
                    path_length=path_length,
                )
            )

        if depth >= max_depth or not _payload_expandable(target, payload):
            continue

        for order, mutation in enumerate(target.mutations):
            try:
                next_payload = mutation.apply(copy.deepcopy(payload))
            except Exception:
                continue
            signature = _payload_signature(next_payload)
            if signature in seen_payloads:
                continue
            seen_payloads.add(signature)
            next_name = mutation.name if mutation_name == "valid_seed" else f"{mutation_name}->{mutation.name}"
            heapq.heappush(
                frontier,
                (-path_length, depth + 1, schedule_seq + order, next_name, next_payload),
            )
        schedule_seq += len(target.mutations)

    cases_sorted = tuple(sorted(cases, key=lambda case: (case.outcome_label, case.depth, case.mutation, case.path_id)))
    return BoundaryTargetReport(
        target=name,
        total_cases=len(cases_sorted),
        unique_outcome_count=len(seen_outcomes),
        unique_path_count=len(seen_paths),
        cases=cases_sorted,
    )


def explore_all_targets(*, max_depth: int = 2, max_frontier: int = 256) -> tuple[BoundaryTargetReport, ...]:
    return tuple(explore_target(target.name, max_depth=max_depth, max_frontier=max_frontier) for target in TARGETS)


def _reports_json(reports: Sequence[BoundaryTargetReport]) -> dict[str, Any]:
    return {
        "schema": "zenodex/state-boundary-concolic/v1",
        "reports": [asdict(report) for report in reports],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Deterministic boundary-path explorer for state validators.")
    parser.add_argument(
        "--target",
        default="all",
        choices=("all",) + tuple(sorted(TARGET_INDEX)),
    )
    parser.add_argument(
        "--format",
        default="json",
        choices=("json", "text"),
    )
    parser.add_argument("--max-depth", type=int, default=2)
    parser.add_argument("--max-frontier", type=int, default=256)
    args = parser.parse_args(list(argv) if argv is not None else None)

    reports = (
        explore_all_targets(max_depth=args.max_depth, max_frontier=args.max_frontier)
        if args.target == "all"
        else (explore_target(args.target, max_depth=args.max_depth, max_frontier=args.max_frontier),)
    )
    if args.format == "json":
        print(json.dumps(_reports_json(reports), indent=2, sort_keys=True))
    else:
        for report in reports:
            print(f"[{report.target}] cases={report.total_cases} outcomes={report.unique_outcome_count} paths={report.unique_path_count}")
            for case in report.cases:
                print(
                    f"  - depth={case.depth} {case.mutation}: {case.outcome_label} "
                    f"path={case.path_id} len={case.path_length}"
                )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
