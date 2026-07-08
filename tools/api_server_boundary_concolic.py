"""
Deterministic boundary-path explorer for `src.integration.api_server`.

This is an offline assurance pilot inspired by concolic testing, not a general
symbolic executor. It starts from valid structured payloads for selected parser
helpers, applies structure-preserving and branch-targeted mutations, explores a
bounded frontier, records exception labels, and traces line-path signatures
through the parser code. The output is a replayable atlas of distinct boundary
paths.
"""
# ruff: noqa: E402,I001

from __future__ import annotations

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

from src.integration import api_server  # noqa: E402


ParserFn = Callable[[object], object]
MutationFn = Callable[[object], object]


def _valid_proof_flags() -> dict[str, int]:
    return {
        "cpmm_ok": 1,
        "balance_ok": 1,
        "token_ok": 1,
        "buyback_floor_ok": 1,
        "buyback_floor_fixedpoint_ok": 1,
        "rebate_ok": 1,
        "lock_weight_ok": 1,
        "proof_ok": 1,
        "binding_ok": 1,
    }


def _valid_feature_extension_inputs() -> dict[str, int]:
    return {
        "trade_amount": 10,
        "fee_charged": 1,
        "buyback_amount": 1,
        "burned_amount": 0,
        "supply_before": 1_000,
        "supply_after": 999,
        "supply_floor": 100,
        "unit_scale": 1,
        "rebate_rate_bps": 10,
        "rebate_amount": 1,
        "rebate_cap": 2,
        "lock_days": 30,
        "stake_amount": 10,
        "tier1_days": 7,
        "tier2_days": 30,
        "weight_t1": 1,
        "weight_t2": 2,
        "weight_t3": 3,
        "weight_claimed": 1,
        "weighted_stake": 10,
    }


def _set_key(payload: object, key: str, value: object) -> object:
    out = copy.deepcopy(payload)
    if not isinstance(out, dict):
        raise TypeError("payload must be a dict")
    out[key] = value
    return out


def _drop_key(payload: object, key: str) -> object:
    out = copy.deepcopy(payload)
    if not isinstance(out, dict):
        raise TypeError("payload must be a dict")
    out.pop(key, None)
    return out


def _set_index(payload: object, idx: int, value: object) -> object:
    out = copy.deepcopy(payload)
    if not isinstance(out, list):
        raise TypeError("payload must be a list")
    out[idx] = value
    return out


def _append_entry(payload: object, entry: object) -> object:
    out = copy.deepcopy(payload)
    if not isinstance(out, list):
        raise TypeError("payload must be a list")
    out.append(entry)
    return out


@dataclass(frozen=True)
class Mutation:
    name: str
    apply: MutationFn


@dataclass(frozen=True)
class ParserTarget:
    name: str
    parser: ParserFn
    trace_files: tuple[Path, ...]
    valid_seed: object
    mutations: tuple[Mutation, ...]


@dataclass(frozen=True)
class BoundaryCase:
    mutation: str
    depth: int
    outcome_label: str
    path_id: str
    path_length: int
    payload: object


@dataclass(frozen=True)
class BoundaryTargetReport:
    target: str
    total_cases: int
    unique_outcome_count: int
    unique_path_count: int
    cases: tuple[BoundaryCase, ...]


API_SERVER_FILE = Path(api_server.__file__).resolve()
FEATURE_EXTENSION_FILE = Path(api_server.__file__).resolve().parent / "settlement_feature_extension_packet.py"


def _parser_file(parser: ParserFn) -> Path:
    return Path(parser.__code__.co_filename).resolve()


TARGETS: tuple[ParserTarget, ...] = (
    ParserTarget(
        name="price_history",
        parser=api_server._parse_price_history_payload,
        trace_files=(_parser_file(api_server._parse_price_history_payload),),
        valid_seed=[100, 101, 102],
        mutations=(
            Mutation("negative_first", lambda seed: _set_index(seed, 0, -1)),
            Mutation("negative_second", lambda seed: _set_index(seed, 1, -1)),
            Mutation("bool_second", lambda seed: _set_index(seed, 1, True)),
            Mutation("string_third", lambda seed: _set_index(seed, 2, "102")),
            Mutation("whole_none", lambda _seed: None),
            Mutation("whole_object", lambda _seed: {"price_pp": 1}),
            Mutation("short_arity", lambda _seed: [100, 101]),
            Mutation("long_arity", lambda _seed: [100, 101, 102, 103]),
        ),
    ),
    ParserTarget(
        name="settlement_proof_flags",
        parser=api_server._parse_settlement_proof_flags_payload,
        trace_files=(_parser_file(api_server._parse_settlement_proof_flags_payload),),
        valid_seed=_valid_proof_flags(),
        mutations=(
            Mutation("missing_first_flag", lambda seed: _drop_key(seed, "cpmm_ok")),
            Mutation("missing_middle_flag", lambda seed: _drop_key(seed, "proof_ok")),
            Mutation("missing_last_flag", lambda seed: _drop_key(seed, "binding_ok")),
            Mutation("bool_first_flag", lambda seed: _set_key(seed, "cpmm_ok", True)),
            Mutation("string_middle_flag", lambda seed: _set_key(seed, "proof_ok", "1")),
            Mutation("out_of_domain_last_flag", lambda seed: _set_key(seed, "binding_ok", 2)),
            Mutation("whole_list", lambda _seed: []),
        ),
    ),
    ParserTarget(
        name="balance_table",
        parser=api_server._parse_balance_table_payload,
        trace_files=(_parser_file(api_server._parse_balance_table_payload),),
        valid_seed=[{"pubkey": "pk1", "asset": "asset1", "amount": 7}],
        mutations=(
            Mutation(
                "empty_pubkey",
                lambda seed: [{"pubkey": "", "asset": seed[0]["asset"], "amount": seed[0]["amount"]}],
            ),
            Mutation(
                "empty_asset",
                lambda seed: [{"pubkey": seed[0]["pubkey"], "asset": "", "amount": seed[0]["amount"]}],
            ),
            Mutation(
                "negative_amount",
                lambda seed: [{"pubkey": seed[0]["pubkey"], "asset": seed[0]["asset"], "amount": -1}],
            ),
            Mutation(
                "duplicate_entry",
                lambda seed: _append_entry(seed, copy.deepcopy(seed[0])),
            ),
            Mutation(
                "second_entry_bad_asset",
                lambda seed: _append_entry(
                    seed,
                    {"pubkey": "pk2", "asset": "", "amount": seed[0]["amount"]},
                ),
            ),
            Mutation(
                "second_entry_negative_amount",
                lambda seed: _append_entry(
                    seed,
                    {"pubkey": "pk2", "asset": "asset2", "amount": -1},
                ),
            ),
            Mutation("whole_object", lambda _seed: {"pubkey": "pk1"}),
            Mutation("entry_not_object", lambda _seed: [1]),
        ),
    ),
    ParserTarget(
        name="lp_balances",
        parser=api_server._parse_lp_balances_payload,
        trace_files=(_parser_file(api_server._parse_lp_balances_payload),),
        valid_seed=[{"pubkey": "pk1", "pool_id": "pool1", "amount": 7}],
        mutations=(
            Mutation(
                "empty_pubkey",
                lambda seed: [{"pubkey": "", "pool_id": seed[0]["pool_id"], "amount": seed[0]["amount"]}],
            ),
            Mutation(
                "empty_pool_id",
                lambda seed: [{"pubkey": seed[0]["pubkey"], "pool_id": "", "amount": seed[0]["amount"]}],
            ),
            Mutation(
                "negative_amount",
                lambda seed: [{"pubkey": seed[0]["pubkey"], "pool_id": seed[0]["pool_id"], "amount": -1}],
            ),
            Mutation("duplicate_entry", lambda seed: _append_entry(seed, copy.deepcopy(seed[0]))),
            Mutation(
                "second_entry_bad_pool_id",
                lambda seed: _append_entry(
                    seed,
                    {"pubkey": "pk2", "pool_id": "", "amount": seed[0]["amount"]},
                ),
            ),
            Mutation(
                "second_entry_negative_amount",
                lambda seed: _append_entry(
                    seed,
                    {"pubkey": "pk2", "pool_id": "pool2", "amount": -1},
                ),
            ),
            Mutation("whole_none", lambda _seed: None),
            Mutation("whole_object", lambda _seed: {"pool_id": "pool1"}),
            Mutation("entry_not_object", lambda _seed: [1]),
        ),
    ),
    ParserTarget(
        name="feature_extension_inputs",
        parser=api_server._parse_settlement_feature_extension_inputs_payload,
        trace_files=(
            _parser_file(api_server._parse_settlement_feature_extension_inputs_payload),
            FEATURE_EXTENSION_FILE,
        ),
        valid_seed=_valid_feature_extension_inputs(),
        mutations=(
            Mutation("missing_first_field", lambda seed: _drop_key(seed, "trade_amount")),
            Mutation("missing_middle_field", lambda seed: _drop_key(seed, "supply_after")),
            Mutation("missing_later_field", lambda seed: _drop_key(seed, "weight_claimed")),
            Mutation("u16_overflow", lambda seed: _set_key(seed, "trade_amount", 0x10000)),
            Mutation("late_u16_overflow", lambda seed: _set_key(seed, "weighted_stake", 0x10000)),
            Mutation("u32_overflow", lambda seed: _set_key(seed, "supply_before", 0x1_0000_0000)),
            Mutation("late_u32_overflow", lambda seed: _set_key(seed, "supply_floor", 0x1_0000_0000)),
            Mutation("bool_field", lambda seed: _set_key(seed, "weight_t1", True)),
            Mutation("string_field", lambda seed: _set_key(seed, "supply_after", "not-int")),
            Mutation("whole_list", lambda _seed: []),
        ),
    ),
)


TARGET_INDEX = {target.name: target for target in TARGETS}


def _hash_path(lines: Sequence[str]) -> str:
    digest = hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()
    return digest[:16]


def _clone_payload(payload: object) -> object:
    return copy.deepcopy(payload)


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


def _payload_expandable(target: ParserTarget, payload: object) -> bool:
    if target.name == "price_history":
        return isinstance(payload, list) and len(payload) == 3
    if target.name in {"settlement_proof_flags", "feature_extension_inputs"}:
        return isinstance(payload, dict)
    if target.name in {"balance_table", "lp_balances"}:
        return isinstance(payload, list)
    return False


def _line_path_signature(*, parser: ParserFn, payload: object, trace_files: Sequence[Path]) -> tuple[str, str, int]:
    trace_names = {str(path.resolve()) for path in trace_files}
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
        try:
            parser(payload)
            outcome = "ok"
        except Exception as exc:  # pragma: no cover - exercised via callers
            outcome = f"{type(exc).__name__}:{exc}"
    finally:
        sys.settrace(previous)

    return outcome, _hash_path(lines), len(lines)


def explore_target(name: str, *, max_depth: int = 2, max_frontier: int = 256) -> BoundaryTargetReport:
    target = TARGET_INDEX[name]
    cases: list[BoundaryCase] = []
    seen_pairs: set[tuple[str, str]] = set()
    seen_outcomes: set[str] = set()
    seen_paths: set[str] = set()
    seen_payloads: set[str] = {_payload_signature(target.valid_seed)}
    frontier: list[tuple[int, int, int, str, object]] = [(0, 0, 0, "valid_seed", _clone_payload(target.valid_seed))]
    explored = 0
    schedule_seq = 1

    while frontier and explored < max_frontier:
        _priority, depth, _seq, mutation_name, payload = heapq.heappop(frontier)
        explored += 1
        outcome, path_id, path_length = _line_path_signature(
            parser=target.parser,
            payload=payload,
            trace_files=target.trace_files,
        )
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
                    payload=payload,
                )
            )

        if depth >= max_depth or not _payload_expandable(target, payload):
            continue

        for order, mutation in enumerate(target.mutations):
            try:
                next_payload = mutation.apply(_clone_payload(payload))
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

    cases_sorted = tuple(
        sorted(cases, key=lambda case: (case.outcome_label, case.depth, case.mutation, case.path_id))
    )
    return BoundaryTargetReport(
        target=name,
        total_cases=len(cases_sorted),
        unique_outcome_count=len(seen_outcomes),
        unique_path_count=len(seen_paths),
        cases=cases_sorted,
    )


def explore_all_targets(*, max_depth: int = 2, max_frontier: int = 256) -> tuple[BoundaryTargetReport, ...]:
    return tuple(explore_target(target.name, max_depth=max_depth, max_frontier=max_frontier) for target in TARGETS)


def _reports_to_jsonable(reports: Sequence[BoundaryTargetReport]) -> dict[str, Any]:
    return {
        "schema": "zenodex/api-server-boundary-concolic/v1",
        "reports": [asdict(report) for report in reports],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Deterministic boundary-path explorer for api_server parser helpers.")
    parser.add_argument(
        "--target",
        default="all",
        choices=("all",) + tuple(sorted(TARGET_INDEX)),
        help="Target parser helper to explore.",
    )
    parser.add_argument(
        "--format",
        default="json",
        choices=("json", "text"),
        help="Output format.",
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
        print(json.dumps(_reports_to_jsonable(reports), indent=2, sort_keys=True))
        return 0

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
