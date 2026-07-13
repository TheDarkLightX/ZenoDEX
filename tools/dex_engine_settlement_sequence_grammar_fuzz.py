from __future__ import annotations

"""
Deterministic action-grammar explorer for stateful settlement behavior in `dex_engine`.

This is a bounded, replayable explorer over short `apply_ops(...)` sequences where
the interesting branch appears only after a prior successful transition:
- provided settlements that remain valid on an unchanged surface
- provided settlements that go stale after pool mutation
- explicit settlement failures after a prior success
"""

import argparse
import copy
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Sequence

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import create_settlement_operation, parse_intents
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id

RunnerFn = Callable[[object], str]


@dataclass(frozen=True)
class GrammarCase:
    derivation: str
    payload: object


@dataclass(frozen=True)
class BoundaryCase:
    derivation: str
    outcome_label: str
    path_id: str
    path_length: int


@dataclass(frozen=True)
class GrammarTargetReport:
    target: str
    total_cases: int
    unique_outcome_count: int
    unique_path_count: int
    cases: tuple[BoundaryCase, ...]


@dataclass(frozen=True)
class MinimizedWitness:
    target: str
    derivation: str
    outcome_label: str
    path_id: str
    path_length: int
    original_size: int
    minimized_size: int
    payload: object


@dataclass(frozen=True)
class GrammarTarget:
    name: str
    runner: RunnerFn
    trace_files: tuple[Path, ...]
    cases: tuple[GrammarCase, ...]


DEX_ENGINE_FILE = (ROOT_DIR / "src/integration/dex_engine.py").resolve()
OPERATIONS_FILE = (ROOT_DIR / "src/integration/operations.py").resolve()
NONCES_FILE = (ROOT_DIR / "src/state/nonces.py").resolve()
BATCH_CLEARING_FILE = (ROOT_DIR / "src/core/batch_clearing.py").resolve()
SETTLEMENT_NF_FILE = (ROOT_DIR / "src/core/settlement_normal_form.py").resolve()

SENDER = "0x" + "aa" * 48
ASSET_A = "0x" + "11" * 32
ASSET_B = "0x" + "22" * 32
ASSET_C = "0x" + "33" * 32
ASSET_D = "0x" + "44" * 32
POOL_AB = compute_pool_id(ASSET_A, ASSET_B, 30)
POOL_CD = compute_pool_id(ASSET_C, ASSET_D, 30)


def _pool(*, pool_id: str, asset0: str, asset1: str) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=5_000,
        reserve1=5_000,
        fee_bps=30,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag="CPMM",
        curve_params="",
    )


def _initial_state() -> DexState:
    balances = BalanceTable()
    balances.set(SENDER, ASSET_A, 10_000)
    balances.set(SENDER, ASSET_B, 0)
    balances.set(SENDER, ASSET_C, 10_000)
    balances.set(SENDER, ASSET_D, 0)
    return DexState(
        balances=balances,
        pools={
            POOL_AB: _pool(pool_id=POOL_AB, asset0=ASSET_A, asset1=ASSET_B),
            POOL_CD: _pool(pool_id=POOL_CD, asset0=ASSET_C, asset1=ASSET_D),
        },
        lp_balances=LPTable(),
    )


def _swap_intent_dict(*, intent_id_byte: str, pool_id: str, asset_in: str, asset_out: str, amount_in: int, nonce: int) -> dict[str, Any]:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + intent_id_byte * 32,
        "sender_pubkey": SENDER,
        "deadline": 9_999_999_999,
        "nonce": nonce,
        "pool_id": pool_id,
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": amount_in,
        "min_amount_out": 1,
    }


def _ops_with_optional_settlement(
    *,
    runtime_state: DexState,
    settlement_state: DexState | None,
    intent_id_byte: str,
    pool_id: str,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    nonce: int,
    include_settlement: bool,
) -> dict[str, Any]:
    intent_dict = _swap_intent_dict(
        intent_id_byte=intent_id_byte,
        pool_id=pool_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        nonce=nonce,
    )
    ops: dict[str, Any] = {"2": [copy.deepcopy(intent_dict)]}
    if include_settlement:
        source_state = settlement_state if settlement_state is not None else runtime_state
        intents = parse_intents({"2": [copy.deepcopy(intent_dict)]})
        settlement = compute_settlement(
            intents=intents,
            pools=source_state.pools,
            balances=source_state.balances,
            lp_balances=source_state.lp_balances,
        )
        ops["3"] = create_settlement_operation(settlement)["3"]
    return ops


def _apply_once(state: DexState, operations: dict[str, Any], *, allow_missing_settlement: bool, require_settlement_match: bool = True) -> DexState:
    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=allow_missing_settlement,
            require_settlement_match=require_settlement_match,
            require_intent_signatures=False,
        ),
        state=state,
        operations=operations,
        block_timestamp=0,
        tx_sender_pubkey=SENDER,
    )
    if not res.ok or res.state is None:  # pragma: no cover
        raise RuntimeError(f"failed to build settlement sequence fixture: {res.error}")
    return res.state


def _hash_path(lines: Sequence[str]) -> str:
    return hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()[:16]


def _stable_jsonable(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, dict):
        return {str(k): _stable_jsonable(v) for k, v in sorted(value.items(), key=lambda item: str(item[0]))}
    if isinstance(value, list):
        return [_stable_jsonable(v) for v in value]
    if isinstance(value, tuple):
        return [_stable_jsonable(v) for v in value]
    return repr(value)


def _payload_fingerprint(payload: object) -> str:
    return json.dumps(_stable_jsonable(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _trace_outcome(*, runner: RunnerFn, payload: object, trace_files: Sequence[Path]) -> tuple[str, str, int]:
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
            outcome = runner(payload)
        except Exception as exc:  # pragma: no cover
            outcome = f"{type(exc).__name__}:{exc}"
    finally:
        sys.settrace(previous)
    return outcome, _hash_path(lines), len(lines)


def _format_lasts(state: DexState) -> str:
    items = sorted(state.nonces.get_all().items())
    if not items:
        return "empty"
    return "|".join(f"{sender[-8:]}={int(last)}" for sender, last in items)


def _sequence_outcome(payload: object) -> str:
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    steps = payload.get("steps")
    if not isinstance(steps, list):
        raise TypeError("steps must be a list")

    state = _initial_state()
    for idx, step in enumerate(steps):
        if not isinstance(step, dict):
            raise TypeError(f"step {idx} must be a dict")
        operations = step.get("operations")
        if not isinstance(operations, dict):
            raise TypeError(f"step {idx}.operations must be a dict")
        config_overrides = step.get("config", {})
        if not isinstance(config_overrides, dict):
            raise TypeError(f"step {idx}.config must be a dict")
        tx_sender = step.get("tx_sender_pubkey", SENDER)
        if tx_sender is not None and not isinstance(tx_sender, str):
            raise TypeError(f"step {idx}.tx_sender_pubkey must be a string or None")
        config = DexEngineConfig(
            allow_missing_settlement=bool(config_overrides.get("allow_missing_settlement", True)),
            require_settlement_match=bool(config_overrides.get("require_settlement_match", True)),
            require_intent_signatures=False,
            max_settlement_fills=int(config_overrides.get("max_settlement_fills", 512)),
        )
        result = apply_ops(
            config=config,
            state=state,
            operations=operations,
            block_timestamp=0,
            tx_sender_pubkey=tx_sender,
        )
        if not result.ok:
            return f"reject:step={idx}:{result.error}"
        assert result.state is not None
        state = result.state
    return f"ok:pools={len(state.pools)}:nonces={_format_lasts(state)}"


def _cases() -> tuple[GrammarCase, ...]:
    initial = _initial_state()
    warmup_ab = _ops_with_optional_settlement(
        runtime_state=initial,
        settlement_state=None,
        intent_id_byte="01",
        pool_id=POOL_AB,
        asset_in=ASSET_A,
        asset_out=ASSET_B,
        amount_in=100,
        nonce=1,
        include_settlement=False,
    )
    post_warmup = _apply_once(copy.deepcopy(initial), copy.deepcopy(warmup_ab), allow_missing_settlement=True)

    valid_ab_with_settlement = _ops_with_optional_settlement(
        runtime_state=initial,
        settlement_state=initial,
        intent_id_byte="02",
        pool_id=POOL_AB,
        asset_in=ASSET_A,
        asset_out=ASSET_B,
        amount_in=100,
        nonce=1,
        include_settlement=True,
    )
    stateful_valid_ab = _ops_with_optional_settlement(
        runtime_state=post_warmup,
        settlement_state=post_warmup,
        intent_id_byte="03",
        pool_id=POOL_AB,
        asset_in=ASSET_A,
        asset_out=ASSET_B,
        amount_in=100,
        nonce=2,
        include_settlement=True,
    )
    stale_ab = _ops_with_optional_settlement(
        runtime_state=post_warmup,
        settlement_state=initial,
        intent_id_byte="03",
        pool_id=POOL_AB,
        asset_in=ASSET_A,
        asset_out=ASSET_B,
        amount_in=100,
        nonce=2,
        include_settlement=True,
    )
    missing_settlement_ab = _ops_with_optional_settlement(
        runtime_state=post_warmup,
        settlement_state=None,
        intent_id_byte="03",
        pool_id=POOL_AB,
        asset_in=ASSET_A,
        asset_out=ASSET_B,
        amount_in=100,
        nonce=2,
        include_settlement=False,
    )
    settlement_only = create_settlement_operation(
        compute_settlement(
            intents=parse_intents({"2": [copy.deepcopy(_swap_intent_dict(intent_id_byte="05", pool_id=POOL_CD, asset_in=ASSET_C, asset_out=ASSET_D, amount_in=120, nonce=2))]}),
            pools=post_warmup.pools,
            balances=post_warmup.balances,
            lp_balances=post_warmup.lp_balances,
        )
    )
    too_many_fills = {
        "3": {
            "module": "TauSwap",
            "version": "0.1",
            "included_intents": [],
            "fills": [{}, {}],
            "balance_deltas": [],
            "reserve_deltas": [],
            "lp_deltas": [],
        }
    }

    return (
        GrammarCase("SettlementSeq->SingleProvidedAb", {"steps": [{"operations": copy.deepcopy(valid_ab_with_settlement), "config": {"allow_missing_settlement": False}}]}),
        GrammarCase(
            "SettlementSeq->WarmupThenStatefulProvidedAb",
            {
                "steps": [
                    {"operations": copy.deepcopy(warmup_ab)},
                    {"operations": copy.deepcopy(stateful_valid_ab), "config": {"allow_missing_settlement": False}},
                ]
            },
        ),
        GrammarCase(
            "SettlementSeq->WarmupThenStaleProvidedAb",
            {
                "steps": [
                    {"operations": copy.deepcopy(warmup_ab)},
                    {"operations": copy.deepcopy(stale_ab), "config": {"allow_missing_settlement": False}},
                ]
            },
        ),
        GrammarCase(
            "SettlementSeq->WarmupThenStaleProvidedAbWithDeadTail",
            {
                "steps": [
                    {"operations": copy.deepcopy(warmup_ab)},
                    {"operations": copy.deepcopy(stale_ab), "config": {"allow_missing_settlement": False}},
                    {"operations": copy.deepcopy(stateful_valid_ab), "config": {"allow_missing_settlement": False}},
                ]
            },
        ),
        GrammarCase(
            "SettlementSeq->WarmupThenMissingSettlementRequired",
            {
                "steps": [
                    {"operations": copy.deepcopy(warmup_ab)},
                    {"operations": copy.deepcopy(missing_settlement_ab), "config": {"allow_missing_settlement": False}},
                ]
            },
        ),
        GrammarCase(
            "SettlementSeq->WarmupThenSettlementWithoutIntents",
            {
                "steps": [
                    {"operations": copy.deepcopy(warmup_ab)},
                    {"operations": copy.deepcopy(settlement_only)},
                ]
            },
        ),
        GrammarCase(
            "SettlementSeq->WarmupThenTooManySettlementFills",
            {
                "steps": [
                    {"operations": copy.deepcopy(warmup_ab)},
                    {"operations": copy.deepcopy(too_many_fills), "config": {"max_settlement_fills": 1}},
                ]
            },
        ),
    )


TARGETS: tuple[GrammarTarget, ...] = (
    GrammarTarget(
        name="dex_engine_settlement_sequence",
        runner=_sequence_outcome,
        trace_files=(DEX_ENGINE_FILE, OPERATIONS_FILE, NONCES_FILE, BATCH_CLEARING_FILE, SETTLEMENT_NF_FILE),
        cases=_cases(),
    ),
)

TARGET_BY_NAME = {target.name: target for target in TARGETS}


def _payload_size(payload: object) -> int:
    return len(_payload_fingerprint(payload))


def _find_case(target_name: str, derivation: str) -> GrammarCase:
    if target_name not in TARGET_BY_NAME:
        raise KeyError(f"unknown target: {target_name}")
    target = TARGET_BY_NAME[target_name]
    for case in target.cases:
        if case.derivation == derivation:
            return case
    raise KeyError(f"unknown derivation for {target_name}: {derivation}")


def _minimization_candidates(payload: object) -> tuple[object, ...]:
    if not isinstance(payload, dict):
        return ()
    steps = payload.get("steps")
    if not isinstance(steps, list):
        return ()

    candidates: list[object] = []
    if len(steps) > 1:
        for new_len in range(len(steps) - 1, 0, -1):
            shortened = copy.deepcopy(payload)
            shortened["steps"] = shortened["steps"][:new_len]
            candidates.append(shortened)
    return tuple(candidates)


def minimize_case(target_name: str, derivation: str, *, max_rounds: int = 16) -> MinimizedWitness:
    target = TARGET_BY_NAME[target_name]
    case = _find_case(target_name, derivation)
    current = copy.deepcopy(case.payload)
    outcome_label, path_id, path_length = _trace_outcome(
        runner=target.runner,
        payload=current,
        trace_files=target.trace_files,
    )
    original_size = _payload_size(current)
    current_size = original_size

    rounds = 0
    while rounds < max_rounds:
        rounds += 1
        best_payload: object | None = None
        best_size = current_size
        best_path_length = path_length
        for candidate in _minimization_candidates(current):
            candidate_size = _payload_size(candidate)
            if candidate_size >= best_size:
                continue
            cand_outcome, cand_path_id, cand_path_length = _trace_outcome(
                runner=target.runner,
                payload=candidate,
                trace_files=target.trace_files,
            )
            if cand_outcome != outcome_label or cand_path_id != path_id:
                continue
            best_payload = candidate
            best_size = candidate_size
            best_path_length = cand_path_length
        if best_payload is None:
            break
        current = best_payload
        current_size = best_size
        path_length = best_path_length

    return MinimizedWitness(
        target=target_name,
        derivation=derivation,
        outcome_label=outcome_label,
        path_id=path_id,
        path_length=path_length,
        original_size=original_size,
        minimized_size=current_size,
        payload=current,
    )


def explore_target(name: str, *, max_cases: int = 64) -> GrammarTargetReport:
    if name not in TARGET_BY_NAME:
        raise KeyError(f"unknown target: {name}")
    target = TARGET_BY_NAME[name]
    seen_payloads: set[str] = set()
    seen_pairs: set[tuple[str, str]] = set()
    accepted: list[BoundaryCase] = []

    for case in target.cases:
        fp = _payload_fingerprint(case.payload)
        if fp in seen_payloads:
            continue
        seen_payloads.add(fp)
        outcome_label, path_id, path_length = _trace_outcome(
            runner=target.runner,
            payload=case.payload,
            trace_files=target.trace_files,
        )
        pair = (outcome_label, path_id)
        if pair in seen_pairs:
            continue
        seen_pairs.add(pair)
        accepted.append(
            BoundaryCase(
                derivation=case.derivation,
                outcome_label=outcome_label,
                path_id=path_id,
                path_length=path_length,
            )
        )
        if len(accepted) >= max_cases:
            break

    cases = tuple(sorted(accepted, key=lambda item: (item.outcome_label, item.path_id, item.derivation)))
    return GrammarTargetReport(
        target=target.name,
        total_cases=len(cases),
        unique_outcome_count=len({case.outcome_label for case in cases}),
        unique_path_count=len({case.path_id for case in cases}),
        cases=cases,
    )


def explore_all_targets() -> tuple[GrammarTargetReport, ...]:
    return tuple(explore_target(target.name) for target in TARGETS)


def _print_text(report: GrammarTargetReport) -> None:
    print(f"[{report.target}] cases={report.total_cases} outcomes={report.unique_outcome_count} paths={report.unique_path_count}")
    for case in report.cases:
        print(f"- {case.derivation}: {case.outcome_label} ({case.path_id}, len={case.path_length})")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", choices=sorted(TARGET_BY_NAME), help="Explore only one target")
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--minimize-derivation", help="minimize one named derivation while preserving its outcome/path pair")
    args = parser.parse_args(argv)

    if args.minimize_derivation:
        if not args.target:
            parser.error("--minimize-derivation requires --target")
        witness = minimize_case(args.target, args.minimize_derivation)
        if args.format == "text":
            print(f"[{witness.target}] {witness.derivation}")
            print(f"outcome={witness.outcome_label} path={witness.path_id} len={witness.path_length}")
            print(f"size={witness.original_size}->{witness.minimized_size}")
            print(json.dumps(_stable_jsonable(witness.payload), indent=2, sort_keys=True))
            return 0
        payload = {
            "schema": "zenodex/dex-engine-settlement-sequence-minimized-witness/v1",
            "witness": {
                **asdict(witness),
                "payload": _stable_jsonable(witness.payload),
            },
        }
        json.dump(payload, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
        return 0

    reports = (explore_target(args.target),) if args.target else explore_all_targets()
    if args.format == "text":
        for report in reports:
            _print_text(report)
        return 0

    payload = {
        "schema": "zenodex/dex-engine-settlement-sequence-grammar-fuzz/v1",
        "reports": [asdict(report) for report in reports],
    }
    json.dump(payload, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
