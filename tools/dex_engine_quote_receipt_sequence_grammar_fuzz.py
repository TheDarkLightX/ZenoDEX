"""
Deterministic action-grammar explorer for stateful quote-receipt behavior in `dex_engine`.

This is a bounded, replayable explorer over short `apply_ops(...)` sequences where
the interesting branch only appears after a prior successful transition:
- a previously valid quote receipt becomes stale after pool mutation
- quote receipt hash and witness requirements fire after earlier success
- split quote-receipt leg binding and coverage checks fire after an unrelated success
"""

from __future__ import annotations

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

from src.agents.intent_signer import (  # noqa: E402
    create_swap_intent_from_quote_receipt,
    create_swap_intents_from_quote_receipt,
)
from src.core.dex import DexState  # noqa: E402
from src.core.quote_receipts import make_route_quote_receipt  # noqa: E402
from src.core.routing import best_route_exact_in_2hop  # noqa: E402
from src.integration.dex_engine import DexEngineConfig, apply_ops  # noqa: E402
from src.integration.operations import (  # noqa: E402
    SignedIntentEnvelope,
    create_signed_intent_operation,
)
from src.state.balances import BalanceTable  # noqa: E402
from src.state.lp import LPTable  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402

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
QUOTE_RECEIPTS_FILE = (ROOT_DIR / "src/core/quote_receipts.py").resolve()
NONCES_FILE = (ROOT_DIR / "src/state/nonces.py").resolve()
BATCH_CLEARING_FILE = (ROOT_DIR / "src/core/batch_clearing.py").resolve()

SENDER = "0x" + "aa" * 48
ASSET_A = "A"
ASSET_B = "B"
ASSET_C = "C"
ASSET_D = "D"


def _pool(*, pool_id: str, asset0: str, asset1: str, reserve0: int, reserve1: int, fee_bps: int = 10) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


DIRECT_POOLS = {
    "p_ab": _pool(pool_id="p_ab", asset0=ASSET_A, asset1=ASSET_B, reserve0=1_000, reserve1=2_000),
    "p_cd": _pool(pool_id="p_cd", asset0=ASSET_C, asset1=ASSET_D, reserve0=1_500, reserve1=3_000),
}

SPLIT_POOLS = {
    "p1": _pool(pool_id="p1", asset0=ASSET_A, asset1=ASSET_B, reserve0=1_000, reserve1=1_000, fee_bps=0),
    "p2": _pool(pool_id="p2", asset0=ASSET_A, asset1=ASSET_B, reserve0=1_000, reserve1=1_000, fee_bps=0),
    "p_cd": _pool(pool_id="p_cd", asset0=ASSET_C, asset1=ASSET_D, reserve0=1_500, reserve1=3_000),
}


def _direct_state() -> DexState:
    balances = BalanceTable()
    balances.set(SENDER, ASSET_A, 10_000)
    balances.set(SENDER, ASSET_B, 0)
    balances.set(SENDER, ASSET_C, 10_000)
    balances.set(SENDER, ASSET_D, 0)
    return DexState(balances=balances, pools=copy.deepcopy(DIRECT_POOLS), lp_balances=LPTable())


def _split_state() -> DexState:
    balances = BalanceTable()
    balances.set(SENDER, ASSET_A, 10_000)
    balances.set(SENDER, ASSET_B, 0)
    balances.set(SENDER, ASSET_C, 10_000)
    balances.set(SENDER, ASSET_D, 0)
    return DexState(balances=balances, pools=copy.deepcopy(SPLIT_POOLS), lp_balances=LPTable())


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

    def tracer(frame, event, arg):
        nonlocal last_loc
        filename = str(Path(frame.f_code.co_filename).resolve())
        if event == "call":
            return tracer if filename in trace_names else None
        if event == "line":
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


def _make_direct_ops(
    *,
    pools: dict[str, PoolState],
    pool_id: str,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    nonce: int,
    attach_witness: bool = True,
    hash_override: str | None = None,
) -> dict[str, Any]:
    route = best_route_exact_in_2hop(
        pools_by_id={pool_id: copy.deepcopy(pools[pool_id])},
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
    )
    assert route is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=route, pools_by_id={pool_id: copy.deepcopy(pools[pool_id])})
    intent = create_swap_intent_from_quote_receipt(
        receipt=receipt,
        pools_by_id={pool_id: copy.deepcopy(pools[pool_id])},
        sender_pubkey=SENDER,
        deadline=9_999_999_999,
        slippage_bps=0,
    )
    intent = intent.with_field("nonce", nonce)
    env = SignedIntentEnvelope(intent=intent, quote_receipt=receipt if attach_witness else None)
    ops = create_signed_intent_operation([env])
    if hash_override is not None:
        ops["2"][0]["quote_receipt_hash"] = hash_override
    return ops


def _make_split_ops(
    *,
    nonce_start: int,
    duplicate_leg: bool = False,
    incomplete: bool = False,
    swapped_leg_indices: bool = False,
) -> dict[str, Any]:
    route = best_route_exact_in_2hop(
        pools_by_id={key: copy.deepcopy(value) for key, value in SPLIT_POOLS.items() if key in {"p1", "p2"}},
        asset_in=ASSET_A,
        asset_out=ASSET_B,
        amount_in=600,
    )
    assert route is not None
    receipt = make_route_quote_receipt(
        kind="exact_in",
        quote=route,
        pools_by_id={key: copy.deepcopy(value) for key, value in SPLIT_POOLS.items() if key in {"p1", "p2"}},
    )
    intents = create_swap_intents_from_quote_receipt(
        receipt=receipt,
        pools_by_id={key: copy.deepcopy(value) for key, value in SPLIT_POOLS.items() if key in {"p1", "p2"}},
        sender_pubkey=SENDER,
        deadline=9_999_999_999,
        slippage_bps=0,
        nonce_start=nonce_start,
    )
    envs = [SignedIntentEnvelope(intent=intent, quote_receipt=receipt) for intent in intents]
    if incomplete:
        envs = envs[:1]
    ops = create_signed_intent_operation(envs)
    if swapped_leg_indices and len(ops["2"]) >= 2:
        first = ops["2"][0]["quote_receipt_leg_index"]
        second = ops["2"][1]["quote_receipt_leg_index"]
        ops["2"][0]["quote_receipt_leg_index"] = second
        ops["2"][1]["quote_receipt_leg_index"] = first
    if duplicate_leg:
        duplicate = dict(ops["2"][0])
        duplicate["intent_id"] = "0x" + "de" * 32
        duplicate["nonce"] = 99
        ops["2"].append(duplicate)
    return ops


def _sequence_outcome(payload: object) -> str:
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    initial_tag = payload.get("initial")
    steps = payload.get("steps")
    if not isinstance(initial_tag, str):
        raise TypeError("initial must be a string")
    if not isinstance(steps, list):
        raise TypeError("steps must be a list")

    if initial_tag == "direct":
        state = _direct_state()
    elif initial_tag == "split":
        state = _split_state()
    else:
        raise ValueError(f"unknown initial state: {initial_tag}")

    config = DexEngineConfig(allow_missing_settlement=True, require_intent_signatures=False)
    for idx, step in enumerate(steps):
        if not isinstance(step, dict):
            raise TypeError(f"step {idx} must be a dict")
        operations = step.get("operations")
        if not isinstance(operations, dict):
            raise TypeError(f"step {idx}.operations must be a dict")
        tx_sender = step.get("tx_sender_pubkey", SENDER)
        if tx_sender is not None and not isinstance(tx_sender, str):
            raise TypeError(f"step {idx}.tx_sender_pubkey must be a string or None")
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


def _direct_cases() -> tuple[GrammarCase, ...]:
    step_ab_1 = {"operations": _make_direct_ops(pools=DIRECT_POOLS, pool_id="p_ab", asset_in=ASSET_A, asset_out=ASSET_B, amount_in=123, nonce=1)}
    step_cd_2 = {"operations": _make_direct_ops(pools=DIRECT_POOLS, pool_id="p_cd", asset_in=ASSET_C, asset_out=ASSET_D, amount_in=111, nonce=2)}
    step_ab_stale_2 = {"operations": _make_direct_ops(pools=DIRECT_POOLS, pool_id="p_ab", asset_in=ASSET_A, asset_out=ASSET_B, amount_in=123, nonce=2)}
    step_cd_hash_mismatch_2 = {
        "operations": _make_direct_ops(
            pools=DIRECT_POOLS,
            pool_id="p_cd",
            asset_in=ASSET_C,
            asset_out=ASSET_D,
            amount_in=111,
            nonce=2,
            hash_override="0xdeadbeef",
        )
    }
    step_cd_missing_witness_2 = {
        "operations": _make_direct_ops(
            pools=DIRECT_POOLS,
            pool_id="p_cd",
            asset_in=ASSET_C,
            asset_out=ASSET_D,
            amount_in=111,
            nonce=2,
            attach_witness=False,
        )
    }
    return (
        GrammarCase("DirectSeq->SingleValidAb", {"initial": "direct", "steps": [copy.deepcopy(step_ab_1)]}),
        GrammarCase("DirectSeq->ValidThenIndependentValidCd", {"initial": "direct", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_cd_2)]}),
        GrammarCase("DirectSeq->ValidThenStaleSamePool", {"initial": "direct", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_ab_stale_2)]}),
        GrammarCase(
            "DirectSeq->ValidThenStaleSamePoolWithDeadTail",
            {"initial": "direct", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_ab_stale_2), copy.deepcopy(step_cd_2)]},
        ),
        GrammarCase(
            "DirectSeq->ValidThenIndependentHashMismatch",
            {"initial": "direct", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_cd_hash_mismatch_2)]},
        ),
        GrammarCase(
            "DirectSeq->ValidThenIndependentMissingWitness",
            {"initial": "direct", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_cd_missing_witness_2)]},
        ),
    )


def _split_cases() -> tuple[GrammarCase, ...]:
    warmup_cd_1 = {"operations": _make_direct_ops(pools=SPLIT_POOLS, pool_id="p_cd", asset_in=ASSET_C, asset_out=ASSET_D, amount_in=111, nonce=1)}
    split_ok_2 = {"operations": _make_split_ops(nonce_start=2)}
    split_dup_2 = {"operations": _make_split_ops(nonce_start=2, duplicate_leg=True)}
    split_incomplete_2 = {"operations": _make_split_ops(nonce_start=2, incomplete=True)}
    split_swapped_leg_indices_2 = {"operations": _make_split_ops(nonce_start=2, swapped_leg_indices=True)}
    return (
        GrammarCase("SplitSeq->WarmupThenSplitValid", {"initial": "split", "steps": [copy.deepcopy(warmup_cd_1), copy.deepcopy(split_ok_2)]}),
        GrammarCase(
            "SplitSeq->WarmupThenSplitDuplicateLeg",
            {"initial": "split", "steps": [copy.deepcopy(warmup_cd_1), copy.deepcopy(split_dup_2)]},
        ),
        GrammarCase(
            "SplitSeq->WarmupThenSplitIncompleteCoverage",
            {"initial": "split", "steps": [copy.deepcopy(warmup_cd_1), copy.deepcopy(split_incomplete_2)]},
        ),
        GrammarCase(
            "SplitSeq->WarmupThenSplitSwappedLegIndices",
            {"initial": "split", "steps": [copy.deepcopy(warmup_cd_1), copy.deepcopy(split_swapped_leg_indices_2)]},
        ),
    )


TARGETS: tuple[GrammarTarget, ...] = (
    GrammarTarget(
        name="direct_quote_receipt_sequence",
        runner=_sequence_outcome,
        trace_files=(DEX_ENGINE_FILE, OPERATIONS_FILE, QUOTE_RECEIPTS_FILE, NONCES_FILE, BATCH_CLEARING_FILE),
        cases=_direct_cases(),
    ),
    GrammarTarget(
        name="split_quote_receipt_sequence",
        runner=_sequence_outcome,
        trace_files=(DEX_ENGINE_FILE, OPERATIONS_FILE, QUOTE_RECEIPTS_FILE, NONCES_FILE, BATCH_CLEARING_FILE),
        cases=_split_cases(),
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
            "schema": "zenodex/dex-engine-quote-receipt-sequence-minimized-witness/v1",
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

    reports_payload: dict[str, Any] = {
        "schema": "zenodex/dex-engine-quote-receipt-sequence-grammar-fuzz/v1",
        "reports": [asdict(report) for report in reports],
    }
    json.dump(reports_payload, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
