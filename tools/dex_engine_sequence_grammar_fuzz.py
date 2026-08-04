from __future__ import annotations

"""
Deterministic action-grammar explorer for multi-step `src.integration.dex_engine`.

This is a bounded, replayable stateful explorer over small sequences of
`apply_ops(...)` calls. It targets real integration-state trajectories where the
interesting behavior appears only after a prior successful transition:
- nonce replay after a valid state mutation
- duplicate CREATE_POOL after a valid pool creation
- second-step sender binding failures
- malformed second-step ingress after prior success

The explorer records unique `(outcome, path)` pairs by tracing through
`dex_engine.py` and its nearby boundary modules.
"""

import argparse
import copy
import hashlib
import json
import sys
from dataclasses import asdict, dataclass, is_dataclass
from pathlib import Path
from typing import Any, Callable, Sequence

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.state.balances import BalanceTable
from src.state.lp import LPTable


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

SENDER = "0x" + "aa" * 48
OTHER_SENDER = "0x" + "bb" * 48
ASSET_A = "0x" + "11" * 32
ASSET_B = "0x" + "22" * 32
ASSET_C = "0x" + "33" * 32
ASSET_D = "0x" + "44" * 32


def _intent_id(byte: str) -> str:
    return "0x" + byte * 32


def _create_pool_ops(*, intent_id: str, sender: str, asset0: str, asset1: str, nonce: int) -> dict[str, Any]:
    return {
        "2": [
            {
                "module": "TauSwap",
                "version": "0.1",
                "kind": "CREATE_POOL",
                "intent_id": intent_id,
                "sender_pubkey": sender,
                "deadline": 9999999999,
                "nonce": nonce,
                "asset0": min(asset0, asset1),
                "asset1": max(asset0, asset1),
                "fee_bps": 30,
                "amount0": 1000,
                "amount1": 2000,
                "created_at": 1,
            }
        ]
    }


def _empty_state_with_assets(assets: Sequence[str], *, amount: int = 10_000) -> DexState:
    balances = BalanceTable()
    for asset in assets:
        balances.set(SENDER, asset, amount)
    return DexState(balances=balances, pools={}, lp_balances=LPTable())


def _hash_path(lines: Sequence[str]) -> str:
    return hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()[:16]


def _stable_jsonable(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if is_dataclass(value):
        from dataclasses import asdict as dc_asdict

        return _stable_jsonable(dc_asdict(value))
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
    trace_label_by_code: dict[object, str | None] = {}
    lines: list[str] = []
    last_loc: str | None = None

    def tracer(frame, event, arg):  # type: ignore[no-untyped-def]
        nonlocal last_loc
        code = frame.f_code
        if code not in trace_label_by_code:
            filename = str(Path(code.co_filename).resolve())
            trace_label_by_code[code] = Path(filename).name if filename in trace_names else None
        trace_label = trace_label_by_code[code]
        if trace_label is None:
            return None
        if event == "line":
            loc = f"{trace_label}:{frame.f_lineno}"
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
    initial_tag = payload.get("initial")
    steps = payload.get("steps")
    if not isinstance(initial_tag, str):
        raise TypeError("initial must be a string")
    if not isinstance(steps, list):
        raise TypeError("steps must be a list")

    if initial_tag == "ab":
        state = _empty_state_with_assets((ASSET_A, ASSET_B))
    elif initial_tag == "abcd":
        state = _empty_state_with_assets((ASSET_A, ASSET_B, ASSET_C, ASSET_D))
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


def _cases() -> tuple[GrammarCase, ...]:
    step_ab_1 = {"operations": _create_pool_ops(intent_id=_intent_id("01"), sender=SENDER, asset0=ASSET_A, asset1=ASSET_B, nonce=1)}
    step_ab_1_replay = {"operations": _create_pool_ops(intent_id=_intent_id("01"), sender=SENDER, asset0=ASSET_A, asset1=ASSET_B, nonce=1)}
    step_ab_2 = {"operations": _create_pool_ops(intent_id=_intent_id("02"), sender=SENDER, asset0=ASSET_A, asset1=ASSET_B, nonce=2)}
    step_cd_2 = {"operations": _create_pool_ops(intent_id=_intent_id("03"), sender=SENDER, asset0=ASSET_C, asset1=ASSET_D, nonce=2)}
    step_cd_2_wrong_sender = {
        "operations": _create_pool_ops(intent_id=_intent_id("03"), sender=SENDER, asset0=ASSET_C, asset1=ASSET_D, nonce=2),
        "tx_sender_pubkey": OTHER_SENDER,
    }
    step_bad_intents = {"operations": {"2": "oops"}}
    step_bad_settlement = {"operations": {"3": []}}
    step_noop = {"operations": {}}

    return (
        GrammarCase("DexSeq->SingleValidPool", {"initial": "ab", "steps": [copy.deepcopy(step_ab_1)]}),
        GrammarCase("DexSeq->NoOpThenValidPool", {"initial": "ab", "steps": [copy.deepcopy(step_noop), copy.deepcopy(step_ab_1)]}),
        GrammarCase("DexSeq->ReplayPoolAfterSuccess", {"initial": "ab", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_ab_1_replay)]}),
        GrammarCase(
            "DexSeq->ReplayPoolAfterSuccessWithDeadTail",
            {
                "initial": "ab",
                "steps": [
                    copy.deepcopy(step_ab_1),
                    copy.deepcopy(step_ab_1_replay),
                    copy.deepcopy(step_cd_2),
                ],
            },
        ),
        GrammarCase("DexSeq->DuplicatePoolFreshNonce", {"initial": "ab", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_ab_2)]}),
        GrammarCase("DexSeq->FreshNonceSecondPool", {"initial": "abcd", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_cd_2)]}),
        GrammarCase("DexSeq->WrongSenderSecondStep", {"initial": "abcd", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_cd_2_wrong_sender)]}),
        GrammarCase("DexSeq->MalformedSecondStep", {"initial": "ab", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_bad_intents)]}),
        GrammarCase("DexSeq->BadSettlementTypeSecondStep", {"initial": "ab", "steps": [copy.deepcopy(step_ab_1), copy.deepcopy(step_bad_settlement)]}),
    )


TARGETS: tuple[GrammarTarget, ...] = (
    GrammarTarget(
        name="dex_engine_sequence",
        runner=_sequence_outcome,
        trace_files=(DEX_ENGINE_FILE, OPERATIONS_FILE, NONCES_FILE, BATCH_CLEARING_FILE),
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
            "schema": "zenodex/dex-engine-sequence-minimized-witness/v1",
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
        "schema": "zenodex/dex-engine-sequence-grammar-fuzz/v1",
        "reports": [asdict(report) for report in reports],
    }
    json.dump(payload, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
