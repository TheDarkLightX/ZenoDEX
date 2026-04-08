from __future__ import annotations

"""
Deterministic action-grammar explorer for multi-step nonce replay semantics.

This is a bounded, replayable grammar fuzzer over *sequences of nonce batches*.
It targets multi-step replay behavior where the interesting surface is not a
single malformed batch but a trace of state transitions through `src.state.nonces`.
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

from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, copy_nonce_table, validate_and_apply_intent_nonce_batch


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


NONCES_FILE = (ROOT_DIR / "src/state/nonces.py").resolve()
CANONICAL_FILE = (ROOT_DIR / "src/state/canonical.py").resolve()

PK1 = "0x" + "11" * 48
PK1_UPPER = "0x" + ("11" * 48).upper()
PK2 = "0x" + "22" * 48


def _intent(*, sender: str, nonce: int | None, intent_id_byte: str) -> Intent:
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
        intent_id="0x" + intent_id_byte * 32,
        sender_pubkey=sender,
        deadline=1,
        fields=fields,
    )


def _step(intents: list[Intent], *, require_all_nonces: bool) -> dict[str, Any]:
    return {
        "intents": intents,
        "require_all_nonces": bool(require_all_nonces),
    }


def _empty_table() -> NonceTable:
    return NonceTable()


def _table_with_last(pubkey: str, last_nonce: int) -> NonceTable:
    table = NonceTable()
    table.set_last(pubkey, last_nonce)
    return table


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
    if isinstance(value, (list, tuple)):
        return [_stable_jsonable(v) for v in value]
    if isinstance(value, set):
        return sorted(_stable_jsonable(v) for v in value)
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


def _format_lasts(table: NonceTable) -> str:
    items = sorted(table.get_all().items())
    return "|".join(f"{pk[-8:]}={int(last)}" for pk, last in items) if items else "empty"


def _sequence_outcome(payload: object) -> str:
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    initial = payload.get("initial")
    steps = payload.get("steps")
    if not isinstance(initial, NonceTable):
        raise TypeError("initial must be a NonceTable")
    if not isinstance(steps, list):
        raise TypeError("steps must be a list")

    state = copy_nonce_table(initial)
    for idx, step in enumerate(steps):
        if not isinstance(step, dict):
            raise TypeError(f"step {idx} must be a dict")
        intents = step.get("intents")
        require_all_nonces = step.get("require_all_nonces")
        if not isinstance(intents, list):
            raise TypeError(f"step {idx}.intents must be a list")
        if not isinstance(require_all_nonces, bool):
            raise TypeError(f"step {idx}.require_all_nonces must be a bool")
        ok, err, updated = validate_and_apply_intent_nonce_batch(
            nonces=state,
            intents=intents,
            require_all_nonces=require_all_nonces,
        )
        if not ok:
            return f"reject:step={idx}:{err}"
        assert updated is not None
        state = updated
    return f"ok:{_format_lasts(state)}"


def _cases() -> tuple[GrammarCase, ...]:
    cases = [
        GrammarCase(
            "Seq->SingleValidBatch",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1, nonce=1, intent_id_byte="01"), _intent(sender=PK1, nonce=2, intent_id_byte="02")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->TwoContiguousBatches",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1, nonce=1, intent_id_byte="03"), _intent(sender=PK1, nonce=2, intent_id_byte="04")], require_all_nonces=True),
                    _step([_intent(sender=PK1, nonce=3, intent_id_byte="05"), _intent(sender=PK1, nonce=4, intent_id_byte="06")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->CrossBatchReplay",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1, nonce=1, intent_id_byte="07"), _intent(sender=PK1, nonce=2, intent_id_byte="08")], require_all_nonces=True),
                    _step([_intent(sender=PK1, nonce=2, intent_id_byte="09")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->CrossBatchReplayWithDeadTail",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1, nonce=1, intent_id_byte="07"), _intent(sender=PK1, nonce=2, intent_id_byte="08")], require_all_nonces=True),
                    _step([_intent(sender=PK1, nonce=2, intent_id_byte="09")], require_all_nonces=True),
                    _step([_intent(sender=PK2, nonce=1, intent_id_byte="0f")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->CrossBatchGap",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1, nonce=1, intent_id_byte="0a")], require_all_nonces=True),
                    _step([_intent(sender=PK1, nonce=3, intent_id_byte="0b")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->MissingRequiredFirstStep",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1, nonce=None, intent_id_byte="0c")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->MixedPresenceBackwardCompat",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1, nonce=1, intent_id_byte="0d"), _intent(sender=PK2, nonce=None, intent_id_byte="0e")], require_all_nonces=False),
                ],
            },
        ),
        GrammarCase(
            "Seq->CanonicalizedSenderAcrossSteps",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1_UPPER, nonce=1, intent_id_byte="0f")], require_all_nonces=True),
                    _step([_intent(sender=PK1, nonce=2, intent_id_byte="10")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->MultiSenderIndependentProgress",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1, nonce=1, intent_id_byte="11"), _intent(sender=PK2, nonce=1, intent_id_byte="12")], require_all_nonces=True),
                    _step([_intent(sender=PK1, nonce=2, intent_id_byte="13"), _intent(sender=PK2, nonce=2, intent_id_byte="14")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->InvalidSenderSecondStep",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1, nonce=1, intent_id_byte="15")], require_all_nonces=True),
                    _step([_intent(sender="not-hex", nonce=2, intent_id_byte="16")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->BackwardCompatNoOpThenAdvance",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([_intent(sender=PK1, nonce=None, intent_id_byte="17")], require_all_nonces=False),
                    _step([_intent(sender=PK1, nonce=1, intent_id_byte="18")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->EmptyBatchThenAdvance",
            {
                "initial": _empty_table(),
                "steps": [
                    _step([], require_all_nonces=True),
                    _step([_intent(sender=PK1, nonce=1, intent_id_byte="19")], require_all_nonces=True),
                ],
            },
        ),
        GrammarCase(
            "Seq->SeededTableThenAdvance",
            {
                "initial": _table_with_last(PK1, 5),
                "steps": [
                    _step([_intent(sender=PK1, nonce=6, intent_id_byte="1a"), _intent(sender=PK1, nonce=7, intent_id_byte="1b")], require_all_nonces=True),
                ],
            },
        ),
    ]
    return tuple(cases)


TARGETS: tuple[GrammarTarget, ...] = (
    GrammarTarget(
        name="nonce_replay_sequence",
        runner=_sequence_outcome,
        trace_files=(NONCES_FILE, CANONICAL_FILE),
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

    for step_index, step in enumerate(steps):
        if not isinstance(step, dict):
            continue
        intents = step.get("intents")
        if not isinstance(intents, list):
            continue
        for intent_index in range(len(intents)):
            trimmed = copy.deepcopy(payload)
            del trimmed["steps"][step_index]["intents"][intent_index]
            candidates.append(trimmed)

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
        fingerprint = _payload_fingerprint(case.payload)
        if fingerprint in seen_payloads:
            continue
        seen_payloads.add(fingerprint)
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
            "schema": "zenodex/nonce-replay-sequence-minimized-witness/v1",
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
        "schema": "zenodex/nonce-replay-sequence-grammar-fuzz/v1",
        "reports": [asdict(report) for report in reports],
    }
    json.dump(payload, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
