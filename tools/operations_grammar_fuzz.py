from __future__ import annotations

"""
Deterministic grammar-based boundary explorer for `src.integration.operations`.

This is a real grammar-backed ingress fuzzer for the operations parser layer.
It is intentionally small and bounded: explicit productions describe supported
operation-group carriers, envelope forms, and malformed-but-nearby variants.
The explorer traces line-path signatures through `operations.py` and records
unique `(outcome, path)` pairs.
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

from src.core.settlement import Settlement
from src.integration import operations
from src.integration.operations import (
    SettlementEnvelope,
    SignedIntentEnvelope,
    create_settlement_operation,
    create_signed_intent_operation,
    parse_settlement_envelope,
    parse_signed_intents,
)
from src.state.intents import Intent, IntentKind


ParserFn = Callable[[object], object]
OutcomeFn = Callable[[object], str]
RepairFn = Callable[[str, object], Sequence["GrammarCase"]]


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
    parser: ParserFn
    outcome: OutcomeFn
    trace_files: tuple[Path, ...]
    cases: tuple[GrammarCase, ...]
    repair_fn: RepairFn | None = None


OPERATIONS_FILE = Path(operations.__file__).resolve()


def _hash_path(lines: Sequence[str]) -> str:
    digest = hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()
    return digest[:16]


def _stable_jsonable(value: object) -> object:
    if isinstance(value, dict):
        return {str(k): _stable_jsonable(v) for k, v in sorted(value.items(), key=lambda item: str(item[0]))}
    if isinstance(value, list):
        return [_stable_jsonable(v) for v in value]
    if isinstance(value, tuple):
        return {"__tuple__": [_stable_jsonable(v) for v in value]}
    return value


def _payload_fingerprint(payload: object) -> str:
    return json.dumps(_stable_jsonable(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _trace_outcome(*, parser: ParserFn, outcome_fn: OutcomeFn, payload: object, trace_files: Sequence[Path]) -> tuple[str, str, int]:
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
            result = parser(payload)
            outcome = outcome_fn(result)
        except Exception as exc:  # pragma: no cover - exercised via callers
            outcome = f"{type(exc).__name__}:{exc}"
    finally:
        sys.settrace(previous)

    return outcome, _hash_path(lines), len(lines)


def _valid_intent_dict() -> dict[str, Any]:
    return {
        "module": "TauSwap",
        "version": "0.1",
        "kind": IntentKind.SWAP_EXACT_IN.value,
        "intent_id": "0x" + "11" * 32,
        "sender_pubkey": "pk1",
        "deadline": 1,
        "pool_id": "pool-1",
        "asset_in": "asset-a",
        "asset_out": "asset-b",
        "amount_in": 5,
        "min_amount_out": 0,
    }


def _valid_quote_receipt_transport() -> dict[str, Any]:
    return {
        "body": {"schema": "zenodex/route_quote_receipt/v1", "kind": "exact_in"},
        "receipt_hash": "hash-1",
    }


def _valid_signature() -> str:
    return "sig-1"


def _valid_signed_intent_env() -> SignedIntentEnvelope:
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id="0x" + "11" * 32,
        sender_pubkey="pk1",
        deadline=1,
        fields={
            "pool_id": "pool-1",
            "asset_in": "asset-a",
            "asset_out": "asset-b",
            "amount_in": 5,
            "min_amount_out": 0,
        },
    )
    return SignedIntentEnvelope(intent=intent, signature=_valid_signature(), quote_receipt=_valid_quote_receipt_transport())


def _valid_settlement_ops() -> dict[str, Any]:
    settlement = Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="",
        included_intents=[],
        fills=[],
        balance_deltas=[],
        reserve_deltas=[],
        lp_deltas=[],
        events=None,
    )
    return create_settlement_operation(settlement)


def _signed_intents_outcome(result: object) -> str:
    if not isinstance(result, list):
        raise TypeError("expected signed intent list")
    reparsed = parse_signed_intents(create_signed_intent_operation(result))
    if reparsed != result:
        raise AssertionError("signed intent roundtrip mismatch")
    return f"ok:{len(result)}"


def _settlement_envelope_outcome(result: object) -> str:
    if result is None:
        return "ok:none"
    if not isinstance(result, SettlementEnvelope):
        raise TypeError("expected SettlementEnvelope or None")
    reparsed = parse_settlement_envelope(
        {
            **create_settlement_operation(result.settlement),
            **({"3": {**create_settlement_operation(result.settlement)["3"], "proof": result.proof}} if result.proof is not None else {}),
        }
    )
    if reparsed != result:
        raise AssertionError("settlement envelope roundtrip mismatch")
    return f"ok:proof={1 if result.proof is not None else 0}"


def _signed_intent_cases() -> tuple[GrammarCase, ...]:
    valid_intent = _valid_intent_dict()
    valid_receipt = _valid_quote_receipt_transport()
    valid_sig = _valid_signature()
    cases = [
        GrammarCase("SignedOps->MissingGroup", {}),
        GrammarCase("SignedOps->WrongGroupType", {"2": "oops"}),
        GrammarCase("SignedOps->EmptyList", {"2": []}),
        GrammarCase("SignedOps->OneEntry ; Entry->IntentDict(valid)", {"2": [copy.deepcopy(valid_intent)]}),
        GrammarCase("SignedOps->OneEntry ; Entry->Envelope1(IntentDict(valid))", {"2": [[copy.deepcopy(valid_intent)]]}),
        GrammarCase("SignedOps->OneEntry ; Entry->Envelope2(IntentDict(valid), Signature(valid))", {"2": [[copy.deepcopy(valid_intent), valid_sig]]}),
        GrammarCase("SignedOps->OneEntry ; Entry->Envelope2(IntentDict(valid), QuoteReceipt(valid))", {"2": [[copy.deepcopy(valid_intent), copy.deepcopy(valid_receipt)]]}),
        GrammarCase("SignedOps->OneEntry ; Entry->Envelope3(IntentDict(valid), Signature(valid), QuoteReceipt(valid))", {"2": [[copy.deepcopy(valid_intent), valid_sig, copy.deepcopy(valid_receipt)]]}),
        GrammarCase("SignedOps->OneEntry ; Entry->NonDict", {"2": [1]}),
        GrammarCase("SignedOps->OneEntry ; Entry->BadEnvelopeLen", {"2": [[copy.deepcopy(valid_intent), valid_sig, copy.deepcopy(valid_receipt), 0]]}),
        GrammarCase("SignedOps->OneEntry ; IntentDict->MissingModule", {"2": [{k: v for k, v in valid_intent.items() if k != "module"}]}),
        GrammarCase("SignedOps->OneEntry ; IntentDict->BadModule", {"2": [{**copy.deepcopy(valid_intent), "module": "BadSwap"}]}),
        GrammarCase("SignedOps->OneEntry ; IntentDict->BadKind", {"2": [{**copy.deepcopy(valid_intent), "kind": "UNKNOWN"}]}),
        GrammarCase("SignedOps->OneEntry ; IntentDict->BadDeadlineType", {"2": [{**copy.deepcopy(valid_intent), "deadline": "1"}]}),
        GrammarCase("SignedOps->OneEntry ; IntentDict->SignatureFieldEmpty", {"2": [{**copy.deepcopy(valid_intent), "signature": ""}]}),
        GrammarCase("SignedOps->OneEntry ; IntentDict->QuoteReceiptFieldBadBody", {"2": [{**copy.deepcopy(valid_intent), "quote_receipt": {"body": [], "receipt_hash": "hash-1"}}]}),
        GrammarCase("SignedOps->OneEntry ; Entry->DuplicateSignatureSame", {"2": [[{**copy.deepcopy(valid_intent), "signature": valid_sig}, valid_sig]]}),
        GrammarCase(
            "SignedOps->OneEntry ; Entry->DuplicateSignatureSameWithDeadTail",
            {
                "2": [
                    [{**copy.deepcopy(valid_intent), "signature": valid_sig}, valid_sig],
                    copy.deepcopy(valid_intent),
                ],
                "23": {"dead": True},
            },
        ),
        GrammarCase("SignedOps->OneEntry ; Entry->DuplicateSignatureDiffers", {"2": [[{**copy.deepcopy(valid_intent), "signature": valid_sig}, "sig-2"]]}),
        GrammarCase("SignedOps->OneEntry ; Entry->DuplicateQuoteReceipt", {"2": [[{**copy.deepcopy(valid_intent), "quote_receipt": copy.deepcopy(valid_receipt)}, copy.deepcopy(valid_receipt)]]}),
        GrammarCase("SignedOps->OneEntry ; Entry->Envelope2(IntentDict(valid), QuoteReceipt(missing_hash))", {"2": [[copy.deepcopy(valid_intent), {"body": {}}]]}),
        GrammarCase("SignedOps->TwoEntries ; Entry1->Valid ; Entry2->MissingModule", {"2": [copy.deepcopy(valid_intent), {k: v for k, v in valid_intent.items() if k != "module"}]}),
    ]
    return tuple(cases)


def _settlement_cases() -> tuple[GrammarCase, ...]:
    valid_ops = _valid_settlement_ops()
    valid_settlement = copy.deepcopy(valid_ops["3"])
    cases = [
        GrammarCase("SettlementOps->MissingGroup", {}),
        GrammarCase("SettlementOps->WrongGroupType", {"3": "oops"}),
        GrammarCase("SettlementOps->Valid", copy.deepcopy(valid_ops)),
        GrammarCase("SettlementOps->Valid+Proof", {"3": {**copy.deepcopy(valid_settlement), "proof": {"scheme": "demo"}}}),
        GrammarCase("SettlementOps->Valid+LegacyZkProof", {"3": {**copy.deepcopy(valid_settlement), "zk_proof": {"scheme": "demo"}}}),
        GrammarCase("SettlementOps->DuplicateProofKeys", {"3": {**copy.deepcopy(valid_settlement), "proof": {"a": 1}, "zk_proof": {"b": 2}}}),
        GrammarCase("SettlementOps->ProofWrongType", {"3": {**copy.deepcopy(valid_settlement), "proof": "oops"}}),
        GrammarCase("SettlementOps->BadModule", {"3": {**copy.deepcopy(valid_settlement), "module": "BadSwap"}}),
        GrammarCase("SettlementOps->BadVersion", {"3": {**copy.deepcopy(valid_settlement), "version": "0.2"}}),
        GrammarCase("SettlementOps->IncludedIntentsWrongType", {"3": {**copy.deepcopy(valid_settlement), "included_intents": "oops"}}),
        GrammarCase("SettlementOps->IncludedIntentBadArity", {"3": {**copy.deepcopy(valid_settlement), "included_intents": [["intent-1"]]}}),
        GrammarCase("SettlementOps->IncludedIntentBadAction", {"3": {**copy.deepcopy(valid_settlement), "included_intents": [["intent-1", "UNKNOWN"]]}}),
        GrammarCase("SettlementOps->FillNonObject", {"3": {**copy.deepcopy(valid_settlement), "fills": [1]}}),
        GrammarCase("SettlementOps->EventsWrongType", {"3": {**copy.deepcopy(valid_settlement), "events": {"x": 1}}}),
        GrammarCase("SettlementOps->BalanceDeltaNonObject", {"3": {**copy.deepcopy(valid_settlement), "balance_deltas": [1]}}),
        GrammarCase("SettlementOps->ReserveDeltaNonObject", {"3": {**copy.deepcopy(valid_settlement), "reserve_deltas": [1]}}),
        GrammarCase("SettlementOps->LpDeltaNonObject", {"3": {**copy.deepcopy(valid_settlement), "lp_deltas": [1]}}),
    ]
    return tuple(cases)


def _derive_signed_intent_repairs(outcome: str, payload: object) -> Sequence[GrammarCase]:
    if not isinstance(payload, dict):
        return ()
    valid_intent = _valid_intent_dict()
    valid_receipt = _valid_quote_receipt_transport()
    repairs: list[GrammarCase] = []
    entries = payload.get("2")

    if outcome.startswith("ValueError:operations['2']") or outcome == "ok:0":
        repaired = {"2": [copy.deepcopy(valid_intent)]}
        repairs.append(GrammarCase("repair:signed_ops->valid-group", repaired))
        return tuple(repairs)

    if not isinstance(entries, list) or not entries:
        return ()
    first = copy.deepcopy(entries[0])

    if "Missing required field: module" in outcome:
        if isinstance(first, dict):
            repaired = copy.deepcopy(payload)
            repaired["2"][0]["module"] = valid_intent["module"]
            repairs.append(GrammarCase("repair:signed_ops->restore-module", repaired))
        elif isinstance(first, list) and first and isinstance(first[0], dict):
            repaired = copy.deepcopy(payload)
            repaired["2"][0][0]["module"] = valid_intent["module"]
            repairs.append(GrammarCase("repair:signed_ops->restore-envelope-module", repaired))
    elif "Invalid module: BadSwap" in outcome:
        if isinstance(first, dict):
            repaired = copy.deepcopy(payload)
            repaired["2"][0]["module"] = valid_intent["module"]
            repairs.append(GrammarCase("repair:signed_ops->fix-module", repaired))
    elif "Invalid intent kind: UNKNOWN" in outcome:
        if isinstance(first, dict):
            repaired = copy.deepcopy(payload)
            repaired["2"][0]["kind"] = valid_intent["kind"]
            repairs.append(GrammarCase("repair:signed_ops->fix-kind", repaired))
    elif "intent.deadline must be an int" in outcome:
        if isinstance(first, dict):
            repaired = copy.deepcopy(payload)
            repaired["2"][0]["deadline"] = valid_intent["deadline"]
            repairs.append(GrammarCase("repair:signed_ops->fix-deadline", repaired))
    elif "intent entry must be a dict" in outcome:
        repairs.append(GrammarCase("repair:signed_ops->replace-entry-with-valid-intent", {"2": [copy.deepcopy(valid_intent)]}))
    elif "intent list entry must have length 1, 2, or 3" in outcome and isinstance(first, list):
        repaired = {"2": [first[:3]]}
        repairs.append(GrammarCase("repair:signed_ops->trim-envelope", repaired))
    elif "signature provided twice" in outcome and isinstance(first, list) and first:
        repaired = {"2": [[copy.deepcopy(first[0])]]}
        repairs.append(GrammarCase("repair:signed_ops->drop-envelope-signature", repaired))
    elif "quote_receipt provided twice" in outcome and isinstance(first, list) and first:
        repaired = {"2": [[copy.deepcopy(first[0])]]}
        repairs.append(GrammarCase("repair:signed_ops->drop-envelope-receipt", repaired))
    elif "quote_receipt.body must be an object" in outcome and isinstance(first, dict):
        repaired = copy.deepcopy(payload)
        repaired["2"][0]["quote_receipt"] = copy.deepcopy(valid_receipt)
        repairs.append(GrammarCase("repair:signed_ops->fix-receipt-body", repaired))
    elif "quote_receipt.receipt_hash must be a non-empty string" in outcome and isinstance(first, list):
        repaired = copy.deepcopy(payload)
        if len(repaired["2"][0]) >= 2 and isinstance(repaired["2"][0][1], dict):
            repaired["2"][0][1]["receipt_hash"] = valid_receipt["receipt_hash"]
            repairs.append(GrammarCase("repair:signed_ops->add-receipt-hash", repaired))
    elif "signature must be non-empty" in outcome and isinstance(first, dict):
        repaired = copy.deepcopy(payload)
        repaired["2"][0]["signature"] = _valid_signature()
        repairs.append(GrammarCase("repair:signed_ops->fill-signature", repaired))

    return tuple(repairs)


def _derive_settlement_repairs(outcome: str, payload: object) -> Sequence[GrammarCase]:
    if not isinstance(payload, dict):
        return ()
    valid_ops = _valid_settlement_ops()
    valid_settlement = copy.deepcopy(valid_ops["3"])
    repairs: list[GrammarCase] = []

    if outcome.startswith("ValueError:operations['3']") or outcome == "ok:none":
        repairs.append(GrammarCase("repair:settlement_ops->valid-group", copy.deepcopy(valid_ops)))
        return tuple(repairs)

    body = payload.get("3")
    if not isinstance(body, dict):
        return ()

    if "settlement proof provided twice" in outcome:
        repaired = copy.deepcopy(payload)
        repaired["3"].pop("zk_proof", None)
        repairs.append(GrammarCase("repair:settlement_ops->drop-legacy-proof", repaired))
    elif "settlement proof must be an object" in outcome:
        repaired = copy.deepcopy(payload)
        repaired["3"]["proof"] = {"scheme": "demo"}
        repairs.append(GrammarCase("repair:settlement_ops->fix-proof-object", repaired))
    elif "Invalid module: BadSwap" in outcome:
        repaired = copy.deepcopy(payload)
        repaired["3"]["module"] = valid_settlement["module"]
        repairs.append(GrammarCase("repair:settlement_ops->fix-module", repaired))
    elif "Invalid version: 0.2" in outcome:
        repaired = copy.deepcopy(payload)
        repaired["3"]["version"] = valid_settlement["version"]
        repairs.append(GrammarCase("repair:settlement_ops->fix-version", repaired))
    elif "settlement.included_intents must be a list" in outcome:
        repaired = copy.deepcopy(payload)
        repaired["3"]["included_intents"] = []
        repairs.append(GrammarCase("repair:settlement_ops->empty-included-intents", repaired))
    elif "fills entries must be objects" in outcome:
        repaired = copy.deepcopy(payload)
        repaired["3"]["fills"] = []
        repairs.append(GrammarCase("repair:settlement_ops->empty-fills", repaired))
    elif "settlement.events must be a list" in outcome:
        repaired = copy.deepcopy(payload)
        repaired["3"].pop("events", None)
        repairs.append(GrammarCase("repair:settlement_ops->empty-events", repaired))
    elif "balance_deltas entries must be objects" in outcome:
        repaired = copy.deepcopy(payload)
        repaired["3"]["balance_deltas"] = []
        repairs.append(GrammarCase("repair:settlement_ops->empty-balance-deltas", repaired))
    elif "reserve_deltas entries must be objects" in outcome:
        repaired = copy.deepcopy(payload)
        repaired["3"]["reserve_deltas"] = []
        repairs.append(GrammarCase("repair:settlement_ops->empty-reserve-deltas", repaired))
    elif "lp_deltas entries must be objects" in outcome:
        repaired = copy.deepcopy(payload)
        repaired["3"]["lp_deltas"] = []
        repairs.append(GrammarCase("repair:settlement_ops->empty-lp-deltas", repaired))

    return tuple(repairs)


TARGETS: tuple[GrammarTarget, ...] = (
    GrammarTarget(
        name="signed_intents",
        parser=parse_signed_intents,
        outcome=_signed_intents_outcome,
        trace_files=(OPERATIONS_FILE,),
        cases=_signed_intent_cases(),
        repair_fn=_derive_signed_intent_repairs,
    ),
    GrammarTarget(
        name="settlement_envelope",
        parser=parse_settlement_envelope,
        outcome=_settlement_envelope_outcome,
        trace_files=(OPERATIONS_FILE,),
        cases=_settlement_cases(),
        repair_fn=_derive_settlement_repairs,
    ),
)

TARGET_INDEX = {target.name: target for target in TARGETS}


def _payload_size(payload: object) -> int:
    return len(_payload_fingerprint(payload))


def _find_case(target_name: str, derivation: str) -> GrammarCase:
    target = TARGET_INDEX[target_name]
    for case in target.cases:
        if case.derivation == derivation:
            return case
    raise KeyError(f"unknown derivation for {target_name}: {derivation}")


def _minimization_candidates(payload: object) -> tuple[object, ...]:
    if not isinstance(payload, dict):
        return ()
    candidates: list[object] = []
    for key in sorted(payload):
        trimmed = copy.deepcopy(payload)
        del trimmed[key]
        candidates.append(trimmed)

    intents = payload.get("2")
    if isinstance(intents, list):
        for idx in range(len(intents)):
            trimmed = copy.deepcopy(payload)
            del trimmed["2"][idx]
            candidates.append(trimmed)
        for idx, entry in enumerate(intents):
            if isinstance(entry, list):
                for sub_idx in range(len(entry)):
                    trimmed = copy.deepcopy(payload)
                    del trimmed["2"][idx][sub_idx]
                    candidates.append(trimmed)
            elif isinstance(entry, dict):
                for key in sorted(entry):
                    trimmed = copy.deepcopy(payload)
                    del trimmed["2"][idx][key]
                    candidates.append(trimmed)

    settlement = payload.get("3")
    if isinstance(settlement, dict):
        for key in sorted(settlement):
            trimmed = copy.deepcopy(payload)
            del trimmed["3"][key]
            candidates.append(trimmed)

    return tuple(candidates)


def minimize_case(target_name: str, derivation: str, *, max_rounds: int = 16) -> MinimizedWitness:
    if target_name == "all":
        raise KeyError("minimize_case requires a concrete target")
    target = TARGET_INDEX[target_name]
    case = _find_case(target_name, derivation)
    current = copy.deepcopy(case.payload)
    outcome_label, path_id, path_length = _trace_outcome(
        parser=target.parser,
        outcome_fn=target.outcome,
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
                parser=target.parser,
                outcome_fn=target.outcome,
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


def explore_target(name: str) -> GrammarTargetReport:
    target = TARGET_INDEX[name]
    seen_pairs: set[tuple[str, str]] = set()
    seen_outcomes: set[str] = set()
    seen_paths: set[str] = set()
    seen_payloads: set[str] = set()
    cases: list[BoundaryCase] = []
    frontier: list[tuple[int, int, GrammarCase]] = [(0, idx, case) for idx, case in enumerate(target.cases)]

    while frontier:
        depth, _, case = frontier.pop(0)
        payload_fp = _payload_fingerprint(case.payload)
        if payload_fp in seen_payloads:
            continue
        seen_payloads.add(payload_fp)
        outcome, path_id, path_length = _trace_outcome(
            parser=target.parser,
            outcome_fn=target.outcome,
            payload=case.payload,
            trace_files=target.trace_files,
        )
        pair = (outcome, path_id)
        if pair in seen_pairs:
            continue
        seen_pairs.add(pair)
        seen_outcomes.add(outcome)
        seen_paths.add(path_id)
        cases.append(
            BoundaryCase(
                derivation=case.derivation,
                outcome_label=outcome,
                path_id=path_id,
                path_length=path_length,
            )
        )
        if depth >= 1 or target.repair_fn is None:
            continue
        for repair_index, repair_case in enumerate(target.repair_fn(outcome, case.payload)):
            frontier.append((depth + 1, repair_index, repair_case))

    return GrammarTargetReport(
        target=name,
        total_cases=len(cases),
        unique_outcome_count=len(seen_outcomes),
        unique_path_count=len(seen_paths),
        cases=tuple(sorted(cases, key=lambda item: (item.outcome_label, item.derivation, item.path_id))),
    )


def explore_all_targets() -> tuple[GrammarTargetReport, ...]:
    return tuple(explore_target(target.name) for target in TARGETS)


def _reports_json(reports: Sequence[GrammarTargetReport]) -> dict[str, Any]:
    return {
        "schema": "zenodex/operations-grammar-fuzz/v1",
        "reports": [asdict(report) for report in reports],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Deterministic grammar-based fuzz explorer for operations parsing.")
    parser.add_argument(
        "--target",
        default="all",
        choices=("all",) + tuple(sorted(TARGET_INDEX)),
        help="Parser target to explore.",
    )
    parser.add_argument("--format", default="json", choices=("json", "text"))
    parser.add_argument("--minimize-derivation", help="minimize one named derivation while preserving its outcome/path pair")
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.minimize_derivation:
        if args.target == "all":
            parser.error("--minimize-derivation requires a concrete --target")
        witness = minimize_case(args.target, args.minimize_derivation)
        if args.format == "json":
            print(
                json.dumps(
                    {
                        "schema": "zenodex/operations-minimized-witness/v1",
                        "witness": {
                            **asdict(witness),
                            "payload": _stable_jsonable(witness.payload),
                        },
                    },
                    indent=2,
                    sort_keys=True,
                )
            )
            return 0
        print(f"[{witness.target}] {witness.derivation}")
        print(f"outcome={witness.outcome_label} path={witness.path_id} len={witness.path_length}")
        print(f"size={witness.original_size}->{witness.minimized_size}")
        print(json.dumps(_stable_jsonable(witness.payload), indent=2, sort_keys=True))
        return 0

    reports = explore_all_targets() if args.target == "all" else (explore_target(args.target),)
    if args.format == "json":
        print(json.dumps(_reports_json(reports), indent=2, sort_keys=True))
        return 0

    for report in reports:
        print(f"[{report.target}] cases={report.total_cases} outcomes={report.unique_outcome_count} paths={report.unique_path_count}")
        for case in report.cases:
            print(f"  - {case.derivation}: {case.outcome_label} path={case.path_id} len={case.path_length}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
