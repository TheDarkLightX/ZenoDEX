"""
Deterministic grammar-based transport explorer for `src.core.quote_receipts`.

This is a grammar-backed boundary fuzzer for route-quote receipt transport and
precheck structure. It focuses on receipt envelope shape and nearby repairs
before the deeper replay semantics dominate:
- top-level receipt/body presence
- receipt hash presence/match
- schema/kind/body-asset/quote-epoch checks
- pools/legs transport shape
- exact-in canonical certificate transport

The explorer traces line-path signatures through `quote_receipts.py` and records
unique `(outcome, path)` pairs. It is bounded, deterministic, and intended for
offline discovery and regression pinning, not as acceptance proof for
functional-core correctness.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import heapq
import json
import sys
from collections.abc import Mapping
from collections.abc import Sequence as SequenceABC
from dataclasses import asdict, dataclass, is_dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Sequence

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool  # noqa: E402
from src.core.quote_receipts import (  # noqa: E402
    make_route_quote_receipt,
    receipt_hash,
    verify_route_quote_receipt,
)
from src.core.routing import RouteHop, RouteLeg, RouteQuote  # noqa: E402
from src.state.pools import PoolState, PoolStatus  # noqa: E402

RunnerFn = Callable[[object], str]
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
    runner: RunnerFn
    trace_files: tuple[Path, ...]
    cases: tuple[GrammarCase, ...]
    repair_fn: RepairFn | None = None


QUOTE_RECEIPTS_FILE = ROOT_DIR / "src/core/quote_receipts.py"
QUOTE_RECEIPT_BODY_VERIFICATION_FILE = ROOT_DIR / "src/core/quote_receipt_body_verification.py"
QUOTE_RECEIPT_GATES_FILE = ROOT_DIR / "src/core/quote_receipt_gates.py"
QUOTE_RECEIPT_GATE_CONTRACT_FILE = ROOT_DIR / "src/core/quote_receipt_gate_contract.py"
QUOTE_RECEIPT_TRACE_FILES = (
    QUOTE_RECEIPTS_FILE,
    QUOTE_RECEIPT_BODY_VERIFICATION_FILE,
    QUOTE_RECEIPT_GATES_FILE,
    QUOTE_RECEIPT_GATE_CONTRACT_FILE,
)


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _valid_exact_out_seed() -> tuple[Mapping[str, Any], dict[str, PoolState]]:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0)}
    pool = pools["p_ab"]
    amount_out = 50
    amount_in, _ = swap_exact_out_for_pool(
        pool,
        reserve_in=int(pool.reserve0),
        reserve_out=int(pool.reserve1),
        amount_out=amount_out,
    )
    quote = RouteQuote(
        asset_in="A",
        asset_out="B",
        amount_in=int(amount_in),
        amount_out=amount_out,
        legs=(
            RouteLeg(
                amount_in=int(amount_in),
                amount_out=amount_out,
                hops=(
                    RouteHop(
                        pool_id="p_ab",
                        asset_in="A",
                        asset_out="B",
                        amount_in=int(amount_in),
                        amount_out=amount_out,
                    ),
                ),
            ),
        ),
    )
    return make_route_quote_receipt(kind="exact_out", quote=quote, pools_by_id=pools, quote_epoch=7), pools


def _valid_exact_in_seed() -> tuple[Mapping[str, Any], dict[str, PoolState]]:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0)}
    pool = pools["p_ab"]
    amount_in = 50
    amount_out, _ = swap_exact_in_for_pool(
        pool,
        reserve_in=int(pool.reserve0),
        reserve_out=int(pool.reserve1),
        amount_in=amount_in,
    )
    quote = RouteQuote(
        asset_in="A",
        asset_out="B",
        amount_in=amount_in,
        amount_out=int(amount_out),
        legs=(
            RouteLeg(
                amount_in=amount_in,
                amount_out=int(amount_out),
                hops=(
                    RouteHop(
                        pool_id="p_ab",
                        asset_in="A",
                        asset_out="B",
                        amount_in=amount_in,
                        amount_out=int(amount_out),
                    ),
                ),
            ),
        ),
    )
    return make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=7), pools


def _hash_path(lines: Sequence[str]) -> str:
    digest = hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()
    return digest[:16]


def _stable_jsonable(value: object) -> object:
    if isinstance(value, Enum):
        return str(value.value)
    if is_dataclass(value):
        return _stable_jsonable(asdict(value))
    if isinstance(value, Mapping):
        return {str(k): _stable_jsonable(v) for k, v in sorted(value.items(), key=lambda item: str(item[0]))}
    if isinstance(value, SequenceABC) and not isinstance(value, (str, bytes, bytearray)):
        return [_stable_jsonable(v) for v in value]
    return value


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


def _quote_receipt_outcome(payload: object) -> str:
    if not isinstance(payload, tuple) or len(payload) != 2:
        raise TypeError("payload must be a (receipt, pools) tuple")
    receipt, pools = payload
    if not isinstance(pools, dict):
        raise TypeError("pools must be a dict")
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    return "ok" if ok else f"reject:{err}"


def _mutate_seed(
    seed: object,
    *,
    receipt_mutator: Callable[[dict[str, Any]], dict[str, Any]] | None = None,
    pools_mutator: Callable[[dict[str, PoolState]], None] | None = None,
) -> object:
    if not isinstance(seed, tuple) or len(seed) != 2:
        raise TypeError("seed must be a (receipt, pools) tuple")
    receipt = copy.deepcopy(seed[0])
    pools = copy.deepcopy(seed[1])
    if receipt_mutator is not None:
        receipt = receipt_mutator(receipt)
    if pools_mutator is not None:
        if not isinstance(pools, dict):
            raise TypeError("pools must be a dict")
        pools_mutator(pools)
    return receipt, pools


def _rehash(receipt: dict[str, Any]) -> dict[str, Any]:
    body = receipt.get("body")
    if isinstance(body, dict):
        receipt["receipt_hash"] = receipt_hash(body)
    return receipt


def _receipt_cases() -> tuple[GrammarCase, ...]:
    exact_out = _valid_exact_out_seed()
    cases = [
        GrammarCase("QuoteReceipt->NonDict", (["not", "a", "receipt"], exact_out[1])),
        GrammarCase("QuoteReceipt->MissingBody", ({"receipt_hash": "hash-only"}, exact_out[1])),
        GrammarCase("QuoteReceipt->ExactOut(valid)", exact_out),
        GrammarCase(
            "QuoteReceipt->ExactOut ; Body->BadSchema",
            _mutate_seed(exact_out, receipt_mutator=lambda receipt: _rehash({**receipt, "body": {**receipt["body"], "schema": "bad/schema"}})),
        ),
        GrammarCase(
            "QuoteReceipt->ExactOut ; ReceiptHash->Missing",
            _mutate_seed(exact_out, receipt_mutator=lambda receipt: {**receipt, "receipt_hash": ""}),
        ),
        GrammarCase(
            "QuoteReceipt->ExactOut ; ReceiptHash->MissingWithDeadBlob",
            _mutate_seed(
                exact_out,
                receipt_mutator=lambda receipt: {
                    **receipt,
                    "receipt_hash": "",
                    "dead_transport_blob": {"junk": ["x", "y", "z"], "note": "ignored"},
                },
            ),
        ),
        GrammarCase(
            "QuoteReceipt->ExactOut ; ReceiptHash->Mismatch",
            _mutate_seed(exact_out, receipt_mutator=lambda receipt: {**receipt, "receipt_hash": "bad-hash"}),
        ),
        GrammarCase(
            "QuoteReceipt->ExactOut ; Body->BadKind",
            _mutate_seed(exact_out, receipt_mutator=lambda receipt: _rehash({**receipt, "body": {**receipt["body"], "kind": "bad_kind"}})),
        ),
        GrammarCase(
            "QuoteReceipt->ExactOut ; Body->UnexpectedCanonicalCertificate",
            _mutate_seed(
                exact_out,
                receipt_mutator=lambda receipt: _rehash(
                    {**receipt, "body": {**receipt["body"], "canonical_route_certificate": {"winner_quote": {}}}}
                ),
            ),
        ),
        GrammarCase(
            "QuoteReceipt->ExactOut ; Body->BadBodyAssets",
            _mutate_seed(exact_out, receipt_mutator=lambda receipt: _rehash({**receipt, "body": {**receipt["body"], "asset_out": "A"}})),
        ),
        GrammarCase(
            "QuoteReceipt->ExactOut ; Body->BadQuoteEpoch",
            _mutate_seed(exact_out, receipt_mutator=lambda receipt: _rehash({**receipt, "body": {**receipt["body"], "quote_epoch": -1}})),
        ),
        GrammarCase(
            "QuoteReceipt->ExactOut ; Body->BadPoolsShape",
            _mutate_seed(exact_out, receipt_mutator=lambda receipt: _rehash({**receipt, "body": {**receipt["body"], "pools": []}})),
        ),
        GrammarCase(
            "QuoteReceipt->ExactOut ; Body->BadLegsShape",
            _mutate_seed(exact_out, receipt_mutator=lambda receipt: _rehash({**receipt, "body": {**receipt["body"], "legs": []}})),
        ),
    ]
    return tuple(cases)


def _certificate_cases() -> tuple[GrammarCase, ...]:
    exact_in = _valid_exact_in_seed()
    cases = [
        GrammarCase("QuoteReceiptExactIn->Valid", exact_in),
        GrammarCase(
            "QuoteReceiptExactIn->TamperedCanonicalCertificate",
            _mutate_seed(
                exact_in,
                receipt_mutator=lambda receipt: _rehash(
                    {
                        **receipt,
                        "body": {
                            **receipt["body"],
                            "canonical_route_certificate": {
                                **receipt["body"]["canonical_route_certificate"],
                                "winner_index": int(receipt["body"]["canonical_route_certificate"]["winner_index"]) + 1,
                            },
                        },
                    }
                ),
            ),
        ),
        GrammarCase(
            "QuoteReceiptExactIn->CertificateWrongType",
            _mutate_seed(
                exact_in,
                receipt_mutator=lambda receipt: _rehash(
                    {**receipt, "body": {**receipt["body"], "canonical_route_certificate": "oops"}}
                ),
            ),
        ),
        GrammarCase(
            "QuoteReceiptExactIn->CertificateMissingWinnerQuote",
            _mutate_seed(
                exact_in,
                receipt_mutator=lambda receipt: _rehash(
                    {**receipt, "body": {**receipt["body"], "canonical_route_certificate": {"winner_index": 0}}}
                ),
            ),
        ),
    ]
    return tuple(cases)


def _derive_receipt_repairs(outcome: str, payload: object) -> Sequence[GrammarCase]:
    if not isinstance(payload, tuple) or len(payload) != 2:
        return ()
    receipt, pools = payload
    if not isinstance(receipt, dict):
        return ()
    repairs: list[GrammarCase] = []

    if outcome == "reject:missing_body":
        repairs.append(GrammarCase("repair:receipt->restore-valid-exact-out", _valid_exact_out_seed()))
        return tuple(repairs)

    body = receipt.get("body")
    if not isinstance(body, dict):
        return ()

    if outcome == "reject:missing_receipt_hash":
        fixed = copy.deepcopy(receipt)
        fixed["receipt_hash"] = receipt_hash(body)
        repairs.append(GrammarCase("repair:receipt->restore-hash", (fixed, copy.deepcopy(pools))))
    elif outcome == "reject:hash_mismatch":
        fixed = copy.deepcopy(receipt)
        fixed["receipt_hash"] = receipt_hash(body)
        repairs.append(GrammarCase("repair:receipt->fix-hash", (fixed, copy.deepcopy(pools))))
    elif outcome == "reject:bad_schema":
        fixed = copy.deepcopy(receipt)
        fixed["body"]["schema"] = "zenodex/route_quote_receipt/v1"
        repairs.append(GrammarCase("repair:receipt->fix-schema", (_rehash(fixed), copy.deepcopy(pools))))
    elif outcome == "reject:bad_kind":
        fixed = copy.deepcopy(receipt)
        fixed["body"]["kind"] = "exact_out"
        repairs.append(GrammarCase("repair:receipt->fix-kind", (_rehash(fixed), copy.deepcopy(pools))))
    elif outcome == "reject:unexpected_canonical_route_certificate":
        fixed = copy.deepcopy(receipt)
        fixed["body"].pop("canonical_route_certificate", None)
        repairs.append(GrammarCase("repair:receipt->drop-certificate", (_rehash(fixed), copy.deepcopy(pools))))
    elif outcome == "reject:bad_body_assets":
        fixed = copy.deepcopy(receipt)
        fixed["body"]["asset_out"] = "B"
        repairs.append(GrammarCase("repair:receipt->fix-assets", (_rehash(fixed), copy.deepcopy(pools))))
    elif outcome == "reject:bad_quote_epoch":
        fixed = copy.deepcopy(receipt)
        fixed["body"]["quote_epoch"] = 0
        repairs.append(GrammarCase("repair:receipt->fix-quote-epoch", (_rehash(fixed), copy.deepcopy(pools))))
    elif outcome == "reject:bad_pools":
        repairs.append(GrammarCase("repair:receipt->restore-pools", _valid_exact_out_seed()))
    elif outcome == "reject:bad_legs":
        repairs.append(GrammarCase("repair:receipt->restore-legs", _valid_exact_out_seed()))

    return tuple(repairs)


def _derive_certificate_repairs(outcome: str, payload: object) -> Sequence[GrammarCase]:
    if not isinstance(payload, tuple) or len(payload) != 2:
        return ()
    receipt, pools = payload
    if not isinstance(receipt, dict):
        return ()
    if not isinstance(receipt.get("body"), dict):
        return ()

    repairs: list[GrammarCase] = []
    if outcome.startswith("reject:bad_canonical_route_certificate"):
        repairs.append(GrammarCase("repair:cert->restore-valid-exact-in", _valid_exact_in_seed()))
        fixed = copy.deepcopy(receipt)
        fixed["body"].pop("canonical_route_certificate", None)
        repairs.append(GrammarCase("repair:cert->drop-canonical-certificate", (_rehash(fixed), copy.deepcopy(pools))))
    return tuple(repairs)


TARGETS: tuple[GrammarTarget, ...] = (
    GrammarTarget(
        name="quote_receipt_transport",
        runner=_quote_receipt_outcome,
        trace_files=QUOTE_RECEIPT_TRACE_FILES,
        cases=_receipt_cases(),
        repair_fn=_derive_receipt_repairs,
    ),
    GrammarTarget(
        name="quote_receipt_exact_in_certificate",
        runner=_quote_receipt_outcome,
        trace_files=QUOTE_RECEIPT_TRACE_FILES,
        cases=_certificate_cases(),
        repair_fn=_derive_certificate_repairs,
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
    if not isinstance(payload, tuple) or len(payload) != 2:
        return ()
    receipt, pools = payload
    candidates: list[object] = []

    if isinstance(receipt, dict):
        for key in sorted(receipt):
            trimmed_receipt = copy.deepcopy(receipt)
            del trimmed_receipt[key]
            candidates.append((trimmed_receipt, copy.deepcopy(pools)))
        body = receipt.get("body")
        if isinstance(body, dict):
            for key in sorted(body):
                trimmed_receipt = copy.deepcopy(receipt)
                del trimmed_receipt["body"][key]
                candidates.append((trimmed_receipt, copy.deepcopy(pools)))

    if isinstance(pools, dict):
        for key in sorted(pools):
            trimmed_pools = copy.deepcopy(pools)
            del trimmed_pools[key]
            candidates.append((copy.deepcopy(receipt), trimmed_pools))

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
    order_counter = 0
    frontier: list[tuple[int, int, str, object]] = []

    def push(case: GrammarCase) -> None:
        nonlocal order_counter
        order_counter += 1
        priority = 0 if case.derivation.startswith("repair:") else 1
        heapq.heappush(frontier, (priority, order_counter, case.derivation, case.payload))

    for case in target.cases:
        push(case)

    while frontier and len(accepted) < max_cases:
        _priority, _ord, derivation, payload = heapq.heappop(frontier)
        fingerprint = _payload_fingerprint(payload)
        if fingerprint in seen_payloads:
            continue
        seen_payloads.add(fingerprint)

        outcome_label, path_id, path_length = _trace_outcome(
            runner=target.runner,
            payload=payload,
            trace_files=target.trace_files,
        )
        pair = (outcome_label, path_id)
        if pair not in seen_pairs:
            seen_pairs.add(pair)
            accepted.append(
                BoundaryCase(
                    derivation=derivation,
                    outcome_label=outcome_label,
                    path_id=path_id,
                    path_length=path_length,
                )
            )

        if target.repair_fn is not None:
            for followup in target.repair_fn(outcome_label, payload):
                push(followup)

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
            "schema": "zenodex/quote-receipt-transport-minimized-witness/v1",
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
        "schema": "zenodex/quote-receipt-transport-grammar-fuzz/v1",
        "reports": [asdict(report) for report in reports],
    }
    json.dump(payload, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
