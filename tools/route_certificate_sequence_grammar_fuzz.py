from __future__ import annotations

"""State-feedback explorer for exact-in route-certificate replay and canonicalization."""

import argparse
import copy
import hashlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Sequence, cast

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from src.core.routing import RouteHop, RouteLeg, RouteQuote
from src.integration.exact_in_route_certificate import (
    build_exact_in_route_canonical_certificate,
    verify_exact_in_route_canonical_certificate,
)
from tools.stateful_feedback import (
    ExplorationTargetReport,
    FeedbackMode,
    Mutation,
    explore_bounded_frontier,
    load_dangerous_surface_manifest,
    report_to_json,
    stable_jsonable,
)
from tools.stateful_semantics import route_certificate_action_summary, route_certificate_semantic_state


EXACT_IN_CERTIFICATE_FILE = (ROOT_DIR / "src/integration/exact_in_route_certificate.py").resolve()


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


def _quote_one_hop(*, pool_id: str, amount_out: int) -> RouteQuote:
    hop = RouteHop(pool_id=pool_id, asset_in="A", asset_out="B", amount_in=10, amount_out=amount_out)
    leg = RouteLeg(hops=(hop,), amount_in=10, amount_out=amount_out)
    return RouteQuote(asset_in="A", asset_out="B", amount_in=10, amount_out=amount_out, legs=(leg,))


def _seed_payload() -> dict[str, Any]:
    initial_quotes = [_quote_one_hop(pool_id="pool_a", amount_out=14), _quote_one_hop(pool_id="pool_b", amount_out=18)]
    return {
        "initial_quotes": initial_quotes,
        "steps": [
            {"quotes": copy.deepcopy(initial_quotes)},
        ],
    }


def _trace(payload: object) -> tuple[str, str, int, tuple[str, ...]]:
    trace_names = {str(EXACT_IN_CERTIFICATE_FILE)}
    lines: list[str] = []
    last_loc: str | None = None

    def tracer(frame, event, arg):
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
            outcome = _sequence_outcome(payload)
        except Exception as exc:  # pragma: no cover
            outcome = f"{type(exc).__name__}:{exc}"
    finally:
        sys.settrace(previous)
    digest = hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()[:16]
    return outcome, digest, len(lines), tuple(lines)


def _sequence_outcome(payload: object) -> str:
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    initial_quotes = payload.get("initial_quotes")
    steps = payload.get("steps")
    if not isinstance(initial_quotes, list) or not initial_quotes:
        raise TypeError("initial_quotes must be a non-empty list")
    if not isinstance(steps, list) or not steps:
        raise TypeError("steps must be a non-empty list")
    if not all(isinstance(quote, RouteQuote) for quote in initial_quotes):
        raise TypeError("initial_quotes entries must be RouteQuote")

    certificate = build_exact_in_route_canonical_certificate(initial_quotes)
    ok0, err0 = verify_exact_in_route_canonical_certificate(initial_quotes, certificate=certificate)
    if not ok0:
        return f"reject:step=0:{err0}"

    for idx, step in enumerate(steps, start=1):
        if not isinstance(step, dict):
            raise TypeError(f"step {idx} must be a dict")
        quotes = step.get("quotes")
        if not isinstance(quotes, list) or not quotes:
            raise TypeError(f"step {idx}.quotes must be a non-empty list")
        if not all(isinstance(quote, RouteQuote) for quote in quotes):
            raise TypeError(f"step {idx}.quotes entries must be RouteQuote")
        ok, err = verify_exact_in_route_canonical_certificate(quotes, certificate=certificate)
        if not ok:
            return f"reject:step={idx}:{err}"
    return f"ok:winner_index={certificate.winner_index}:candidate_count={len(certificate.candidates)}"


def _expandable(payload: object) -> bool:
    return isinstance(payload, dict) and isinstance(payload.get("steps"), list)


def _payload_step_quotes(payload: object) -> tuple[dict[str, Any], list[RouteQuote]]:
    out = cast(dict[str, Any], copy.deepcopy(payload))
    steps = cast(list[dict[str, Any]], out["steps"])
    step0 = steps[0]
    quotes = cast(list[RouteQuote], step0["quotes"])
    return out, quotes


def _add_better_candidate(payload: object) -> object:
    out, quotes = _payload_step_quotes(payload)
    quotes.append(_quote_one_hop(pool_id="pool_c", amount_out=19))
    return out


def _reorder_candidates(payload: object) -> object:
    out, quotes = _payload_step_quotes(payload)
    cast(list[dict[str, Any]], out["steps"])[0]["quotes"] = list(reversed(quotes))
    return out


def _mutate_existing_candidate(payload: object) -> object:
    out, quotes = _payload_step_quotes(payload)
    quotes[1] = _quote_one_hop(pool_id="pool_b", amount_out=17)
    return out


def _duplicate_candidate(payload: object) -> object:
    out, quotes = _payload_step_quotes(payload)
    quotes.append(copy.deepcopy(quotes[0]))
    return out


MUTATIONS: tuple[Mutation, ...] = (
    Mutation(name="add_better_candidate", apply=_add_better_candidate),
    Mutation(name="reorder_candidates", apply=_reorder_candidates),
    Mutation(name="mutate_existing_candidate", apply=_mutate_existing_candidate),
    Mutation(name="duplicate_candidate", apply=_duplicate_candidate),
)
DERIVATION_BUILDERS: dict[str, Callable[[], object]] = {
    "valid_seed": _seed_payload,
    "add_better_candidate": lambda: _add_better_candidate(_seed_payload()),
    "reorder_candidates": lambda: _reorder_candidates(_seed_payload()),
    "mutate_existing_candidate": lambda: _mutate_existing_candidate(_seed_payload()),
    "duplicate_candidate": lambda: _duplicate_candidate(_seed_payload()),
}


def _payload_size(payload: object) -> int:
    return len(json.dumps(stable_jsonable(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True))


def minimize_case(derivation: str) -> MinimizedWitness:
    if derivation not in DERIVATION_BUILDERS:
        raise KeyError(f"unknown derivation: {derivation}")
    payload = DERIVATION_BUILDERS[derivation]()
    outcome_label, path_id, path_length, _ = _trace(payload)
    size = _payload_size(payload)
    return MinimizedWitness(
        target="route_certificate_sequence",
        derivation=derivation,
        outcome_label=outcome_label,
        path_id=path_id,
        path_length=path_length,
        original_size=size,
        minimized_size=size,
        payload=payload,
    )


def explore_target(
    name: str = "route_certificate_sequence",
    *,
    max_depth: int = 2,
    max_frontier: int = 64,
    target_manifest: str | None = None,
    target_id: str | None = None,
    feedback_mode: FeedbackMode = "stateful",
):
    if name != "route_certificate_sequence":
        raise KeyError(f"unknown target: {name}")
    dangerous_surfaces = load_dangerous_surface_manifest(target_manifest)
    return explore_bounded_frontier(
        harness_id="route_certificate_sequence:route_certificate_sequence",
        seed=_seed_payload(),
        mutations=MUTATIONS,
        trace_fn=_trace,
        expandable=_expandable,
        max_depth=max_depth,
        max_frontier=max_frontier,
        feedback_mode=feedback_mode,
        dangerous_surfaces=dangerous_surfaces,
        target_id=target_id,
        semantic_state_fn=route_certificate_semantic_state,
        action_summary_fn=route_certificate_action_summary,
    )


def explore_all_targets(
    *,
    max_depth: int = 2,
    max_frontier: int = 64,
    target_manifest: str | None = None,
    target_id: str | None = None,
    feedback_mode: FeedbackMode = "stateful",
):
    return (
        explore_target(
            max_depth=max_depth,
            max_frontier=max_frontier,
            target_manifest=target_manifest,
            target_id=target_id,
            feedback_mode=feedback_mode,
        ),
    )


def _reports_json(reports: Sequence[ExplorationTargetReport]) -> dict[str, Any]:
    return {
        "schema": "zenodex/route-certificate-sequence-grammar-fuzz/v1",
        "reports": [report_to_json(report) for report in reports],
    }


def _minimized_witness_json(witness: MinimizedWitness) -> dict[str, Any]:
    return {
        "schema": "zenodex/route-certificate-sequence-minimized-witness/v1",
        "witness": {
            **asdict(witness),
            "payload": stable_jsonable(witness.payload),
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", default="route_certificate_sequence", choices=("route_certificate_sequence",))
    parser.add_argument("--format", default="json", choices=("json", "text"))
    parser.add_argument("--max-depth", type=int, default=2)
    parser.add_argument("--max-frontier", type=int, default=64)
    parser.add_argument("--target-manifest")
    parser.add_argument("--target-id")
    parser.add_argument("--feedback-mode", choices=("legacy", "stateful"), default="stateful")
    parser.add_argument("--minimize-derivation", choices=tuple(DERIVATION_BUILDERS))
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.minimize_derivation is not None:
        witness = minimize_case(args.minimize_derivation)
        if args.format == "json":
            print(json.dumps(_minimized_witness_json(witness), indent=2, sort_keys=True))
            return 0
        print(f"[{witness.target}] {witness.derivation}: {witness.outcome_label} ({witness.path_id}, len={witness.path_length})")
        return 0

    reports = explore_all_targets(
        max_depth=args.max_depth,
        max_frontier=args.max_frontier,
        target_manifest=args.target_manifest,
        target_id=args.target_id,
        feedback_mode=args.feedback_mode,
    )
    if args.format == "json":
        print(json.dumps(_reports_json(reports), indent=2, sort_keys=True))
        return 0
    for report in reports:
        print(
            f"[{report.target}] cases={report.total_cases} outcomes={report.unique_outcome_count} "
            f"paths={report.unique_path_count} states={report.unique_state_count} transitions={report.unique_transition_count}"
        )
        if report.reached_target_ids:
            print(f"  targets: {', '.join(report.reached_target_ids)}")
        for case in report.cases:
            print(f"  - depth={case.depth} {case.mutation}: {case.outcome_label} path={case.path_id} len={case.path_length}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
