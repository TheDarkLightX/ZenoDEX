from __future__ import annotations

"""Shared deterministic semantic-state feedback helpers for weird-machine exploration.

These helpers stay in the tooling layer. They do not participate in functional-
core execution or consensus-critical semantics.
"""

import copy
import hashlib
import json
import time
from dataclasses import asdict, dataclass, is_dataclass
from pathlib import Path
from typing import Any, Callable, Literal, TypedDict, cast
import re


FeedbackMode = Literal["legacy", "stateful"]
MutationFn = Callable[[object], object]
ExpandableFn = Callable[[object], bool]
TraceResult = tuple[str, str, int] | tuple[str, str, int, tuple[str, ...]]
TraceFn = Callable[[object], TraceResult]
SemanticStateFn = Callable[[object, str, str, tuple[str, ...], tuple[str, ...], tuple[str, ...], str], object]
ActionSummaryFn = Callable[[object, object, str], object]


class DangerousSurfaceDoc(TypedDict):
    id: str
    machine_family: str
    invariant_boundary: str
    action_grammar: str
    harnesses: list[str]
    trace_tokens: list[str]
    outcome_tokens: list[str]
    waypoint_tags: list[str]
    witness_ids: list[str]


class DangerousSurfaceManifestDoc(TypedDict):
    schema: str
    surfaces: list[DangerousSurfaceDoc]


@dataclass(frozen=True)
class DangerousSurface:
    id: str
    machine_family: str
    invariant_boundary: str
    action_grammar: str
    harnesses: tuple[str, ...]
    trace_tokens: tuple[str, ...]
    outcome_tokens: tuple[str, ...]
    waypoint_tags: tuple[str, ...]
    witness_ids: tuple[str, ...]


@dataclass(frozen=True)
class Mutation:
    name: str
    apply: MutationFn


@dataclass(frozen=True)
class TraceObservation:
    outcome_label: str
    path_id: str
    path_length: int
    line_trace: tuple[str, ...]
    payload_signature: str
    state_signature: str
    state_summary: object
    action_signature: str
    action_summary: object
    transition_signature: str
    target_hits: tuple[str, ...]
    waypoint_tags: tuple[str, ...]


@dataclass(frozen=True)
class ExplorationCase:
    mutation: str
    depth: int
    outcome_label: str
    path_id: str
    path_length: int
    state_signature: str
    state_summary: object
    action_signature: str
    action_summary: object
    transition_signature: str
    target_hits: tuple[str, ...]
    waypoint_tags: tuple[str, ...]
    payload: object | None = None


@dataclass(frozen=True)
class ExplorationTargetReport:
    harness_id: str
    target: str
    feedback_mode: FeedbackMode
    total_cases: int
    unique_outcome_count: int
    unique_path_count: int
    unique_state_count: int
    unique_transition_count: int
    reached_target_ids: tuple[str, ...]
    cases: tuple[ExplorationCase, ...]


@dataclass(frozen=True)
class FrontierEntry:
    priority: tuple[int, int, int, int, int, str, str, int]
    depth: int
    mutation_name: str
    payload: object
    observation: TraceObservation


@dataclass(frozen=True)
class HarnessRunSummary:
    harness_id: str
    reached_target_ids: tuple[str, ...]
    outcome_labels: tuple[str, ...]
    mutations: tuple[str, ...]


def stable_jsonable(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if is_dataclass(value) and not isinstance(value, type):
        return stable_jsonable(asdict(cast(Any, value)))
    if isinstance(value, dict):
        return {str(key): stable_jsonable(val) for key, val in sorted(value.items(), key=lambda item: str(item[0]))}
    if isinstance(value, (list, tuple)):
        return [stable_jsonable(item) for item in value]
    if isinstance(value, set):
        return sorted(stable_jsonable(item) for item in value)
    return repr(value)


def payload_signature(payload: object) -> str:
    canonical = json.dumps(stable_jsonable(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:16]


def _summary_signature(value: object) -> str:
    canonical = json.dumps(stable_jsonable(value), sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:16]


def hash_lines(lines: tuple[str, ...]) -> str:
    return hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()[:16]


def _classify_outcome(outcome_label: str) -> str:
    if outcome_label.startswith("ok"):
        return "ok"
    if outcome_label.startswith("reject:"):
        return "reject"
    if outcome_label.startswith("handled:"):
        return "handled"
    return outcome_label.split(":", 1)[0] or "unknown"


def _scalar_bucket(value: object) -> object:
    if value is None:
        return {"type": "none"}
    if isinstance(value, bool):
        return {"type": "bool", "value": value}
    if isinstance(value, int) and not isinstance(value, bool):
        if value < 0:
            bucket = "neg"
        elif value == 0:
            bucket = "zero"
        elif value == 1:
            bucket = "one"
        elif value <= 8:
            bucket = "small"
        elif value <= 1024:
            bucket = "medium"
        else:
            bucket = "large"
        return {"type": "int", "bucket": bucket}
    if isinstance(value, float):
        return {"type": "float", "repr": repr(value)}
    if isinstance(value, str):
        if not value:
            return {"type": "str", "shape": "empty"}
        if value.startswith("0x"):
            return {"type": "hex", "len": len(value) - 2}
        if value.startswith("reject:") or value.startswith("ok") or value.startswith("handled:"):
            return {"type": "outcome", "class": _classify_outcome(value)}
        return {"type": "str", "len": len(value)}
    return {"type": type(value).__name__}


def generic_shape_summary(value: object, *, max_depth: int = 2, max_items: int = 4) -> object:
    if max_depth <= 0:
        if isinstance(value, dict):
            return {"type": "dict", "len": len(value)}
        if isinstance(value, (list, tuple, set)):
            return {"type": type(value).__name__, "len": len(value)}
        return _scalar_bucket(value)
    if value is None or isinstance(value, (bool, int, float, str)):
        return _scalar_bucket(value)
    if is_dataclass(value) and not isinstance(value, type):
        return generic_shape_summary(asdict(cast(Any, value)), max_depth=max_depth, max_items=max_items)
    if isinstance(value, dict):
        items = list(sorted(value.items(), key=lambda item: str(item[0])))
        return {
            "type": "dict",
            "len": len(items),
            "keys": [str(key) for key, _ in items[:max_items]],
            "items": {
                str(key): generic_shape_summary(val, max_depth=max_depth - 1, max_items=max_items)
                for key, val in items[:max_items]
            },
        }
    if isinstance(value, (list, tuple)):
        rows = list(value)
        return {
            "type": type(value).__name__,
            "len": len(rows),
            "items": [generic_shape_summary(item, max_depth=max_depth - 1, max_items=max_items) for item in rows[:max_items]],
        }
    if isinstance(value, set):
        rows = sorted(stable_jsonable(item) for item in value)
        return {
            "type": "set",
            "len": len(rows),
            "items": [generic_shape_summary(item, max_depth=max_depth - 1, max_items=max_items) for item in rows[:max_items]],
        }
    return {"type": type(value).__name__, "repr": repr(value)}


def _default_semantic_state(
    *,
    payload: object,
    outcome_label: str,
    path_id: str,
    line_trace: tuple[str, ...],
    target_hits: tuple[str, ...],
    waypoint_tags: tuple[str, ...],
    harness_id: str,
) -> object:
    return {
        "harness_id": harness_id,
        "outcome_class": _classify_outcome(outcome_label),
        "path_id": path_id,
        "target_hits": list(target_hits),
        "waypoint_tags": list(waypoint_tags),
        "trace_tail": list(line_trace[-3:]),
        "payload_shape": generic_shape_summary(payload),
    }


def _default_action_summary(prev_payload: object, next_payload: object, mutation_name: str) -> object:
    return {
        "kind": mutation_name,
        "prev_shape": generic_shape_summary(prev_payload, max_depth=1),
        "next_shape": generic_shape_summary(next_payload, max_depth=1),
    }


def load_dangerous_surface_manifest(path: str | Path | None) -> tuple[DangerousSurface, ...]:
    if path is None:
        return ()
    raw = json.loads(Path(path).read_text(encoding="utf-8"))
    if raw.get("schema") != "zenodex/stateful-dangerous-surface-manifest/v1":
        raise ValueError("unsupported dangerous surface manifest schema")
    surfaces_raw = raw.get("surfaces")
    if not isinstance(surfaces_raw, list):
        raise ValueError("dangerous surface manifest surfaces must be a list")
    rows: list[DangerousSurface] = []
    for row in surfaces_raw:
        if not isinstance(row, dict):
            raise ValueError("dangerous surface rows must be objects")
        rows.append(
            DangerousSurface(
                id=_require_text(row.get("id"), name="surface.id"),
                machine_family=_require_text(row.get("machine_family"), name="surface.machine_family"),
                invariant_boundary=_require_text(row.get("invariant_boundary"), name="surface.invariant_boundary"),
                action_grammar=_require_text(row.get("action_grammar"), name="surface.action_grammar"),
                harnesses=_require_text_tuple(row.get("harnesses"), name="surface.harnesses"),
                trace_tokens=_require_text_tuple(row.get("trace_tokens", []), name="surface.trace_tokens"),
                outcome_tokens=_require_text_tuple(row.get("outcome_tokens", []), name="surface.outcome_tokens"),
                waypoint_tags=_require_text_tuple(row.get("waypoint_tags", []), name="surface.waypoint_tags"),
                witness_ids=_require_text_tuple(row.get("witness_ids", []), name="surface.witness_ids"),
            )
        )
    return tuple(sorted(rows, key=lambda row: row.id))


def build_trace_observation(
    *,
    harness_id: str,
    payload: object,
    trace_fn: TraceFn,
    dangerous_surfaces: tuple[DangerousSurface, ...],
    target_id: str | None,
    previous_state_signature: str | None = None,
    action_summary: object | None = None,
    semantic_state_fn: SemanticStateFn | None = None,
) -> TraceObservation:
    trace_result = trace_fn(payload)
    if len(trace_result) == 3:
        outcome_label, path_id, path_length = trace_result
        line_trace: tuple[str, ...] = ()
    else:
        outcome_label, path_id, path_length, line_trace = trace_result
    payload_sig = payload_signature(payload)
    target_hits, waypoint_tags = compute_target_hits(
        harness_id=harness_id,
        dangerous_surfaces=dangerous_surfaces,
        target_id=target_id,
        outcome_label=outcome_label,
        line_trace=line_trace,
    )
    raw_state = (
        semantic_state_fn(payload, outcome_label, path_id, line_trace, target_hits, waypoint_tags, harness_id)
        if semantic_state_fn is not None
        else _default_semantic_state(
            payload=payload,
            outcome_label=outcome_label,
            path_id=path_id,
            line_trace=line_trace,
            target_hits=target_hits,
            waypoint_tags=waypoint_tags,
            harness_id=harness_id,
        )
    )
    canonical_state = stable_jsonable(raw_state)
    state_sig = _summary_signature({"harness_id": harness_id, "semantic_state": canonical_state})
    canonical_action = stable_jsonable(action_summary if action_summary is not None else {"kind": "seed"})
    action_sig = _summary_signature(canonical_action)
    transition_sig = _summary_signature(
        {
            "pre": previous_state_signature or "ROOT",
            "action": canonical_action,
            "post": canonical_state,
        }
    )
    return TraceObservation(
        outcome_label=outcome_label,
        path_id=path_id,
        path_length=path_length,
        line_trace=line_trace,
        payload_signature=payload_sig,
        state_signature=state_sig,
        state_summary=canonical_state,
        action_signature=action_sig,
        action_summary=canonical_action,
        transition_signature=transition_sig,
        target_hits=target_hits,
        waypoint_tags=waypoint_tags,
    )


def compute_target_hits(
    *,
    harness_id: str,
    dangerous_surfaces: tuple[DangerousSurface, ...],
    target_id: str | None,
    outcome_label: str,
    line_trace: tuple[str, ...],
) -> tuple[tuple[str, ...], tuple[str, ...]]:
    hits: list[str] = []
    tags: set[str] = set()
    trace_text = "\n".join(line_trace)
    for surface in dangerous_surfaces:
        if target_id is not None and surface.id != target_id:
            continue
        if surface.harnesses and harness_id not in surface.harnesses:
            continue
        outcome_match = any(token in outcome_label for token in surface.outcome_tokens)
        trace_match = any(token in trace_text for token in surface.trace_tokens)
        if outcome_match or trace_match:
            hits.append(surface.id)
            tags.update(surface.waypoint_tags)
    return tuple(sorted(set(hits))), tuple(sorted(tags))


def frontier_priority(
    *,
    observation: TraceObservation,
    mutation_name: str,
    schedule_seq: int,
    feedback_mode: FeedbackMode,
    seen_states: set[str],
    seen_transitions: set[str],
    seen_pairs: set[tuple[str, str]],
) -> tuple[int, int, int, int, int, str, str, int]:
    if feedback_mode == "legacy":
        return (1, 1, 1, 1, -observation.path_length, mutation_name, observation.payload_signature, schedule_seq)
    target_rank = 0 if observation.target_hits else 1
    transition_rank = 0 if observation.transition_signature not in seen_transitions else 1
    state_rank = 0 if observation.state_signature not in seen_states else 1
    pair_rank = 0 if (observation.outcome_label, observation.path_id) not in seen_pairs else 1
    return (
        target_rank,
        transition_rank,
        state_rank,
        pair_rank,
        -observation.path_length,
        mutation_name,
        observation.payload_signature,
        schedule_seq,
    )


def explore_bounded_frontier(
    *,
    harness_id: str,
    seed: object,
    mutations: tuple[Mutation, ...],
    trace_fn: TraceFn,
    expandable: ExpandableFn,
    max_depth: int,
    max_frontier: int,
    feedback_mode: FeedbackMode,
    dangerous_surfaces: tuple[DangerousSurface, ...] = (),
    target_id: str | None = None,
    include_payloads: bool = False,
    semantic_state_fn: SemanticStateFn | None = None,
    action_summary_fn: ActionSummaryFn | None = None,
) -> ExplorationTargetReport:
    seed_payload = copy.deepcopy(seed)
    seen_payloads: set[str] = {payload_signature(seed_payload)}
    seen_pairs: set[tuple[str, str]] = set()
    seen_outcomes: set[str] = set()
    seen_paths: set[str] = set()
    seen_states: set[str] = set()
    seen_transitions: set[str] = set()
    reached_target_ids: set[str] = set()
    cases: list[ExplorationCase] = []

    seed_observation = build_trace_observation(
        harness_id=harness_id,
        payload=seed_payload,
        trace_fn=trace_fn,
        dangerous_surfaces=dangerous_surfaces,
        target_id=target_id,
        action_summary={"kind": "seed", "target": harness_id.split(":", 1)[-1]},
        semantic_state_fn=semantic_state_fn,
    )
    frontier: list[FrontierEntry] = [
        FrontierEntry(
            priority=frontier_priority(
                observation=seed_observation,
                mutation_name="valid_seed",
                schedule_seq=0,
                feedback_mode=feedback_mode,
                seen_states=seen_states,
                seen_transitions=seen_transitions,
                seen_pairs=seen_pairs,
            ),
            depth=0,
            mutation_name="valid_seed",
            payload=seed_payload,
            observation=seed_observation,
        )
    ]
    schedule_seq = 1
    explored = 0

    while frontier and explored < max_frontier:
        entry = frontier.pop(0)
        frontier.sort(key=lambda row: row.priority)
        explored += 1
        observation = entry.observation
        pair = (observation.outcome_label, observation.path_id)
        seen_states.add(observation.state_signature)
        seen_transitions.add(observation.transition_signature)
        seen_outcomes.add(observation.outcome_label)
        seen_paths.add(observation.path_id)
        reached_target_ids.update(observation.target_hits)
        if pair not in seen_pairs:
            seen_pairs.add(pair)
            cases.append(
                ExplorationCase(
                    mutation=entry.mutation_name,
                    depth=entry.depth,
                    outcome_label=observation.outcome_label,
                    path_id=observation.path_id,
                    path_length=observation.path_length,
                    state_signature=observation.state_signature,
                    state_summary=observation.state_summary,
                    action_signature=observation.action_signature,
                    action_summary=observation.action_summary,
                    transition_signature=observation.transition_signature,
                    target_hits=observation.target_hits,
                    waypoint_tags=observation.waypoint_tags,
                    payload=copy.deepcopy(entry.payload) if include_payloads else None,
                )
            )

        if entry.depth >= max_depth or not expandable(entry.payload):
            continue

        for order, mutation in enumerate(mutations):
            try:
                next_payload = mutation.apply(copy.deepcopy(entry.payload))
            except Exception:
                continue
            next_payload_sig = payload_signature(next_payload)
            if next_payload_sig in seen_payloads:
                continue
            seen_payloads.add(next_payload_sig)
            next_name = mutation.name if entry.mutation_name == "valid_seed" else f"{entry.mutation_name}->{mutation.name}"
            action_summary = (
                action_summary_fn(entry.payload, next_payload, mutation.name)
                if action_summary_fn is not None
                else _default_action_summary(entry.payload, next_payload, mutation.name)
            )
            next_observation = build_trace_observation(
                harness_id=harness_id,
                payload=next_payload,
                trace_fn=trace_fn,
                dangerous_surfaces=dangerous_surfaces,
                target_id=target_id,
                previous_state_signature=entry.observation.state_signature,
                action_summary=action_summary,
                semantic_state_fn=semantic_state_fn,
            )
            frontier.append(
                FrontierEntry(
                    priority=frontier_priority(
                        observation=next_observation,
                        mutation_name=next_name,
                        schedule_seq=schedule_seq + order,
                        feedback_mode=feedback_mode,
                        seen_states=seen_states,
                        seen_transitions=seen_transitions,
                        seen_pairs=seen_pairs,
                    ),
                    depth=entry.depth + 1,
                    mutation_name=next_name,
                    payload=next_payload,
                    observation=next_observation,
                )
            )
        frontier.sort(key=lambda row: row.priority)
        schedule_seq += len(mutations)

    cases_sorted = tuple(sorted(cases, key=lambda case: (case.outcome_label, case.depth, case.mutation, case.path_id)))
    return ExplorationTargetReport(
        harness_id=harness_id,
        target=harness_id.split(":", 1)[-1],
        feedback_mode=feedback_mode,
        total_cases=len(cases_sorted),
        unique_outcome_count=len(seen_outcomes),
        unique_path_count=len(seen_paths),
        unique_state_count=len(seen_states),
        unique_transition_count=len(seen_transitions),
        reached_target_ids=tuple(sorted(reached_target_ids)),
        cases=cases_sorted,
    )


def report_to_json(report: ExplorationTargetReport) -> dict[str, Any]:
    raw = asdict(report)
    raw["cases"] = [
        {
            **{key: stable_jsonable(value) for key, value in case.items()},
        }
        for case in cast(list[dict[str, Any]], raw["cases"])
    ]
    return raw


def load_report_payload(path: str | Path) -> dict[str, Any]:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def build_introspection_report(
    *,
    dangerous_surfaces: tuple[DangerousSurface, ...],
    shared_witness_index: dict[str, Any] | None,
    report_payloads: list[dict[str, Any]],
    target_id: str | None = None,
) -> dict[str, Any]:
    witness_by_surface: dict[str, list[str]] = {surface.id: [] for surface in dangerous_surfaces}
    reached_by_surface: dict[str, set[str]] = {surface.id: set() for surface in dangerous_surfaces}
    ran_harnesses: set[str] = set()
    report_count = 0

    for payload in report_payloads:
        rows = _iter_report_rows(payload)
        report_count += len(rows)
        for report in rows:
            harness_id = _require_text(report.get("harness_id"), name="report.harness_id")
            ran_harnesses.add(harness_id)
            for surface_id in cast(list[str], report.get("reached_target_ids", [])):
                if surface_id in reached_by_surface:
                    reached_by_surface[surface_id].add(harness_id)

    unique_witness_ids: set[str] = set()
    if shared_witness_index is not None:
        for witness in _iter_witness_rows(shared_witness_index):
            witness_id = _require_text(witness.get("id"), name="witness.id")
            for surface in dangerous_surfaces:
                if witness_id in surface.witness_ids:
                    unique_witness_ids.add(witness_id)
                    witness_by_surface[surface.id].append(witness_id)
                    reached_by_surface[surface.id].add(f"witness:{witness_id}")

    statuses: list[dict[str, Any]] = []
    counts = {status: 0 for status in ("unharnessed", "harnessed_unreached", "reached_no_witness", "witnessed")}
    for surface in dangerous_surfaces:
        if target_id is not None and surface.id != target_id:
            continue
        witness_ids = sorted(set(witness_by_surface.get(surface.id, [])))
        reached_by = sorted(reached_by_surface.get(surface.id, set()))
        harnessed = bool(set(surface.harnesses) & ran_harnesses) or bool(reached_by)
        reached = bool(reached_by)
        if witness_ids:
            status = "witnessed"
        elif reached:
            status = "reached_no_witness"
        elif harnessed:
            status = "harnessed_unreached"
        else:
            status = "unharnessed"
        counts[status] += 1
        statuses.append(
            {
                "surface_id": surface.id,
                "machine_family": surface.machine_family,
                "invariant_boundary": surface.invariant_boundary,
                "status": status,
                "harnesses": list(surface.harnesses),
                "reached_by": reached_by,
                "witness_ids": witness_ids,
                "waypoint_tags": list(surface.waypoint_tags),
            }
        )
    atlas_status = "draft"
    if statuses:
        if counts["witnessed"] == len(statuses):
            atlas_status = "complete"
        elif counts["witnessed"] > 0 or counts["reached_no_witness"] > 0:
            atlas_status = "partial"
    return {
        "schema": "zenodex/acceptance-tcb-fuzz-introspection/v1",
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "surface_count": len(statuses),
        "target_count": len(statuses),
        "report_count": report_count,
        "witness_count": len(unique_witness_ids),
        "atlas_status": atlas_status,
        "status_counts": counts,
        "surfaces": statuses,
    }


_REJECT_STEP_RE = re.compile(r"^reject:step=\d+:(?P<reason>.+)$")
_REJECT_RE = re.compile(r"^reject:(?P<reason>.+)$")
_HANDLED_RE = re.compile(r"^handled:(?P<status>[^:]+):(?P<reason>.+)$")


def _guard_reason_from_outcome_label(outcome_label: str) -> str:
    for regex in (_REJECT_STEP_RE, _REJECT_RE):
        match = regex.match(outcome_label)
        if match is not None:
            return _require_text(match.group("reason"), name="guard.reason")
    handled = _HANDLED_RE.match(outcome_label)
    if handled is not None:
        return _require_text(handled.group("reason"), name="guard.reason")
    return outcome_label


def _guard_family_from_reason(reason: str) -> str:
    lowered = reason.lower()
    if "unauthorized" in lowered or "proof_flags" in lowered:
        return "authorization_guard"
    if "nonce" in lowered:
        return "nonce_replay_guard"
    if "source_id not allowlisted" in lowered:
        return "attestation_policy_guard"
    if "packet_hash mismatch" in lowered:
        return "attestation_packet_binding_guard"
    if "attestation is stale" in lowered or "signed_at_epoch is in the future" in lowered:
        return "attestation_temporal_guard"
    if "signature" in lowered:
        return "signature_guard"
    if "candidate_set_hash" in lowered or "winner_index" in lowered or "winner_quote" in lowered or "candidate list" in lowered or "argmin" in lowered:
        return "route_canonicalization_guard"
    if "canonical_route_certificate" in lowered or "bad_canonical_route_certificate" in lowered:
        return "route_certificate_binding_guard"
    if "missing_pool_fingerprint" in lowered or "unexpected_pool_fingerprint" in lowered:
        return "receipt_pool_envelope_guard"
    if "pool_snapshot_mismatch" in lowered or "missing_pool" in lowered:
        return "snapshot_freshness_guard"
    if "missing_receipt_hash" in lowered or "hash_mismatch" in lowered:
        return "receipt_transport_guard"
    if "settlement mismatch" in lowered:
        return "settlement_freshness_guard"
    return "other_guard"


def build_guard_attribution_report(
    *,
    dangerous_surfaces: tuple[DangerousSurface, ...],
    shared_witness_index: dict[str, Any] | None,
    target_id: str | None = None,
) -> dict[str, Any]:
    surface_by_witness: dict[str, set[str]] = {}
    machine_families_by_witness: dict[str, set[str]] = {}
    for surface in dangerous_surfaces:
        if target_id is not None and surface.id != target_id:
            continue
        for witness_id in surface.witness_ids:
            surface_by_witness.setdefault(witness_id, set()).add(surface.id)
            machine_families_by_witness.setdefault(witness_id, set()).add(surface.machine_family)

    rows: list[dict[str, Any]] = []
    guard_groups: dict[str, dict[str, Any]] = {}
    for witness in _iter_witness_rows(shared_witness_index or {}):
        witness_id = _require_text(witness.get("id"), name="witness.id")
        surface_ids = sorted(surface_by_witness.get(witness_id, set()))
        if target_id is not None and not surface_ids:
            continue
        outcome_label = _require_text(witness.get("outcome_label"), name="witness.outcome_label")
        guard_reason = _guard_reason_from_outcome_label(outcome_label)
        guard_family = _guard_family_from_reason(guard_reason)
        row = {
            "witness_id": witness_id,
            "surface_ids": surface_ids,
            "machine_families": sorted(machine_families_by_witness.get(witness_id, set())),
            "guard_reason": guard_reason,
            "guard_family": guard_family,
            "outcome_label": outcome_label,
            "derivation": _require_text(witness.get("derivation"), name="witness.derivation"),
            "path_length": int(witness.get("path_length", 0)),
            "witness_out": witness.get("witness_out"),
        }
        rows.append(row)
        group = guard_groups.setdefault(
            guard_family,
            {
                "guard_family": guard_family,
                "witness_ids": set(),
                "surface_ids": set(),
                "machine_families": set(),
                "sample_reasons": [],
                "max_path_length": 0,
                "min_path_length": None,
            },
        )
        cast(set[str], group["witness_ids"]).add(witness_id)
        cast(set[str], group["surface_ids"]).update(surface_ids)
        row_machine_families = cast(list[str], row["machine_families"])
        cast(set[str], group["machine_families"]).update(row_machine_families)
        if guard_reason not in cast(list[str], group["sample_reasons"]) and len(cast(list[str], group["sample_reasons"])) < 4:
            cast(list[str], group["sample_reasons"]).append(guard_reason)
        path_length = int(cast(int, row["path_length"]))
        group["max_path_length"] = max(int(group["max_path_length"]), path_length)
        min_path = group["min_path_length"]
        if min_path is None or path_length < int(min_path):
            group["min_path_length"] = path_length

    guard_rows = [
        {
            "guard_family": group["guard_family"],
            "witness_count": len(cast(set[str], group["witness_ids"])),
            "witness_ids": sorted(cast(set[str], group["witness_ids"])),
            "surface_ids": sorted(cast(set[str], group["surface_ids"])),
            "machine_families": sorted(cast(set[str], group["machine_families"])),
            "sample_reasons": cast(list[str], group["sample_reasons"]),
            "max_path_length": int(group["max_path_length"]),
            "min_path_length": int(group["min_path_length"] or 0),
        }
        for group in guard_groups.values()
    ]
    guard_rows.sort(key=lambda row: (-int(row["witness_count"]), row["guard_family"]))
    rows.sort(key=lambda row: (row["guard_family"], row["witness_id"]))
    return {
        "schema": "zenodex/acceptance-tcb-guard-attribution/v1",
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "witness_count": len(rows),
        "guard_family_count": len(guard_rows),
        "guards": guard_rows,
        "witnesses": rows,
    }


_SURFACE_PROXIMITY_WEIGHT: dict[str, int] = {
    "stale_settlement_boundary": 52,
    "quote_receipt_certificate_boundary": 48,
    "route_canonicalization_boundary": 46,
    "settlement_attestation_policy_boundary": 44,
    "nonce_replay_guard": 40,
    "stale_quote_receipt_boundary": 38,
    "quote_receipt_pool_envelope_boundary": 34,
    "operations_signature_reuse_boundary": 32,
    "quote_receipt_transport_boundary": 28,
    "api_request_authorization_boundary": 18,
}


_GUARD_PROXIMITY_WEIGHT: dict[str, int] = {
    "route_canonicalization_guard": 18,
    "route_certificate_binding_guard": 16,
    "settlement_freshness_guard": 17,
    "attestation_temporal_guard": 15,
    "attestation_packet_binding_guard": 15,
    "attestation_policy_guard": 14,
    "nonce_replay_guard": 14,
    "snapshot_freshness_guard": 13,
    "signature_guard": 10,
    "receipt_pool_envelope_guard": 10,
    "receipt_transport_guard": 8,
    "authorization_guard": 6,
    "other_guard": 4,
}


def _surface_proximity_weight(surface_ids: list[str]) -> int:
    if not surface_ids:
        return 10
    return max(_SURFACE_PROXIMITY_WEIGHT.get(surface_id, 12) for surface_id in surface_ids)


def _proximity_flags(*, derivation: str, outcome_label: str, surface_ids: list[str], guard_family: str) -> dict[str, bool]:
    lowered_derivation = derivation.lower()
    lowered_outcome = outcome_label.lower()
    state_carryover = any(
        token in lowered_derivation or token in lowered_outcome
        for token in ("replay", "stale", "future", "warmup", "crossbatch", "validthen", "drift")
    )
    repair_after_tamper = any(token in lowered_derivation for token in ("rehash", "repair", "rebuild"))
    post_verification_binding = guard_family in {
        "route_canonicalization_guard",
        "route_certificate_binding_guard",
        "attestation_packet_binding_guard",
        "receipt_pool_envelope_guard",
    }
    value_or_ordering_path = any(
        surface_id in {
            "stale_settlement_boundary",
            "quote_receipt_certificate_boundary",
            "route_canonicalization_boundary",
            "settlement_attestation_policy_boundary",
            "stale_quote_receipt_boundary",
        }
        for surface_id in surface_ids
    )
    return {
        "state_carryover": state_carryover,
        "repair_after_tamper": repair_after_tamper,
        "post_verification_binding": post_verification_binding,
        "value_or_ordering_path": value_or_ordering_path,
    }


def _proximity_band(score: int) -> str:
    if score >= 86:
        return "critical"
    if score >= 66:
        return "high"
    if score >= 46:
        return "medium"
    return "low"


def build_exploit_proximity_report(
    *,
    dangerous_surfaces: tuple[DangerousSurface, ...],
    shared_witness_index: dict[str, Any] | None,
    target_id: str | None = None,
) -> dict[str, Any]:
    surface_by_witness: dict[str, set[str]] = {}
    machine_families_by_witness: dict[str, set[str]] = {}
    for surface in dangerous_surfaces:
        if target_id is not None and surface.id != target_id:
            continue
        for witness_id in surface.witness_ids:
            surface_by_witness.setdefault(witness_id, set()).add(surface.id)
            machine_families_by_witness.setdefault(witness_id, set()).add(surface.machine_family)

    rows: list[dict[str, Any]] = []
    for witness in _iter_witness_rows(shared_witness_index or {}):
        witness_id = _require_text(witness.get("id"), name="witness.id")
        surface_ids = sorted(surface_by_witness.get(witness_id, set()))
        if target_id is not None and not surface_ids:
            continue
        if not surface_ids:
            continue
        outcome_label = _require_text(witness.get("outcome_label"), name="witness.outcome_label")
        derivation = _require_text(witness.get("derivation"), name="witness.derivation")
        guard_reason = _guard_reason_from_outcome_label(outcome_label)
        guard_family = _guard_family_from_reason(guard_reason)
        flags = _proximity_flags(
            derivation=derivation,
            outcome_label=outcome_label,
            surface_ids=surface_ids,
            guard_family=guard_family,
        )
        minimized_size = int(witness.get("minimized_size", 0))
        score = _surface_proximity_weight(surface_ids) + _GUARD_PROXIMITY_WEIGHT.get(guard_family, 4)
        if outcome_label.startswith("reject:step="):
            score += 8
        elif outcome_label.startswith("reject:"):
            score += 5
        if flags["state_carryover"]:
            score += 12
        if flags["repair_after_tamper"]:
            score += 10
        if flags["post_verification_binding"]:
            score += 8
        if flags["value_or_ordering_path"]:
            score += 8
        if len(surface_ids) > 1:
            score += (len(surface_ids) - 1) * 4
        if minimized_size > 0 and minimized_size <= 256:
            score += 6
        elif minimized_size <= 1024:
            score += 4
        elif minimized_size <= 4096:
            score += 2
        row = {
            "witness_id": witness_id,
            "surface_ids": surface_ids,
            "machine_families": sorted(machine_families_by_witness.get(witness_id, set())),
            "guard_family": guard_family,
            "guard_reason": guard_reason,
            "derivation": derivation,
            "outcome_label": outcome_label,
            "target": witness.get("target"),
            "campaign_dir": witness.get("campaign_dir"),
            "campaign_report": witness.get("campaign_report"),
            "witness_out": witness.get("witness_out"),
            "minimized_size": minimized_size,
            "proximity_score": score,
            "severity_band": _proximity_band(score),
            "flags": flags,
        }
        rows.append(row)

    unique_rows: dict[str, dict[str, Any]] = {}
    for row in rows:
        witness_id = _require_text(row["witness_id"], name="proximity.witness_id")
        current = unique_rows.get(witness_id)
        candidate_key = (
            int(row["proximity_score"]),
            -int(row.get("minimized_size", 0)),
            _require_text(str(row.get("campaign_dir") or "-"), name="proximity.campaign_dir"),
        )
        if current is None:
            unique_rows[witness_id] = row
            continue
        current_key = (
            int(current["proximity_score"]),
            -int(current.get("minimized_size", 0)),
            _require_text(str(current.get("campaign_dir") or "-"), name="proximity.campaign_dir"),
        )
        if candidate_key > current_key:
            unique_rows[witness_id] = row

    deduped_rows = sorted(unique_rows.values(), key=lambda row: (-int(row["proximity_score"]), row["witness_id"]))
    hotspot_groups: dict[str, dict[str, Any]] = {}
    for row in deduped_rows:
        hotspot_key = cast(list[str], row["surface_ids"])[0]
        group = hotspot_groups.setdefault(
            hotspot_key,
            {
                "surface_id": hotspot_key,
                "machine_families": set(),
                "guard_families": set(),
                "witness_rows": [],
            },
        )
        cast(set[str], group["machine_families"]).update(cast(list[str], row["machine_families"]))
        cast(set[str], group["guard_families"]).add(_require_text(row["guard_family"], name="proximity.guard_family"))
        cast(list[dict[str, Any]], group["witness_rows"]).append(row)

    hotspot_rows: list[dict[str, Any]] = []
    for hotspot in hotspot_groups.values():
        witness_rows = cast(list[dict[str, Any]], hotspot["witness_rows"])
        witness_rows.sort(key=lambda row: (-int(row["proximity_score"]), row["witness_id"]))
        top = witness_rows[0]
        hotspot_rows.append(
            {
                "surface_id": hotspot["surface_id"],
                "machine_families": sorted(cast(set[str], hotspot["machine_families"])),
                "guard_families": sorted(cast(set[str], hotspot["guard_families"])),
                "witness_count": len(witness_rows),
                "top_witness_id": top["witness_id"],
                "top_guard_family": top["guard_family"],
                "top_proximity_score": top["proximity_score"],
                "severity_band": top["severity_band"],
            }
        )
    hotspot_rows.sort(key=lambda row: (-int(row["top_proximity_score"]), row["surface_id"]))
    return {
        "schema": "zenodex/acceptance-tcb-exploit-proximity/v1",
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "witness_count": len(deduped_rows),
        "hotspot_count": len(hotspot_rows),
        "top_witnesses": deduped_rows[:10],
        "hotspots": hotspot_rows,
    }


def build_weird_machine_atlas(
    *,
    dangerous_surfaces: tuple[DangerousSurface, ...],
    shared_witness_index: dict[str, Any] | None,
    report_payloads: list[dict[str, Any]],
    target_id: str | None = None,
) -> dict[str, Any]:
    witness_rows = list(_iter_witness_rows(shared_witness_index or {}))
    cases_by_surface: dict[str, list[dict[str, Any]]] = {surface.id: [] for surface in dangerous_surfaces}
    for payload in report_payloads:
        for report in _iter_report_rows(payload):
            harness_id = _require_text(report.get("harness_id"), name="report.harness_id")
            for case in cast(list[dict[str, Any]], report.get("cases", [])):
                for surface_id in cast(list[str], case.get("target_hits", [])):
                    if surface_id in cases_by_surface:
                        tagged = dict(case)
                        tagged["harness_id"] = harness_id
                        cases_by_surface[surface_id].append(tagged)

    entries: list[dict[str, Any]] = []
    for surface in dangerous_surfaces:
        if target_id is not None and surface.id != target_id:
            continue
        related_witnesses = [row for row in witness_rows if _require_text(row.get("id"), name="witness.id") in surface.witness_ids]
        related_cases = cases_by_surface.get(surface.id, [])
        status = "witnessed" if related_witnesses else ("reached" if related_cases else "draft")
        warmup = "none"
        if related_witnesses:
            warmup = _require_text(related_witnesses[0].get("derivation", ""), name="witness.derivation")
        elif related_cases:
            warmup = _require_text(related_cases[0].get("mutation", ""), name="case.mutation")
        entries.append(
            {
                "surface_id": surface.id,
                "machine_family": surface.machine_family,
                "warmup_summary": warmup,
                "action_grammar": surface.action_grammar,
                "target_surface_crossed": surface.id,
                "invariant_boundary": surface.invariant_boundary,
                "witness_status": status,
                "sample_outcomes": sorted(
                    {
                        _require_text(case.get("outcome_label", ""), name="case.outcome_label")
                        for case in related_cases[:4]
                    }
                ),
                "sample_witnesses": sorted(
                    {
                        _require_text(row.get("id", ""), name="witness.id")
                        for row in related_witnesses[:4]
                    }
                ),
                "reached_harnesses": sorted(
                    {
                        _require_text(case.get("harness_id", ""), name="case.harness_id")
                        for case in related_cases
                    }
                ),
                "sample_state_summaries": [stable_jsonable(case.get("state_summary")) for case in related_cases[:2]],
                "sample_action_summaries": [stable_jsonable(case.get("action_summary")) for case in related_cases[:2]],
            }
        )
    atlas_status = "draft"
    if entries:
        statuses = {entry["witness_status"] for entry in entries}
        if statuses == {"witnessed"}:
            atlas_status = "complete"
        elif "witnessed" in statuses or "reached" in statuses:
            atlas_status = "partial"
    return {
        "schema": "zenodex/acceptance-tcb-weird-machine-atlas/v1",
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "atlas_status": atlas_status,
        "entry_count": len(entries),
        "witnessed_count": sum(1 for entry in entries if entry["witness_status"] == "witnessed"),
        "entries": entries,
    }


def build_surface_suggestions(
    *,
    dangerous_surfaces: tuple[DangerousSurface, ...],
    shared_witness_index: dict[str, Any] | None,
    report_payloads: list[dict[str, Any]],
    target_id: str | None = None,
) -> dict[str, Any]:
    surface_by_id = {surface.id: surface for surface in dangerous_surfaces}
    present_witness_ids = {
        _require_text(row.get("id"), name="witness.id") for row in _iter_witness_rows(shared_witness_index or {})
    }
    suggestions: dict[tuple[str, ...], dict[str, Any]] = {}
    report_count = 0

    def _entry_for(surface_ids: tuple[str, ...]) -> dict[str, Any]:
        entry = suggestions.get(surface_ids)
        if entry is None:
            entry = {
                "surface_ids": surface_ids,
                "machine_families": {surface_by_id[surface_id].machine_family for surface_id in surface_ids},
                "shared_harnesses": set(),
                "shared_waypoint_tags": set(),
                "witness_ids": set(),
                "sample_outcomes": [],
                "sample_action_summaries": [],
                "sample_state_summaries": [],
                "report_support_count": 0,
                "multi_hit_case_count": 0,
            }
            suggestions[surface_ids] = entry
        return entry

    def _append_unique_sample(rows: list[Any], value: Any, *, limit: int = 3) -> None:
        stable = stable_jsonable(value)
        if stable in rows:
            return
        if len(rows) < limit:
            rows.append(stable)

    for payload in report_payloads:
        rows = _iter_report_rows(payload)
        report_count += len(rows)
        for report in rows:
            harness_id = _require_text(report.get("harness_id"), name="report.harness_id")
            reached = tuple(
                sorted(
                    {
                        _require_text(surface_id, name="report.reached_target_ids[]")
                        for surface_id in cast(list[str], report.get("reached_target_ids", []))
                        if surface_id in surface_by_id and (target_id is None or surface_id == target_id)
                    }
                )
            )
            if len(reached) >= 2:
                entry = _entry_for(reached)
                entry["report_support_count"] += 1
                cast(set[str], entry["shared_harnesses"]).add(harness_id)
                cast(set[str], entry["shared_waypoint_tags"]).update(
                    tag for surface_id in reached for tag in surface_by_id[surface_id].waypoint_tags
                )
                cast(set[str], entry["witness_ids"]).update(
                    witness_id
                    for surface_id in reached
                    for witness_id in surface_by_id[surface_id].witness_ids
                    if witness_id in present_witness_ids
                )

            for case in cast(list[dict[str, Any]], report.get("cases", [])):
                hits = tuple(
                    sorted(
                        {
                            _require_text(surface_id, name="case.target_hits[]")
                            for surface_id in cast(list[str], case.get("target_hits", []))
                            if surface_id in surface_by_id and (target_id is None or surface_id == target_id)
                        }
                    )
                )
                if len(hits) < 2:
                    continue
                entry = _entry_for(hits)
                entry["multi_hit_case_count"] += 1
                cast(set[str], entry["shared_harnesses"]).add(harness_id)
                cast(set[str], entry["shared_waypoint_tags"]).update(
                    tag for surface_id in hits for tag in surface_by_id[surface_id].waypoint_tags
                )
                cast(set[str], entry["witness_ids"]).update(
                    witness_id
                    for surface_id in hits
                    for witness_id in surface_by_id[surface_id].witness_ids
                    if witness_id in present_witness_ids
                )
                _append_unique_sample(cast(list[Any], entry["sample_outcomes"]), _require_text(case.get("outcome_label"), name="case.outcome_label"))
                _append_unique_sample(cast(list[Any], entry["sample_action_summaries"]), case.get("action_summary"))
                _append_unique_sample(cast(list[Any], entry["sample_state_summaries"]), case.get("state_summary"))

    suggestion_rows: list[dict[str, Any]] = []
    for surface_ids, entry in suggestions.items():
        report_support_count = int(entry["report_support_count"])
        multi_hit_case_count = int(entry["multi_hit_case_count"])
        witness_ids = sorted(cast(set[str], entry["witness_ids"]))
        shared_harnesses = sorted(cast(set[str], entry["shared_harnesses"]))
        shared_waypoint_tags = sorted(cast(set[str], entry["shared_waypoint_tags"]))
        confidence = "low"
        if multi_hit_case_count > 0 and witness_ids:
            confidence = "high"
        elif multi_hit_case_count > 0 or report_support_count > 1:
            confidence = "medium"
        kind = "cross_surface_composition" if multi_hit_case_count > 0 else "shared_harness_overlap"
        actionability = "overlap_only"
        if multi_hit_case_count > 0:
            actionability = "candidate"
            if len(shared_harnesses) == 1 and report_support_count == 1:
                actionability = "already_in_harness"
        score = len(surface_ids) * 100 + multi_hit_case_count * 10 + report_support_count * 5 + len(witness_ids)
        if actionability == "already_in_harness":
            score -= 250
        suggestion_rows.append(
            {
                "suggestion_id": "compose:" + "+".join(surface_ids),
                "kind": kind,
                "actionability": actionability,
                "surface_ids": list(surface_ids),
                "machine_families": sorted(cast(set[str], entry["machine_families"])),
                "shared_harnesses": shared_harnesses,
                "shared_waypoint_tags": shared_waypoint_tags,
                "witness_ids": witness_ids,
                "report_support_count": report_support_count,
                "multi_hit_case_count": multi_hit_case_count,
                "confidence": confidence,
                "score": score,
                "rationale": (
                    f"{kind} supported by {multi_hit_case_count} multi-hit case(s) across "
                    f"{len(shared_harnesses)} harness(es) and {len(witness_ids)} witness id(s)."
                ),
                "sample_outcomes": cast(list[Any], entry["sample_outcomes"]),
                "sample_action_summaries": cast(list[Any], entry["sample_action_summaries"]),
                "sample_state_summaries": cast(list[Any], entry["sample_state_summaries"]),
            }
        )

    suggestion_rows.sort(key=lambda row: (-int(row["score"]), row["suggestion_id"]))
    return {
        "schema": "zenodex/acceptance-tcb-surface-suggestions/v1",
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "report_count": report_count,
        "suggestion_count": len(suggestion_rows),
        "suggestions": suggestion_rows,
    }


def _iter_report_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    reports = payload.get("reports", [])
    if not isinstance(reports, list):
        return []
    return [row for row in reports if isinstance(row, dict)]


def _iter_witness_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    witnesses = payload.get("witnesses", [])
    if not isinstance(witnesses, list):
        return []
    return [row for row in witnesses if isinstance(row, dict)]


def _require_text(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{name} must be a non-empty string")
    return value.strip()


def _require_text_tuple(value: object, *, name: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise ValueError(f"{name} must be a list")
    rows: list[str] = []
    for idx, item in enumerate(value):
        if not isinstance(item, str) or not item.strip():
            raise ValueError(f"{name}[{idx}] must be a non-empty string")
        rows.append(item.strip())
    return tuple(rows)
