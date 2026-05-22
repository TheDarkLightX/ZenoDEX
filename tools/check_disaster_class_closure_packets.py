#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.check_disaster_shape_taxonomy_crosswalk import (
    DEFAULT_CROSSWALK,
    check_crosswalk,
)
from tools.disaster_shape_types import (
    AxisId,
    BadTracePredicate,
    ClosurePacket,
    ClosurePacketId,
    CrosswalkEntryId,
)


SCHEMA = "zenodex/disaster-class-closure-packets/v1"
DEFAULT_PACKETS = REPO_ROOT / "tools" / "disaster_class_closure_packets.json"
REQUIRED_GLOBAL_THEOREMS = {"class_closure", "axis_rejection", "immunity"}


def _load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as fh:
        payload = json.load(fh)
    if not isinstance(payload, dict):
        raise TypeError(f"{path} root must be a JSON object")
    return payload


def _crosswalk_entry_axes(crosswalk_path: Path) -> dict[CrosswalkEntryId, set[AxisId]]:
    payload = _load_json(crosswalk_path)
    entries = payload.get("entries", [])
    if not isinstance(entries, list):
        return {}
    result: dict[CrosswalkEntryId, set[AxisId]] = {}
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        entry_id = entry.get("id")
        axes = entry.get("mapped_axis_ids")
        if isinstance(entry_id, str) and isinstance(axes, list):
            result[CrosswalkEntryId(entry_id)] = {
                AxisId(axis) for axis in axes if isinstance(axis, str)
            }
    return result


def _parse_bad_trace_predicate(value: object) -> BadTracePredicate | None:
    if not isinstance(value, dict):
        return None
    name = value.get("name")
    state_scope = value.get("state_scope")
    conditions = value.get("conditions")
    if not isinstance(name, str) or not name:
        return None
    if not isinstance(state_scope, list) or not all(
        isinstance(item, str) and item for item in state_scope
    ):
        return None
    if not isinstance(conditions, list) or not all(
        isinstance(item, str) and item for item in conditions
    ):
        return None
    return BadTracePredicate(
        name=name,
        state_scope=tuple(state_scope),
        conditions=tuple(conditions),
    )


def _parse_closure_packet(value: object) -> ClosurePacket | None:
    if not isinstance(value, dict):
        return None
    packet_id = value.get("id")
    crosswalk_entry_id = value.get("crosswalk_entry_id")
    predicate = _parse_bad_trace_predicate(value.get("bad_trace_predicate"))
    closure_obligations = value.get("closure_obligations")
    if not isinstance(packet_id, str) or not packet_id:
        return None
    if not isinstance(crosswalk_entry_id, str) or not crosswalk_entry_id:
        return None
    if predicate is None:
        return None
    if not isinstance(closure_obligations, list) or not all(
        isinstance(item, str) and item for item in closure_obligations
    ):
        return None
    return ClosurePacket(
        packet_id=ClosurePacketId(packet_id),
        crosswalk_entry_id=CrosswalkEntryId(crosswalk_entry_id),
        bad_trace_predicate=predicate,
        closure_obligations=tuple(closure_obligations),
    )


def check_closure_packets(
    packet_path: Path = DEFAULT_PACKETS,
    *,
    crosswalk_path: Path = DEFAULT_CROSSWALK,
) -> dict[str, Any]:
    payload = _load_json(packet_path)
    crosswalk_result = check_crosswalk(crosswalk_path)
    crosswalk_axes = _crosswalk_entry_axes(crosswalk_path)
    crosswalk_entry_ids: set[CrosswalkEntryId] = set(crosswalk_axes)

    errors: list[str] = []
    warnings: list[str] = []

    if not crosswalk_result["ok"]:
        errors.append("crosswalk checker must pass before closure packets can be checked")
        errors.extend(f"crosswalk: {error}" for error in crosswalk_result["errors"])

    if payload.get("schema") != SCHEMA:
        errors.append(f"schema must be {SCHEMA!r}")

    theorem_template = payload.get("global_theorem_template")
    if not isinstance(theorem_template, dict):
        errors.append("global_theorem_template must be an object")
    else:
        missing = sorted(REQUIRED_GLOBAL_THEOREMS - set(theorem_template))
        if missing:
            errors.append(f"global_theorem_template missing theorem(s): {', '.join(missing)}")
        for theorem_name in REQUIRED_GLOBAL_THEOREMS & set(theorem_template):
            value = theorem_template.get(theorem_name)
            if not isinstance(value, str) or "trace" not in value:
                errors.append(f"global_theorem_template.{theorem_name} must be a trace theorem string")

    packets = payload.get("packets")
    if not isinstance(packets, list) or not packets:
        errors.append("packets must be a non-empty list")
        packets = []

    seen_packet_ids: set[ClosurePacketId] = set()
    covered_entry_ids: set[CrosswalkEntryId] = set()
    total_conditions = 0
    total_obligations = 0
    exact_axis_bindings = 0

    for idx, packet in enumerate(packets):
        if not isinstance(packet, dict):
            errors.append(f"packets[{idx}] must be an object")
            continue
        typed_packet = _parse_closure_packet(packet)
        packet_id = packet.get("id")
        if not isinstance(packet_id, str) or not packet_id:
            errors.append(f"packets[{idx}].id must be a non-empty string")
            packet_id = f"<packet-{idx}>"
        typed_packet_id = ClosurePacketId(packet_id)
        if typed_packet_id in seen_packet_ids:
            errors.append(f"duplicate packet id: {packet_id}")
        seen_packet_ids.add(typed_packet_id)
        if typed_packet is None:
            errors.append(f"{packet_id} is not a fully typed closure packet")

        entry_id = packet.get("crosswalk_entry_id")
        if not isinstance(entry_id, str) or not entry_id:
            errors.append(f"{packet_id}.crosswalk_entry_id must be a non-empty string")
            continue
        typed_entry_id = CrosswalkEntryId(entry_id)
        if typed_entry_id not in crosswalk_entry_ids:
            errors.append(f"{packet_id} references unknown crosswalk entry {entry_id!r}")
        covered_entry_ids.add(typed_entry_id)

        predicate = packet.get("bad_trace_predicate")
        if not isinstance(predicate, dict):
            errors.append(f"{packet_id}.bad_trace_predicate must be an object")
            continue
        predicate_name = predicate.get("name")
        if not isinstance(predicate_name, str) or not predicate_name.endswith("BadTrace"):
            errors.append(f"{packet_id}.bad_trace_predicate.name must end with BadTrace")
        state_scope = predicate.get("state_scope")
        if not isinstance(state_scope, list) or len(state_scope) < 2:
            errors.append(f"{packet_id}.bad_trace_predicate.state_scope must contain at least two fields")
        elif any(not isinstance(item, str) or not item for item in state_scope):
            errors.append(f"{packet_id}.bad_trace_predicate.state_scope entries must be non-empty strings")
        conditions = predicate.get("conditions")
        if not isinstance(conditions, list) or len(conditions) < 3:
            errors.append(f"{packet_id}.bad_trace_predicate.conditions must contain at least three clauses")
        else:
            total_conditions += len(conditions)
            for condition_idx, condition in enumerate(conditions):
                if not isinstance(condition, str) or not condition.strip():
                    errors.append(
                        f"{packet_id}.bad_trace_predicate.conditions[{condition_idx}] must be a non-empty string"
                    )

        obligations = packet.get("closure_obligations")
        if not isinstance(obligations, list) or len(obligations) < 2:
            errors.append(f"{packet_id}.closure_obligations must contain at least two obligations")
        else:
            total_obligations += len(obligations)
            joined = " ".join(str(obligation).lower() for obligation in obligations)
            if "map" not in joined or "reject" not in joined:
                errors.append(f"{packet_id}.closure_obligations must include mapping and rejection obligations")
            for obligation_idx, obligation in enumerate(obligations):
                if not isinstance(obligation, str) or not obligation.strip():
                    errors.append(f"{packet_id}.closure_obligations[{obligation_idx}] must be a non-empty string")

        if typed_entry_id in crosswalk_axes:
            axis_count = len(crosswalk_axes[typed_entry_id])
            if axis_count == 0:
                errors.append(f"{packet_id} binds to a crosswalk entry with no axes")
            else:
                exact_axis_bindings += 1

    missing_packets = sorted(str(entry_id) for entry_id in crosswalk_entry_ids - covered_entry_ids)
    extra_packets = sorted(str(entry_id) for entry_id in covered_entry_ids - crosswalk_entry_ids)
    if missing_packets:
        errors.append(f"crosswalk entries missing closure packets: {', '.join(missing_packets)}")
    if extra_packets:
        errors.append(f"closure packets reference non-crosswalk entries: {', '.join(extra_packets)}")

    ok = not errors
    return {
        "schema": "zenodex/disaster-class-closure-packets-check/v1",
        "ok": ok,
        "packet_path": str(packet_path),
        "crosswalk_path": str(crosswalk_path),
        "packet_count": len(packets),
        "crosswalk_entry_count": len(crosswalk_entry_ids),
        "covered_crosswalk_entry_count": len(covered_entry_ids & crosswalk_entry_ids),
        "missing_packet_count": len(missing_packets),
        "extra_packet_count": len(extra_packets),
        "exact_axis_binding_count": exact_axis_bindings,
        "total_bad_trace_condition_count": total_conditions,
        "total_closure_obligation_count": total_obligations,
        "crosswalk_known_axis_count": crosswalk_result.get("known_axis_count"),
        "crosswalk_mapped_axis_count": crosswalk_result.get("mapped_axis_count"),
        "errors": errors,
        "warnings": warnings,
    }


def _print_text(result: dict[str, Any]) -> None:
    print(f"ok: {result['ok']}")
    print(f"packet_count: {result['packet_count']}")
    print(f"crosswalk_entry_count: {result['crosswalk_entry_count']}")
    print(f"covered_crosswalk_entry_count: {result['covered_crosswalk_entry_count']}")
    print(f"missing_packet_count: {result['missing_packet_count']}")
    print(f"extra_packet_count: {result['extra_packet_count']}")
    print(f"exact_axis_binding_count: {result['exact_axis_binding_count']}")
    print(f"total_bad_trace_condition_count: {result['total_bad_trace_condition_count']}")
    print(f"total_closure_obligation_count: {result['total_closure_obligation_count']}")
    print(f"crosswalk_known_axis_count: {result['crosswalk_known_axis_count']}")
    print(f"crosswalk_mapped_axis_count: {result['crosswalk_mapped_axis_count']}")
    for warning in result["warnings"]:
        print(f"warning: {warning}")
    for error in result["errors"]:
        print(f"error: {error}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packets", nargs="?", type=Path, default=DEFAULT_PACKETS)
    parser.add_argument("--crosswalk", type=Path, default=DEFAULT_CROSSWALK)
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)

    result = check_closure_packets(args.packets, crosswalk_path=args.crosswalk)
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        _print_text(result)
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
