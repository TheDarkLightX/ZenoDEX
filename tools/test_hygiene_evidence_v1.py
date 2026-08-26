"""Evidence-packet parser for Test Hygiene Contract V1."""

from __future__ import annotations

import datetime as dt
import re
from pathlib import Path
from typing import Any, Mapping, cast

from tools.test_hygiene_model_v1 import (
    ALLOWED_DECISIONS,
    ALLOWED_RISK_CLASSES,
    EVIDENCE_SCHEMA,
    ContractV1,
    PacketV1,
    PinV1,
    RemovedPathV1,
    TestHygieneError,
    exact_fields,
    load_json,
    object_value,
    portable_path,
    require,
    string_list,
    string_value,
)

_SHA256_RE = re.compile(r"[0-9a-f]{64}")
_EVIDENCE_ID_RE = re.compile(r"THV1-[0-9]{8}-[a-z0-9][a-z0-9-]*")
_PACKET_FIELDS = frozenset(
    {
        "schema",
        "evidence_id",
        "created_date",
        "claim_scope",
        "change_kind",
        "risk_class",
        "invariant_ids",
        "failure_modes",
        "source_pins",
        "removed_paths",
        "test_pins",
        "evidence_families",
        "aaa",
        "reject_is_noop",
        "boundary_dimensions",
        "mutations",
        "nonclaims",
    }
)
_OPTIONAL_PACKET_FIELDS = frozenset({"supersedes_evidence_ids"})


def _parse_pin(value: object, *, context: str, test_pin: bool) -> PinV1:
    raw = object_value(value, context=context)
    expected = frozenset(
        {"path", "sha256", "node_ids"} if test_pin else {"path", "sha256"}
    )
    exact_fields(raw, expected, context=context)
    path = portable_path(raw["path"], context=f"{context}.path")
    digest = string_value(raw["sha256"], context=f"{context}.sha256")
    require(_SHA256_RE.fullmatch(digest) is not None, f"{context}: invalid sha256")
    if not test_pin:
        return PinV1(path=path, sha256=digest)

    require(
        path.startswith("tests/") and path.endswith(".py"),
        f"{context}: test pin must name a Python test file",
    )
    node_ids = string_list(raw["node_ids"], context=f"{context}.node_ids")
    for node_id in node_ids:
        require(
            node_id.startswith(f"{path}::"),
            f"{context}: node id must belong to pinned test path",
        )
        require(
            not any(character.isspace() for character in node_id),
            f"{context}: node id contains whitespace",
        )
    return PinV1(path=path, sha256=digest, node_ids=node_ids)


def _parse_pins(raw: object, *, context: str, test_pin: bool) -> tuple[PinV1, ...]:
    require(type(raw) is list, f"{context}: expected list")
    pins = tuple(
        _parse_pin(item, context=f"{context}[{index}]", test_pin=test_pin)
        for index, item in enumerate(cast(list[object], raw))
    )
    if test_pin:
        require(bool(pins), f"{context}: expected non-empty list")
    return pins


def _parse_removed(raw: object, *, context: str) -> tuple[RemovedPathV1, ...]:
    require(type(raw) is list, f"{context}: expected list")
    result: list[RemovedPathV1] = []
    for index, item in enumerate(cast(list[object], raw)):
        item_context = f"{context}[{index}]"
        row = object_value(item, context=item_context)
        exact_fields(
            row,
            frozenset({"path", "reason", "replacement_paths"}),
            context=item_context,
        )
        result.append(
            RemovedPathV1(
                path=portable_path(row["path"], context=f"{item_context}.path"),
                reason=string_value(row["reason"], context=f"{item_context}.reason"),
                replacement_paths=string_list(
                    row["replacement_paths"],
                    context=f"{item_context}.replacement_paths",
                ),
            )
        )
    return tuple(result)


def _decision(value: object, *, context: str) -> None:
    raw = object_value(value, context=context)
    exact_fields(raw, frozenset({"status", "reason"}), context=context)
    status = string_value(raw["status"], context=f"{context}.status")
    require(status in ALLOWED_DECISIONS, f"{context}: invalid status")
    string_value(raw["reason"], context=f"{context}.reason")


def _validate_boundaries(raw: object, *, context: str, required: bool) -> None:
    require(type(raw) is list, f"{context}: expected list")
    rows = cast(list[object], raw)
    if required:
        require(bool(rows), f"{context.rsplit('.', 1)[0]}: boundary evidence requires dimensions")
    for index, item in enumerate(rows):
        item_context = f"{context}[{index}]"
        row = object_value(item, context=item_context)
        exact_fields(row, frozenset({"name", "points"}), context=item_context)
        string_value(row["name"], context=f"{item_context}.name")
        points = string_list(row["points"], context=f"{item_context}.points")
        require(
            len(points) >= 2,
            f"{item_context}: expected at least two boundary points",
        )


def _validate_mutations(
    raw: object,
    *,
    context: str,
    required: bool,
    pinned_nodes: frozenset[str],
) -> None:
    require(type(raw) is list, f"{context}: expected list")
    rows = cast(list[object], raw)
    if required:
        require(bool(rows), f"{context.rsplit('.', 1)[0]}: mutation evidence requires named mutants")
    for index, item in enumerate(rows):
        item_context = f"{context}[{index}]"
        row = object_value(item, context=item_context)
        exact_fields(row, frozenset({"description", "killed_by"}), context=item_context)
        string_value(row["description"], context=f"{item_context}.description")
        killer = string_value(row["killed_by"], context=f"{item_context}.killed_by")
        require(
            killer in pinned_nodes,
            f"{context.rsplit('.', 1)[0]}: mutation killer is not a pinned node",
        )


def _validate_path_partition(
    *,
    context: str,
    source_pins: tuple[PinV1, ...],
    test_pins: tuple[PinV1, ...],
    removed: tuple[RemovedPathV1, ...],
) -> None:
    pin_paths = [pin.path for pin in (*source_pins, *test_pins)]
    test_paths = {pin.path for pin in test_pins}
    require(len(pin_paths) == len(set(pin_paths)), f"{context}: duplicate pinned paths")
    removed_paths = [item.path for item in removed]
    require(
        len(removed_paths) == len(set(removed_paths)),
        f"{context}: duplicate removed paths",
    )
    require(
        not (set(pin_paths) & set(removed_paths)),
        f"{context}: path cannot be pinned and removed",
    )
    for item in removed:
        require(
            set(item.replacement_paths) <= set(pin_paths),
            f"{context}: removed path replacement is not pinned",
        )
        if item.path.startswith("tests/"):
            require(
                bool(set(item.replacement_paths) & test_paths),
                f"{context}: deleted test replacement must be a pinned test",
            )


def load_packet(path: Path, contract: ContractV1) -> PacketV1:
    context = path.name
    raw = load_json(path, context=context)
    expected_fields = _PACKET_FIELDS | (
        _OPTIONAL_PACKET_FIELDS
        if "supersedes_evidence_ids" in raw
        else frozenset()
    )
    exact_fields(raw, expected_fields, context=context)
    require(raw["schema"] == EVIDENCE_SCHEMA, f"{context}: schema mismatch")
    evidence_id = string_value(raw["evidence_id"], context=f"{context}.evidence_id")
    require(
        _EVIDENCE_ID_RE.fullmatch(evidence_id) is not None,
        f"{context}: invalid evidence id",
    )
    require(path.stem == evidence_id, f"{context}: filename must equal evidence id")
    _parse_packet_metadata(raw, context=context, contract=contract)

    source_pins = _parse_pins(
        raw["source_pins"], context=f"{context}.source_pins", test_pin=False
    )
    test_pins = _parse_pins(
        raw["test_pins"], context=f"{context}.test_pins", test_pin=True
    )
    removed = _parse_removed(raw["removed_paths"], context=f"{context}.removed_paths")
    _validate_path_partition(
        context=context,
        source_pins=source_pins,
        test_pins=test_pins,
        removed=removed,
    )

    families = frozenset(
        string_list(raw["evidence_families"], context=f"{context}.evidence_families")
    )
    require(families <= contract.allowed_families, f"{context}: unsupported evidence family")
    _decision(raw["aaa"], context=f"{context}.aaa")
    _decision(raw["reject_is_noop"], context=f"{context}.reject_is_noop")
    _validate_boundaries(
        raw["boundary_dimensions"],
        context=f"{context}.boundary_dimensions",
        required="boundary" in families,
    )
    nodes = frozenset(node for pin in test_pins for node in pin.node_ids)
    _validate_mutations(
        raw["mutations"],
        context=f"{context}.mutations",
        required="mutation" in families,
        pinned_nodes=nodes,
    )
    return PacketV1(
        path=path,
        evidence_id=evidence_id,
        risk_class=string_value(raw["risk_class"], context=f"{context}.risk_class"),
        families=families,
        source_pins=source_pins,
        test_pins=test_pins,
        removed_paths=removed,
        supersedes_evidence_ids=(
            string_list(
                raw["supersedes_evidence_ids"],
                context=f"{context}.supersedes_evidence_ids",
            )
            if "supersedes_evidence_ids" in raw
            else ()
        ),
    )


def _parse_packet_metadata(
    raw: Mapping[str, Any], *, context: str, contract: ContractV1
) -> None:
    try:
        dt.date.fromisoformat(
            string_value(raw["created_date"], context=f"{context}.created_date")
        )
    except ValueError as exc:
        raise TestHygieneError(f"{context}: invalid created_date") from exc
    string_value(raw["claim_scope"], context=f"{context}.claim_scope")
    change_kind = string_value(raw["change_kind"], context=f"{context}.change_kind")
    require(
        change_kind in contract.allowed_change_kinds,
        f"{context}: unsupported change kind",
    )
    risk_class = string_value(raw["risk_class"], context=f"{context}.risk_class")
    require(risk_class in ALLOWED_RISK_CLASSES, f"{context}: unsupported risk class")
    string_list(raw["invariant_ids"], context=f"{context}.invariant_ids")
    string_list(raw["failure_modes"], context=f"{context}.failure_modes")
    string_list(raw["nonclaims"], context=f"{context}.nonclaims")


def load_packets(evidence_dir: Path, contract: ContractV1) -> tuple[PacketV1, ...]:
    if not evidence_dir.exists():
        return ()
    require(
        evidence_dir.is_dir(), f"evidence path is not a directory: {evidence_dir}"
    )
    packets = tuple(
        load_packet(path, contract) for path in sorted(evidence_dir.glob("*.json"))
    )
    ids = [packet.evidence_id for packet in packets]
    require(len(ids) == len(set(ids)), "duplicate evidence ids")
    seen: set[str] = set()
    superseded_by: dict[str, str] = {}
    for packet in packets:
        for predecessor in packet.supersedes_evidence_ids:
            require(
                predecessor in seen,
                f"{packet.evidence_id}: superseded evidence must be an earlier packet: {predecessor}",
            )
            require(
                predecessor not in superseded_by,
                f"{packet.evidence_id}: evidence already superseded by {superseded_by.get(predecessor, '')}: {predecessor}",
            )
            superseded_by[predecessor] = packet.evidence_id
        seen.add(packet.evidence_id)
    return packets
