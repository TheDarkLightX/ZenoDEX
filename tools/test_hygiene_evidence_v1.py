"""Evidence-packet parser for Test Hygiene Contract V1.

Mutation rows (``mutations[]``) come in three shapes:

- MECHANICAL: ``{description, killed_by, mutant: {path, needle, replacement}}``.
  ``path`` is one of the packet's ``source_pins``; ``needle`` must occur exactly once
  in that file (checked by ``tools/check_test_hygiene_v1.py`` while the pin is current
  and by ``tools/thv1_mutation_ledger_v1.py`` before it mutates); ``killed_by`` is a
  pinned pytest node or ``<pinned crate>/tests/<target>.rs::<filter>`` for a cargo
  test. The ledger executes the row: the killer must fail on the mutated copy.
- NARRATIVE: ``{description, killed_by, narrative: true}``. Declared but not executable
  (the description says why); never counted as killed.
- LEGACY: ``{description, killed_by}``. The pre-ledger string claim. Accepted only for
  packets whose evidence-id date precedes ``MECHANICAL_MUTATION_ROWS_FROM``; those
  packets are immutable replay records (append-only) that no gate ever executed, and
  the checker reports them as ``legacy`` so the count stays visible. A packet dated at
  or after the cutover must use ``mutant`` or ``narrative``; the diff-aware checker
  also refuses an ADDED packet carrying legacy rows whatever its date.
"""

from __future__ import annotations

import dataclasses
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
_HYGIENE_LINEAGE_RE = re.compile(r"^(.*?)(?:-v([0-9]+))?(\.json)?$")
_HYGIENE_DATE_PREFIX_RE = re.compile(r"^THV1-[0-9]{8}-")

# Evidence-id date (THV1-YYYYMMDD-...) from which string-only mutation rows are refused.
MECHANICAL_MUTATION_ROWS_FROM = "20260903"
MUTATION_ROW_KINDS = ("mechanical", "narrative", "legacy")
_LEGACY_ROW_FIELDS = frozenset({"description", "killed_by"})
_MECHANICAL_ROW_FIELDS = frozenset({"description", "killed_by", "mutant"})
_NARRATIVE_ROW_FIELDS = frozenset({"description", "killed_by", "narrative"})
_MUTANT_FIELDS = frozenset({"path", "needle", "replacement"})


@dataclasses.dataclass(frozen=True, slots=True)
class MutantV1:
    """One textual mutant: ``needle`` (exactly once in ``path``) becomes ``replacement``."""

    path: str
    needle: str
    replacement: str


@dataclasses.dataclass(frozen=True, slots=True)
class MutationRowV1:
    description: str
    killed_by: str
    mutant: MutantV1 | None = None
    narrative: bool = False

    @property
    def kind(self) -> str:
        if self.mutant is not None:
            return "mechanical"
        return "narrative" if self.narrative else "legacy"


def needle_occurrences_v1(text: str, needle: str) -> int:
    """Count every start position of ``needle`` in ``text`` (overlapping ones included)."""

    if not needle:
        return 0
    count = 0
    position = text.find(needle)
    while position != -1:
        count += 1
        position = text.find(needle, position + 1)
    return count


def hygiene_lineage_key_v1(name: str) -> tuple[str, int, str]:
    """Order key for packets: lineage name, then the trailing ``-vN`` compared numerically, then the name.

    The gate selects the newest packet whose pin matches a changed path. Lexicographic file order
    ranks ``-v9`` above ``-v27``, so a stale early packet shadowed every later one for any path
    whose bytes it still matched (campaign finding at P31); this key is the same one
    ``tools/o008_formal_cycle_admission_v1.hygiene_lineage_key_v1`` uses, pinned equal by test.
    The date prefix stays part of the name (recency across lineages); a version cut under an older
    date is refused at load time by ``require_lineage_versions_monotone_with_dates_v1`` rather
    than reordered (Opus P32 F-2).
    """

    match = _HYGIENE_LINEAGE_RE.fullmatch(name)
    if match is None:
        return (name, -1, name)
    version = -1 if match.group(2) is None else int(match.group(2))
    return (match.group(1), version, name)


def hygiene_dated_lineage_v1(name: str) -> tuple[str, str, int]:
    """Split a packet name into (date-stripped lineage, date prefix, numeric version)."""

    lineage_with_date, version, _ = hygiene_lineage_key_v1(name)
    stem = lineage_with_date.rsplit("/", 1)[-1]
    date = stem[:14] if _HYGIENE_DATE_PREFIX_RE.match(stem) else ""
    return (_HYGIENE_DATE_PREFIX_RE.sub("", stem), date, version)


def require_lineage_versions_monotone_with_dates_v1(names: list[str]) -> None:
    """Refuse a lineage whose versions regress across date prefixes (Opus P32 F-2).

    Packets order by name first (recency across lineages) and by numeric version within a name, so
    a later version cut under an OLDER date prefix would be shadowed by the newer-dated packet. Instead
    of reordering, the loader refuses the mis-dated cut: within one date-stripped lineage, a packet
    with a later date must carry a higher version than every packet with an earlier date.
    """

    by_lineage: dict[str, list[tuple[str, int, str]]] = {}
    for name in names:
        lineage, date, version = hygiene_dated_lineage_v1(name)
        by_lineage.setdefault(lineage, []).append((date, version, name))
    for lineage, rows in by_lineage.items():
        for date_a, version_a, name_a in rows:
            for date_b, version_b, name_b in rows:
                if date_a < date_b and version_a >= version_b:
                    raise TestHygieneError(
                        f"lineage {lineage}: {name_a} (version {version_a}) is dated before {name_b}"
                        f" (version {version_b}); versions must rise with the date prefix"
                    )
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


def _parse_mutant(raw: object, *, context: str, source_pin_paths: frozenset[str]) -> MutantV1:
    mutant = object_value(raw, context=context)
    exact_fields(mutant, _MUTANT_FIELDS, context=context)
    path = portable_path(mutant["path"], context=f"{context}.path")
    require(path in source_pin_paths, f"{context}.path: mutant path is not a pinned source path")
    needle = mutant["needle"]
    require(type(needle) is str and needle != "", f"{context}.needle: expected non-empty string")
    replacement = mutant["replacement"]
    require(type(replacement) is str, f"{context}.replacement: expected string")
    require(replacement != needle, f"{context}: replacement must differ from needle")
    return MutantV1(path=path, needle=cast(str, needle), replacement=cast(str, replacement))


def _validate_killer(
    killer: str,
    *,
    packet_context: str,
    pinned_nodes: frozenset[str],
    rust_test_paths: frozenset[str],
    legacy: bool,
) -> None:
    if killer in pinned_nodes:
        return
    if not legacy:
        path, separator, rest = killer.partition("::")
        cargo_filter = (
            bool(separator)
            and path in rust_test_paths
            and bool(rest)
            and not any(character.isspace() for character in rest)
        )
        if cargo_filter:
            return
        raise TestHygieneError(
            f"{packet_context}: mutation killer is not a pinned node or a pinned cargo test filter"
        )
    raise TestHygieneError(f"{packet_context}: mutation killer is not a pinned node")


def _validate_mutations(
    raw: object,
    *,
    context: str,
    required: bool,
    pinned_nodes: frozenset[str],
    source_pins: tuple[PinV1, ...],
    legacy_allowed: bool,
) -> tuple[MutationRowV1, ...]:
    require(type(raw) is list, f"{context}: expected list")
    rows = cast(list[object], raw)
    packet_context = context.rsplit(".", 1)[0]
    if required:
        require(bool(rows), f"{packet_context}: mutation evidence requires named mutants")
    source_pin_paths = frozenset(pin.path for pin in source_pins)
    rust_test_paths = frozenset(
        pin.path for pin in source_pins if pin.path.endswith(".rs") and "/tests/" in pin.path
    )
    result: list[MutationRowV1] = []
    for index, item in enumerate(rows):
        item_context = f"{context}[{index}]"
        row = object_value(item, context=item_context)
        keys = frozenset(row)
        mutant: MutantV1 | None = None
        narrative = False
        if keys == _MECHANICAL_ROW_FIELDS:
            mutant = _parse_mutant(
                row["mutant"], context=f"{item_context}.mutant", source_pin_paths=source_pin_paths
            )
        elif keys == _NARRATIVE_ROW_FIELDS:
            require(row["narrative"] is True, f"{item_context}.narrative: must be true")
            narrative = True
        elif keys == _LEGACY_ROW_FIELDS:
            require(
                legacy_allowed,
                f"{item_context}: string-only mutation rows are refused from"
                f" {MECHANICAL_MUTATION_ROWS_FROM}; declare mutant or narrative",
            )
        else:
            raise TestHygieneError(
                f"{item_context}: expected description, killed_by and exactly one of"
                f" mutant or narrative; got {sorted(keys)}"
            )
        description = string_value(row["description"], context=f"{item_context}.description")
        killer = string_value(row["killed_by"], context=f"{item_context}.killed_by")
        _validate_killer(
            killer,
            packet_context=packet_context,
            pinned_nodes=pinned_nodes,
            rust_test_paths=rust_test_paths,
            legacy=mutant is None and not narrative,
        )
        result.append(MutationRowV1(description, killer, mutant, narrative))
    return tuple(result)


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


def _parse_packet(
    path: Path, contract: ContractV1
) -> tuple[PacketV1, tuple[MutationRowV1, ...]]:
    context = path.name
    raw = load_json(path, context=context)
    exact_fields(raw, _PACKET_FIELDS, context=context)
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
    mutations = _validate_mutations(
        raw["mutations"],
        context=f"{context}.mutations",
        required="mutation" in families,
        pinned_nodes=nodes,
        source_pins=source_pins,
        legacy_allowed=evidence_id[5:13] < MECHANICAL_MUTATION_ROWS_FROM,
    )
    packet = PacketV1(
        path=path,
        evidence_id=evidence_id,
        risk_class=string_value(raw["risk_class"], context=f"{context}.risk_class"),
        families=families,
        source_pins=source_pins,
        test_pins=test_pins,
        removed_paths=removed,
    )
    return packet, mutations


def load_packet(path: Path, contract: ContractV1) -> PacketV1:
    return _parse_packet(path, contract)[0]


def load_packet_with_mutations(
    path: Path, contract: ContractV1
) -> tuple[PacketV1, tuple[MutationRowV1, ...]]:
    """Load one packet together with its validated mutation rows."""

    return _parse_packet(path, contract)


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


def load_packets_with_mutations(
    evidence_dir: Path, contract: ContractV1
) -> tuple[tuple[PacketV1, tuple[MutationRowV1, ...]], ...]:
    """Load every packet (lineage order, monotone-version rule) with its mutation rows."""

    if not evidence_dir.exists():
        return ()
    require(
        evidence_dir.is_dir(), f"evidence path is not a directory: {evidence_dir}"
    )
    ordered = sorted(
        evidence_dir.glob("*.json"),
        key=lambda path: hygiene_lineage_key_v1(path.name),
    )
    require_lineage_versions_monotone_with_dates_v1([path.name for path in ordered])
    loaded = tuple(_parse_packet(path, contract) for path in ordered)
    ids = [packet.evidence_id for packet, _ in loaded]
    require(len(ids) == len(set(ids)), "duplicate evidence ids")
    return loaded


def load_packets(evidence_dir: Path, contract: ContractV1) -> tuple[PacketV1, ...]:
    return tuple(packet for packet, _ in load_packets_with_mutations(evidence_dir, contract))
