#!/usr/bin/env python3
"""Validate Test Hygiene Contract V1 and changed-file evidence.

With ``--base-ref`` or ``--changed-file``, every changed critical path requires
a current source-pinned evidence packet. Static mode validates closed schemas
while retaining historical packets as immutable replay records.

Mutation rows are classified (mechanical, narrative, legacy) and counted in the
report; for every mechanical row whose mutated path is still at its pinned
bytes, the needle must occur exactly once. Executing the rows is the job of
``tools/thv1_mutation_ledger_v1.py``; this checker never runs a test.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import subprocess
import sys
from pathlib import Path
from typing import Sequence, cast

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.test_hygiene_evidence_v1 import (
    MECHANICAL_MUTATION_ROWS_FROM,
    MUTATION_ROW_KINDS,
    MutationRowV1,
    hygiene_dated_lineage_v1,
    load_packets_with_mutations,
    needle_occurrences_v1,
)
from tools.test_hygiene_model_v1 import (
    ALLOWED_STATUSES,
    CONTRACT_SCHEMA,
    DEFAULT_CONTRACT,
    DEFAULT_EVIDENCE_DIR,
    REPO_ROOT,
    ChangedPathV1,
    ContractV1,
    PacketV1,
    PinV1,
    RuleV1,
    TestHygieneError,
    load_contract,
    require,
    sha256_file,
)

__all__ = [
    "DEFAULT_CONTRACT",
    "DEFAULT_EVIDENCE_DIR",
    "REPO_ROOT",
    "ChangedPathV1",
    "TestHygieneError",
    "check_repository",
    "collect_git_changed_paths",
]

PacketRowsV1 = tuple[PacketV1, tuple[MutationRowV1, ...]]


@dataclasses.dataclass(frozen=True, slots=True)
class _SelectionContextV1:
    repo_root: Path
    packets: tuple[PacketV1, ...]
    strong_families: frozenset[str]


def _matching_rules(contract: ContractV1, path: str) -> tuple[RuleV1, ...]:
    return tuple(rule for rule in contract.rules if rule.matches(path))


def _validate_current_packet(repo_root: Path, packet: PacketV1) -> None:
    for pin in packet.source_pins:
        _validate_pin(repo_root, packet, pin, "source")
    for pin in packet.test_pins:
        _validate_pin(repo_root, packet, pin, "test")


def _validate_pin(
    repo_root: Path,
    packet: PacketV1,
    pin: PinV1,
    label: str,
) -> None:
    absolute = repo_root / pin.path
    require(
        absolute.is_file(),
        f"{packet.evidence_id}: missing pinned {label} path {pin.path}",
    )
    require(
        sha256_file(absolute) == pin.sha256,
        f"{packet.evidence_id}: {label} sha256 drift for {pin.path}",
    )


def _packet_satisfies_rules(
    *,
    packet: PacketV1,
    path: str,
    rules: tuple[RuleV1, ...],
    strong_families: frozenset[str],
) -> None:
    required = frozenset().union(*(rule.required_families for rule in rules))
    require(
        required <= packet.families,
        f"{packet.evidence_id}: missing required evidence families for {path}",
    )
    minimum = max(rule.minimum_strong_families for rule in rules)
    strong_count = len(packet.families & strong_families)
    require(
        strong_count >= minimum,
        f"{packet.evidence_id}: insufficient strong evidence families for {path}",
    )
    require(
        packet.risk_class != "ordinary",
        f"{packet.evidence_id}: critical path cannot use ordinary risk class",
    )


def _select_packet(
    context: _SelectionContextV1,
    change: ChangedPathV1,
    rules: tuple[RuleV1, ...],
) -> PacketV1:
    stale_labels: list[str] = []
    for packet in reversed(context.packets):
        if change.status == "D":
            if packet.removal_for(change.path) is None:
                continue
        else:
            pin = packet.current_pin_for(change.path)
            if pin is None:
                continue
            absolute = context.repo_root / pin.path
            if not absolute.is_file() or sha256_file(absolute) != pin.sha256:
                stale_labels.append("test" if pin.node_ids else "source")
                continue

        _packet_satisfies_rules(
            packet=packet,
            path=change.path,
            rules=rules,
            strong_families=context.strong_families,
        )
        _validate_current_packet(context.repo_root, packet)
        return packet

    if stale_labels:
        raise TestHygieneError(
            f"{sorted(stale_labels)[0]} sha256 drift for changed path {change.path}"
        )
    raise TestHygieneError(f"uncovered critical path: {change.status}:{change.path}")


def _count_mutation_rows(
    repo_root: Path, loaded: Sequence[PacketRowsV1]
) -> dict[str, int]:
    """Count rows by kind; a mechanical row on a current pin must find its needle exactly once."""

    counts = {kind: 0 for kind in MUTATION_ROW_KINDS}
    counts["mechanical_current"] = 0
    digests: dict[str, str | None] = {}
    for packet, rows in loaded:
        for row in rows:
            counts[row.kind] += 1
            if row.mutant is None:
                continue
            pin = packet.current_pin_for(row.mutant.path)
            require(pin is not None, f"{packet.evidence_id}: mutant path is not pinned")
            absolute = repo_root / row.mutant.path
            if row.mutant.path not in digests:
                digests[row.mutant.path] = sha256_file(absolute) if absolute.is_file() else None
            if digests[row.mutant.path] != cast(PinV1, pin).sha256:
                continue
            counts["mechanical_current"] += 1
            text = absolute.read_bytes().decode("utf-8")
            occurrences = needle_occurrences_v1(text, row.mutant.needle)
            require(
                occurrences == 1,
                f"{packet.evidence_id}: mutant needle occurs {occurrences} times in"
                f" {row.mutant.path}; a mechanical row needs exactly one",
            )
    return counts


def _created_date_v1(path: Path | None) -> str:
    """The packet's own ``created_date`` as YYYYMMDD, or the far future when unreadable.

    An unreadable or absent date is treated as post-cutover so the strict rule applies:
    a packet that will not say when it was authored does not earn the legacy exemption.
    """

    if path is None or not path.is_file():
        return "99999999"
    try:
        value = json.loads(path.read_text(encoding="utf-8")).get("created_date")
    except (OSError, ValueError):
        return "99999999"
    if type(value) is not str:
        return "99999999"
    compact = value.replace("-", "")
    return compact if len(compact) == 8 and compact.isdigit() else "99999999"


def _carried_rows_v1(evidence_id: str, loaded: Sequence[PacketRowsV1]) -> frozenset[tuple[str, str]]:
    """The (description, killer) pairs an earlier packet of the same lineage already declared."""

    lineage, date, version = hygiene_dated_lineage_v1(evidence_id)
    carried: set[tuple[str, str]] = set()
    for packet, rows in loaded:
        other_lineage, other_date, other_version = hygiene_dated_lineage_v1(packet.evidence_id)
        if other_lineage != lineage:
            continue
        if (other_date, other_version) >= (date, version):
            continue
        carried.update((row.description, row.killed_by) for row in rows)
    return frozenset(carried)


def _reject_added_legacy_packets(
    changed_paths: Sequence[ChangedPathV1],
    loaded: Sequence[PacketRowsV1],
    *,
    evidence_prefix: str,
) -> None:
    """A packet ADDED on or after the cutover may not carry string-only rows.

    The rule applies to a row a packet DECLARES, not to one it carries forward. A packet
    added on or after the cutover may not introduce a string-only row, but a successor
    that merely re-pins its predecessor keeps that predecessor's rows: evidence packets
    are append-only, so re-cutting history is not available, and requiring it would make
    an honest re-pin impossible.

    A packet is exempt entirely only when BOTH its evidence-id date and its own
    ``created_date`` precede the cutover. Membership of the diff cannot be the key on its
    own: a diff taken against an old base (the campaign base, say) reports every packet
    cut since then as added, including ones authored before the cutover. Reading the
    packet's own ``created_date`` keeps the rule's teeth against a back-dated evidence id.

    DECLARED RESIDUALS: a packet that back-dates BOTH fields is exempt, because nothing in
    the evidence directory records when a packet was authored; and a carried-forward row
    is identified by its (description, killer) pair appearing in an earlier packet of the
    same lineage, so a new row that copies an old row's text exactly is treated as carried.
    """

    rows_by_name = {packet.path.name: rows for packet, rows in loaded}
    rows_by_name_path = {packet.path.name: packet.path for packet, _rows in loaded}
    for change in changed_paths:
        if change.status != "A" or not change.path.startswith(evidence_prefix):
            continue
        name = Path(change.path).name
        evidence_id = name[:-5] if name.endswith(".json") else name
        if evidence_id[5:13] < MECHANICAL_MUTATION_ROWS_FROM and _created_date_v1(
            rows_by_name_path.get(name)
        ) < MECHANICAL_MUTATION_ROWS_FROM:
            continue
        rows = rows_by_name.get(name, ())
        carried = _carried_rows_v1(evidence_id, loaded)
        introduced = [
            row for row in rows if row.kind == "legacy" and (row.description, row.killed_by) not in carried
        ]
        require(
            not introduced,
            f"added evidence packet {change.path} declares string-only mutation rows;"
            " declare mutant or narrative",
        )


def check_repository(
    *,
    repo_root: Path = REPO_ROOT,
    contract_path: Path = DEFAULT_CONTRACT,
    evidence_dir: Path = DEFAULT_EVIDENCE_DIR,
    changed_paths: Sequence[ChangedPathV1] = (),
) -> dict[str, object]:
    """Validate contract structure and optional changed-file coverage."""

    contract = load_contract(contract_path)
    loaded = load_packets_with_mutations(evidence_dir, contract)
    packets = tuple(packet for packet, _ in loaded)
    normalized = tuple(
        sorted(set(changed_paths), key=lambda item: (item.path, item.status))
    )
    _reject_packet_rewrites(normalized, evidence_prefix=contract.evidence_path_prefix)
    _reject_added_legacy_packets(normalized, loaded, evidence_prefix=contract.evidence_path_prefix)
    mutation_rows = _count_mutation_rows(repo_root, loaded)

    selected: dict[str, PacketV1] = {}
    critical: list[ChangedPathV1] = []
    selection_context = _SelectionContextV1(
        repo_root=repo_root,
        packets=packets,
        strong_families=contract.strong_families,
    )
    for change in normalized:
        rules = _matching_rules(contract, change.path)
        if not rules:
            continue
        critical.append(change)
        selected[change.path] = _select_packet(
            selection_context,
            change,
            rules,
        )

    selected_packets = {packet.evidence_id: packet for packet in selected.values()}
    nodes = sorted(
        {node for packet in selected_packets.values() for node in packet.node_ids}
    )
    return {
        "ok": True,
        "contract_schema": CONTRACT_SCHEMA,
        "evidence_packet_count": len(packets),
        "changed_path_count": len(normalized),
        "critical_path_count": len(critical),
        "covered_critical_paths": sorted(selected),
        "selected_evidence_ids": sorted(selected_packets),
        "pytest_node_ids": nodes,
        "mutation_rows": mutation_rows,
    }


def _reject_packet_rewrites(
    changed_paths: Sequence[ChangedPathV1], *, evidence_prefix: str
) -> None:
    for change in changed_paths:
        if change.path.startswith(evidence_prefix) and change.status != "A":
            raise TestHygieneError(
                f"evidence packets are append-only: {change.status}:{change.path}"
            )


def collect_git_changed_paths(
    repo_root: Path, base_ref: str
) -> tuple[ChangedPathV1, ...]:
    """Return base-to-HEAD changes with renames normalized to delete plus add."""

    require(bool(base_ref.strip()), "base ref must not be empty")
    try:
        merge_base = subprocess.run(
            ["git", "merge-base", base_ref, "HEAD"],
            cwd=repo_root,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        output = subprocess.run(
            ["git", "diff", "--name-status", "--find-renames", merge_base, "HEAD"],
            cwd=repo_root,
            check=True,
            capture_output=True,
            text=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as exc:
        raise TestHygieneError(
            f"failed to collect Git diff for {base_ref}: {exc}"
        ) from exc
    return _parse_git_name_status(output)


def _parse_git_name_status(output: str) -> tuple[ChangedPathV1, ...]:
    changes: list[ChangedPathV1] = []
    for line in output.splitlines():
        fields = line.split("\t")
        status = fields[0]
        if status.startswith(("R", "C")):
            require(len(fields) == 3, f"malformed Git rename row: {line}")
            changes.append(ChangedPathV1(status="D", path=fields[1]))
            changes.append(ChangedPathV1(status="A", path=fields[2]))
            continue
        normalized_status = status[:1]
        require(
            normalized_status in ALLOWED_STATUSES and len(fields) == 2,
            f"unsupported Git diff row: {line}",
        )
        changes.append(ChangedPathV1(status=normalized_status, path=fields[1]))
    return tuple(changes)


def _parse_changed_file(value: str) -> ChangedPathV1:
    status, separator, path = value.partition(":")
    require(bool(separator), "--changed-file must use STATUS:path")
    return ChangedPathV1(status=status, path=path)


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--evidence-dir", type=Path, default=DEFAULT_EVIDENCE_DIR)
    parser.add_argument("--base-ref")
    parser.add_argument("--changed-file", action="append", default=[])
    parser.add_argument("--emit-pytest-nodes", action="store_true")
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        require(
            not (args.base_ref and args.changed_file),
            "use either --base-ref or --changed-file",
        )
        changed = (
            collect_git_changed_paths(REPO_ROOT, cast(str, args.base_ref))
            if args.base_ref
            else tuple(
                _parse_changed_file(value)
                for value in cast(list[str], args.changed_file)
            )
        )
        report = check_repository(
            repo_root=REPO_ROOT,
            contract_path=cast(Path, args.contract),
            evidence_dir=cast(Path, args.evidence_dir),
            changed_paths=changed,
        )
    except TestHygieneError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if args.emit_pytest_nodes:
        for node_id in cast(list[str], report["pytest_node_ids"]):
            print(node_id)
    elif args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        rows = cast(dict[str, int], report["mutation_rows"])
        print(
            "test-hygiene-v1: ok "
            f"packets={report['evidence_packet_count']} "
            f"critical={report['critical_path_count']} "
            f"mutation_rows=mechanical:{rows['mechanical']}"
            f"/narrative:{rows['narrative']}/legacy:{rows['legacy']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
