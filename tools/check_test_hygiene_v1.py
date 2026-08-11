#!/usr/bin/env python3
"""Validate Test Hygiene Contract V1 and changed-file evidence.

With ``--base-ref`` or ``--changed-file``, every changed critical path requires
a current source-pinned evidence packet. Static mode validates closed schemas
while retaining historical packets as immutable replay records.
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

from tools.test_hygiene_evidence_v1 import load_packets
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


def check_repository(
    *,
    repo_root: Path = REPO_ROOT,
    contract_path: Path = DEFAULT_CONTRACT,
    evidence_dir: Path = DEFAULT_EVIDENCE_DIR,
    changed_paths: Sequence[ChangedPathV1] = (),
) -> dict[str, object]:
    """Validate contract structure and optional changed-file coverage."""

    contract = load_contract(contract_path)
    packets = load_packets(evidence_dir, contract)
    normalized = tuple(
        sorted(set(changed_paths), key=lambda item: (item.path, item.status))
    )
    _reject_packet_rewrites(normalized, evidence_prefix=contract.evidence_path_prefix)

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
        print(
            "test-hygiene-v1: ok "
            f"packets={report['evidence_packet_count']} "
            f"critical={report['critical_path_count']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
