#!/usr/bin/env python3
"""Validate obligation quality for the V1 packets selected by a candidate diff."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Sequence, cast

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.check_test_hygiene_v1 import (
    REPO_ROOT,
    ChangedPathV1,
    collect_git_changed_paths,
)
from tools.check_test_hygiene_v1 import check_repository as check_hygiene_repository
from tools.test_hygiene_evidence_v1 import load_packets as load_hygiene_packets
from tools.test_hygiene_model_v1 import (
    TestHygieneError,
    require,
)
from tools.test_hygiene_model_v1 import (
    load_contract as load_hygiene_contract,
)
from tools.test_quality_model_v2 import (
    CONTRACT_SCHEMA,
    DEFAULT_CONTRACT,
    DEFAULT_EVIDENCE_DIR,
    QualityContractV2,
    QualityPacketV2,
    load_quality_contract,
    load_quality_packets,
)


def _reject_quality_packet_rewrites(
    changed_paths: Sequence[ChangedPathV1], *, evidence_prefix: str
) -> None:
    for change in changed_paths:
        if change.path.startswith(evidence_prefix) and change.status != "A":
            raise TestHygieneError(
                f"quality evidence packets are append-only: {change.status}:{change.path}"
            )


def _parse_changed_file(value: str) -> ChangedPathV1:
    status, separator, path = value.partition(":")
    require(bool(separator), "--changed-file must use STATUS:path")
    return ChangedPathV1(status=status, path=path)


def _required_quality_by_hygiene_packet(
    *,
    changed_paths: Sequence[ChangedPathV1],
    hygiene_contract_path: Path,
    evidence_by_path: dict[str, str],
    quality_contract: QualityContractV2,
) -> dict[str, tuple[int, frozenset[str]]]:
    hygiene_contract = load_hygiene_contract(hygiene_contract_path)
    grades: dict[str, int] = defaultdict(int)
    kinds: dict[str, set[str]] = defaultdict(set)
    for change in changed_paths:
        evidence_id = evidence_by_path.get(change.path)
        if evidence_id is None:
            continue
        matching_rules = tuple(rule for rule in hygiene_contract.rules if rule.matches(change.path))
        for rule in matching_rules:
            requirement = quality_contract.requirement_for(rule.rule_id)
            grades[evidence_id] = max(grades[evidence_id], requirement.minimum_oracle_grade)
            kinds[evidence_id].update(requirement.required_falsifier_kinds)
    return {
        evidence_id: (grades[evidence_id], frozenset(kinds[evidence_id])) for evidence_id in grades
    }


def _validate_packet_against_hygiene(
    *,
    quality_packet: QualityPacketV2,
    hygiene_node_ids: frozenset[str],
    minimum_oracle_grade: int,
    required_falsifier_kinds: frozenset[str],
) -> None:
    require(
        quality_packet.oracle_grade >= minimum_oracle_grade,
        f"{quality_packet.evidence_id}: oracle independence grade is below the required minimum",
    )
    actual_kinds = frozenset(item.kind for item in quality_packet.falsifiers)
    require(
        required_falsifier_kinds <= actual_kinds,
        f"{quality_packet.evidence_id}: missing required executed falsifier kind",
    )
    for falsifier in quality_packet.falsifiers:
        unknown_nodes = sorted(set(falsifier.killed_by_node_ids) - hygiene_node_ids)
        require(
            not unknown_nodes,
            f"{quality_packet.evidence_id}: falsifier killer is not a selected pinned node: {unknown_nodes}",
        )


def check_test_quality_repository(
    *,
    repo_root: Path = REPO_ROOT,
    quality_contract_path: Path = DEFAULT_CONTRACT,
    quality_evidence_dir: Path = DEFAULT_EVIDENCE_DIR,
    changed_paths: Sequence[ChangedPathV1] = (),
) -> dict[str, object]:
    """Validate V1 executable coverage plus its linked V2 quality obligations."""

    quality_contract = load_quality_contract(quality_contract_path)
    hygiene_contract_path = repo_root / quality_contract.hygiene_contract_path
    hygiene_contract = load_hygiene_contract(hygiene_contract_path)
    hygiene_rule_ids = frozenset(rule.rule_id for rule in hygiene_contract.rules)
    quality_rule_ids = frozenset(
        requirement.rule_id for requirement in quality_contract.requirements
    )
    require(
        quality_rule_ids == hygiene_rule_ids,
        "quality contract rule ids must exactly match hygiene contract rule ids",
    )
    normalized = tuple(sorted(set(changed_paths), key=lambda item: (item.path, item.status)))
    _reject_quality_packet_rewrites(
        normalized, evidence_prefix=quality_contract.evidence_path_prefix
    )
    hygiene_report = check_hygiene_repository(
        repo_root=repo_root,
        contract_path=hygiene_contract_path,
        evidence_dir=repo_root / hygiene_contract.evidence_path_prefix,
        changed_paths=normalized,
    )
    quality_packets = load_quality_packets(quality_evidence_dir, quality_contract)
    hygiene_packets = load_hygiene_packets(
        repo_root / hygiene_contract.evidence_path_prefix, hygiene_contract
    )
    hygiene_by_id = {packet.evidence_id: packet for packet in hygiene_packets}
    for packet in quality_packets:
        require(
            packet.hygiene_evidence_id in hygiene_by_id,
            f"{packet.evidence_id}: linked hygiene evidence does not exist",
        )

    quality_by_hygiene_id = {packet.hygiene_evidence_id: packet for packet in quality_packets}
    evidence_by_path = cast(dict[str, str], hygiene_report["evidence_by_critical_path"])
    requirements = _required_quality_by_hygiene_packet(
        changed_paths=normalized,
        hygiene_contract_path=hygiene_contract_path,
        evidence_by_path=evidence_by_path,
        quality_contract=quality_contract,
    )
    selected_quality: dict[str, QualityPacketV2] = {}
    for hygiene_id, (minimum_grade, required_kinds) in requirements.items():
        quality_packet = quality_by_hygiene_id.get(hygiene_id)
        require(
            quality_packet is not None,
            f"selected hygiene evidence lacks V2 quality obligation: {hygiene_id}",
        )
        hygiene_packet = hygiene_by_id[hygiene_id]
        _validate_packet_against_hygiene(
            quality_packet=cast(QualityPacketV2, quality_packet),
            hygiene_node_ids=frozenset(hygiene_packet.node_ids),
            minimum_oracle_grade=minimum_grade,
            required_falsifier_kinds=required_kinds,
        )
        selected_quality[hygiene_id] = cast(QualityPacketV2, quality_packet)

    return {
        "ok": True,
        "contract_schema": CONTRACT_SCHEMA,
        "quality_packet_count": len(quality_packets),
        "changed_path_count": hygiene_report["changed_path_count"],
        "critical_path_count": hygiene_report["critical_path_count"],
        "covered_critical_paths": hygiene_report["covered_critical_paths"],
        "selected_hygiene_evidence_ids": sorted(selected_quality),
        "selected_quality_evidence_ids": sorted(
            packet.evidence_id for packet in selected_quality.values()
        ),
        "pytest_node_ids": hygiene_report["pytest_node_ids"],
    }


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--evidence-dir", type=Path, default=DEFAULT_EVIDENCE_DIR)
    parser.add_argument("--base-ref")
    parser.add_argument("--changed-file", action="append", default=[])
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
            else tuple(_parse_changed_file(value) for value in cast(list[str], args.changed_file))
        )
        report = check_test_quality_repository(
            repo_root=REPO_ROOT,
            quality_contract_path=cast(Path, args.contract),
            quality_evidence_dir=cast(Path, args.evidence_dir),
            changed_paths=changed,
        )
    except TestHygieneError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            "test-quality-v2: ok "
            f"packets={report['quality_packet_count']} "
            f"critical={report['critical_path_count']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
