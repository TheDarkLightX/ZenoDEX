#!/usr/bin/env python3
"""Render the append-only hygiene packet for the bounded ZRPF preservation diff.

The renderer accepts either the current Git index or one exact base-to-HEAD
diff. It selects paths governed by Test Hygiene Contract V1, hashes their
current bytes, discovers deterministic pytest node IDs with the Python AST, and
emits one canonical evidence packet. Deleted and renamed critical paths reject.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Sequence, cast

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.test_hygiene_model_v1 import DEFAULT_CONTRACT, load_contract

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "tests/evidence/test_hygiene/"
    "THV1-20260811-zrpf-fcis-preservation-snapshot.json"
)
EVIDENCE_ID = "THV1-20260811-zrpf-fcis-preservation-snapshot"
ALLOWED_STATUSES = frozenset({"A", "M"})


class RenderError(RuntimeError):
    """Raised when the staged preservation scope is ambiguous or stale."""


@dataclass(frozen=True, slots=True)
class ChangedPath:
    status: str
    path: str


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _portable_path(raw_path: str) -> str:
    pure = PurePosixPath(raw_path)
    if pure.is_absolute() or ".." in pure.parts or "." in pure.parts:
        raise RenderError(f"non-portable changed path: {raw_path}")
    return pure.as_posix()


def _git_diff(*, cached: bool, base_ref: str | None) -> tuple[ChangedPath, ...]:
    command = ["git", "diff"]
    if cached:
        command.append("--cached")
    command.extend(["--name-status", "--find-renames"])
    if base_ref is not None:
        command.extend([base_ref, "HEAD"])
    try:
        output = subprocess.run(
            command,
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as exc:
        raise RenderError(f"failed to collect Git preservation diff: {exc}") from exc

    changes: list[ChangedPath] = []
    for line in output.splitlines():
        fields = line.split("\t")
        status = fields[0][:1]
        if status not in ALLOWED_STATUSES or len(fields) != 2:
            raise RenderError(f"unsupported preservation diff row: {line}")
        changes.append(ChangedPath(status, _portable_path(fields[1])))
    if not changes:
        raise RenderError("preservation diff is empty")
    return tuple(sorted(set(changes), key=lambda item: item.path))


def _pytest_nodes(path: str, source: str) -> list[str]:
    try:
        module = ast.parse(source, filename=path)
    except SyntaxError as exc:
        raise RenderError(f"cannot parse staged Python test {path}: {exc}") from exc
    nodes: list[str] = []
    for item in module.body:
        if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if item.name.startswith("test_"):
                nodes.append(f"{path}::{item.name}")
            continue
        if isinstance(item, ast.ClassDef) and item.name.startswith("Test"):
            for child in item.body:
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)) and (
                    child.name.startswith("test_")
                ):
                    nodes.append(f"{path}::{item.name}::{child.name}")
    if not nodes:
        raise RenderError(f"critical Python test has no pytest node: {path}")
    return nodes


def _packet(changes: tuple[ChangedPath, ...]) -> dict[str, Any]:
    contract = load_contract(DEFAULT_CONTRACT)
    source_pins: list[dict[str, str]] = []
    test_pins: list[dict[str, object]] = []
    for change in changes:
        if not any(rule.matches(change.path) for rule in contract.rules):
            continue
        absolute = REPO_ROOT / change.path
        if not absolute.is_file():
            raise RenderError(f"critical staged path is missing: {change.path}")
        digest = _sha256_file(absolute)
        if change.path.startswith("tests/") and change.path.endswith(".py"):
            source = absolute.read_text(encoding="utf-8")
            test_pins.append(
                {
                    "path": change.path,
                    "sha256": digest,
                    "node_ids": _pytest_nodes(change.path, source),
                }
            )
        else:
            source_pins.append({"path": change.path, "sha256": digest})
    if not source_pins or not test_pins:
        raise RenderError("preservation packet requires source and test pins")

    hygiene_missing = (
        "tests/test_check_test_hygiene_v1.py::"
        "test_changed_critical_path_requires_evidence_packet"
    )
    hygiene_drift = (
        "tests/test_check_test_hygiene_v1.py::test_stale_source_pin_rejects_packet"
    )
    effect_relabel = (
        "tests/core/test_global_settlement_abi_v1.py::"
        "test_epoch_rejects_global_effect_plan_unrelated_to_verified_route_effects"
    )
    pinned_nodes = {
        cast(str, node)
        for pin in test_pins
        for node in cast(list[object], pin["node_ids"])
    }
    required_killers = {hygiene_missing, hygiene_drift, effect_relabel}
    if not required_killers <= pinned_nodes:
        missing = sorted(required_killers - pinned_nodes)
        raise RenderError(f"preservation mutation killers are absent: {missing}")

    return {
        "schema": "zenodex/test-hygiene-evidence/v1",
        "evidence_id": EVIDENCE_ID,
        "created_date": "2026-08-11",
        "claim_scope": (
            "The bounded staged ZRPF/FCIS preservation snapshot has exact current "
            "source and test hashes, executable Python nodes, Rust parity gates, "
            "and fail-closed evidence metadata without granting production authority."
        ),
        "change_kind": "assurance_infrastructure",
        "risk_class": "authority",
        "invariant_ids": [
            "ZRPF-PRESERVATION-SNAPSHOT-IS-CLOSED",
            "ZRPF-PRESERVATION-PINS-MATCH-CURRENT-BYTES",
            "ZRPF-PRESERVATION-RETAINS-NEGATIVE-EVIDENCE",
            "ZRPF-PRESERVATION-GRANTS-NO-PRODUCTION-AUTHORITY",
        ],
        "failure_modes": [
            "a critical staged path is omitted from current evidence",
            "a source or test changes after the preservation packet is rendered",
            "the epoch effect plan is relabeled independently of verified route effects",
            "a historical evidence packet is treated as current after source evolution",
        ],
        "source_pins": source_pins,
        "removed_paths": [],
        "test_pins": test_pins,
        "evidence_families": [
            "aaa_regression",
            "negative_regression",
            "boundary",
            "differential",
            "stateful",
            "mutation",
            "replay",
        ],
        "aaa": {
            "status": "applied",
            "reason": (
                "Pinned tests arrange typed state and adversarial mutations, act "
                "through deterministic cores or fail-closed checkers, and assert "
                "exact acceptance, rejection, roots, effects, and no-op behavior."
            ),
        },
        "reject_is_noop": {
            "status": "applied",
            "reason": (
                "Receipt, composition, replay, migration, and hygiene regressions "
                "assert rejection before witness creation or durable mutation."
            ),
        },
        "boundary_dimensions": [
            {
                "name": "epoch_route_count",
                "points": [
                    "zero_rejects",
                    "one_accepts",
                    "eight_accepts",
                    "nine_accepts",
                    "sixty_four_accepts",
                    "sixty_five_rejects",
                ],
            },
            {
                "name": "source_pin_freshness",
                "points": ["exact_current_bytes_accept", "one_byte_drift_rejects"],
            },
            {
                "name": "receipt_binding",
                "points": ["exact_journal_accepts", "foreign_or_relabelled_journal_rejects"],
            },
        ],
        "mutations": [
            {
                "description": "allow a changed critical path without current evidence",
                "killed_by": hygiene_missing,
            },
            {
                "description": "accept a stale source hash in the selected evidence packet",
                "killed_by": hygiene_drift,
            },
            {
                "description": "allow an unrelated epoch effect plan beside valid route evidence",
                "killed_by": effect_relabel,
            },
        ],
        "nonclaims": [
            "This is a research-only preservation snapshot and grants no settlement, publication, migration, or writer capability.",
            "Host and static guest tests do not establish complete recursive-proof soundness or production verifier governance.",
            "Real RISC0 proof regeneration and high-load recursion remain deferred to Runpod.",
            "The current effect composer remains restricted to sequential ASSET_TRANSFER routes without terminal or external-outbox composition.",
            "The broader M6 safe-mount and whole-economy candidate is outside this replayable snapshot.",
        ],
    }


def _canonical_bytes(packet: dict[str, Any]) -> bytes:
    return (json.dumps(packet, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def _write_atomic(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as handle:
        temporary = Path(handle.name)
        handle.write(payload)
        handle.flush()
        os.fsync(handle.fileno())
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--cached", action="store_true")
    source.add_argument("--base-ref")
    output = parser.add_mutually_exclusive_group(required=True)
    output.add_argument("--write", type=Path)
    output.add_argument("--check", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args([] if argv is None else argv)
    changes = _git_diff(cached=bool(args.cached), base_ref=cast(str | None, args.base_ref))
    payload = _canonical_bytes(_packet(changes))
    write_path = cast(Path | None, args.write)
    if write_path is not None:
        _write_atomic(write_path, payload)
        print(f"wrote ZRPF preservation packet: {write_path}")
        return 0
    check_path = cast(Path, args.check)
    try:
        current = check_path.read_bytes()
    except OSError as exc:
        raise RenderError(f"cannot read preservation packet {check_path}: {exc}") from exc
    if current != payload:
        raise RenderError(f"preservation packet drift: {check_path}")
    print(f"ZRPF preservation packet match: {check_path}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except RenderError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
