#!/usr/bin/env python3
"""Build the fail-closed FCIS M5-P4A cross-consumer parity matrix.

Source presence never counts as byte-level parity.  A row may use
``PASS_EXACT_BYTES`` only when it binds a replay artifact containing the same
fixture set and all normative observables.  P4A has no such promoted
cross-language artifact, so the matrix records the missing evidence directly.
"""

# ruff: noqa: E402 -- the executable tool must add the repository root before src imports

from __future__ import annotations

import hashlib
import json
import sys
from collections import Counter
from pathlib import Path
from typing import cast

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from src.runtime.authority import (
    PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES,
    TRUSTED_CORE_AUTHORITY_SURFACES,
)
from src.state.canonical import canonical_json_bytes

_REPORT_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_CROSS_LANGUAGE_MATRIX_V1.json"
_BASELINE_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_LEGACY_BASELINE_V1.json"
_DIFFERENTIAL_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_DIFFERENTIAL_REPLAY_V1.json"
_MOUNT_GRAPH_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_MOUNT_CALL_GRAPH_V1.json"
_SCHEMA = "zenodex/fcis-m5-p4a-cross-language-matrix/v1"
_REVIEWED_START_SHA = "c344bac741c1d4a15511b77f8e2b60f93260a449"
_CLOSED_STATUSES = frozenset(
    {
        "PASS_EXACT_BYTES",
        "UNPROMOTED_SHADOW_ONLY",
        "MISSING_BLOCKER",
        "NOT_APPLICABLE_WITH_REASON",
    }
)
_CONSUMERS = (
    "python_fcis",
    "rust_runtime",
    "tau_adapter",
    "proof_guest",
    "settlement_verifier",
)


class DuplicateJsonKey(ValueError):
    """Raised when a generated artifact repeats a JSON object key."""


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateJsonKey(key)
        result[key] = value
    return result


def _load_object(path: Path) -> dict[str, object]:
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_strict_object,
    )
    if type(value) is not dict:
        raise ValueError(f"{path.name} must contain one JSON object")
    return cast(dict[str, object], value)


def _sha256(raw: bytes) -> str:
    return "0x" + hashlib.sha256(raw).hexdigest()


def _artifact_payload(value: dict[str, object]) -> bytes:
    payload = dict(value)
    payload.pop("artifact_sha256", None)
    return canonical_json_bytes(payload)


def _assert_artifact_hash(path: Path, value: dict[str, object]) -> None:
    claimed = value.get("artifact_sha256")
    if type(claimed) is not str:
        raise ValueError(f"{path.name} lacks artifact_sha256")
    actual = _sha256(_artifact_payload(value))
    if claimed != actual:
        raise ValueError(f"{path.name} artifact_sha256 mismatch")


def _with_artifact_hash(value: dict[str, object]) -> dict[str, object]:
    result = dict(value)
    result["artifact_sha256"] = _sha256(_artifact_payload(result))
    return result


def _evidence_reference(path: Path) -> dict[str, object]:
    return {
        "path": path.relative_to(_REPO_ROOT).as_posix(),
        "file_sha256": _sha256(path.read_bytes()),
    }


def _baseline_commands(baseline: dict[str, object]) -> list[dict[str, object]]:
    raw = baseline.get("command_inventory")
    if type(raw) is not list or any(type(row) is not dict for row in raw):
        raise ValueError("baseline command_inventory is malformed")
    rows = cast(list[dict[str, object]], raw)
    result: list[dict[str, object]] = []
    seen: set[str] = set()
    for row in rows:
        command = row.get("command_kind")
        if type(command) is not str or command in seen:
            raise ValueError("baseline command inventory is not unique")
        seen.add(command)
        evidence = row.get("source_evidence")
        if type(evidence) is not list or any(type(item) is not str for item in evidence):
            raise ValueError("baseline command source evidence is malformed")
        result.append(
            {
                "surface_id": f"command:{command}",
                "surface_kind": "MOUNTED_COMMAND",
                "source_evidence": list(cast(list[str], evidence)),
                "required_for_public_testnet": True,
            }
        )
    return sorted(result, key=lambda row: cast(str, row["surface_id"]))


def _mount_surfaces(mount_graph: dict[str, object]) -> list[dict[str, object]]:
    raw = mount_graph.get("source_rows")
    if type(raw) is not list or any(type(row) is not dict for row in raw):
        raise ValueError("mount graph source_rows is malformed")
    violation_paths_raw = mount_graph.get("violation_counts_by_path")
    if type(violation_paths_raw) is not dict:
        raise ValueError("mount graph violation_counts_by_path is malformed")
    violation_paths = set(cast(dict[str, object], violation_paths_raw))
    result: list[dict[str, object]] = []
    for row in cast(list[dict[str, object]], raw):
        path = row.get("path")
        role = row.get("source_role")
        source_hash = row.get("source_sha256")
        if type(path) is not str or type(role) is not str or type(source_hash) is not str:
            raise ValueError("mount graph source identity is malformed")
        result.append(
            {
                "surface_id": f"authority_path:{path}",
                "surface_kind": "FINAL_MOUNT_PROFILE_PATH",
                "source_evidence": [f"{path}@{source_hash}"],
                "required_for_public_testnet": True,
                "has_structural_blocker": path in violation_paths,
                "role": role,
            }
        )
    return sorted(result, key=lambda row: cast(str, row["surface_id"]))


def _trusted_core_surfaces() -> list[dict[str, object]]:
    required = PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES
    return [
        {
            "surface_id": f"trusted_core:{surface}",
            "surface_kind": "RUNTIME_AUTHORITY_POLICY_SURFACE",
            "source_evidence": ["src/runtime/authority.py"],
            "required_for_public_testnet": surface in required,
        }
        for surface in sorted(TRUSTED_CORE_AUTHORITY_SURFACES)
    ]


def _row_status(surface: dict[str, object], consumer: str) -> tuple[str, str]:
    if consumer == "python_fcis" and not surface.get("has_structural_blocker", False):
        return (
            "UNPROMOTED_SHADOW_ONLY",
            "Python FCIS code exists only as an unpromoted shadow; exact legacy parity is open.",
        )
    if consumer == "python_fcis":
        return (
            "MISSING_BLOCKER",
            "The final-mount structural checker reports an unresolved authority violation.",
        )
    return (
        "MISSING_BLOCKER",
        f"No source-pinned all-observable exact-byte replay promotes {consumer} for this surface.",
    )


def _matrix_rows(
    surfaces: list[dict[str, object]],
    evidence: list[dict[str, object]],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for surface in surfaces:
        for consumer in _CONSUMERS:
            status, reason = _row_status(surface, consumer)
            if status not in _CLOSED_STATUSES:
                raise AssertionError("matrix builder emitted unknown status")
            rows.append(
                {
                    "surface_id": surface["surface_id"],
                    "surface_kind": surface["surface_kind"],
                    "consumer": consumer,
                    "status": status,
                    "reason": reason,
                    "required_equivalence": (
                        "canonical acceptance/rejection and byte-identical state, "
                        "effects, receipt, replay, outbox, fees, roots, and versions"
                    ),
                    "source_evidence": surface["source_evidence"],
                    "parity_evidence": evidence,
                    "required_for_public_testnet": surface["required_for_public_testnet"],
                }
            )
    return sorted(
        rows,
        key=lambda row: (
            cast(str, row["surface_id"]),
            cast(str, row["consumer"]),
        ),
    )


def build_cross_language_matrix_v1() -> dict[str, object]:
    baseline = _load_object(_BASELINE_PATH)
    differential = _load_object(_DIFFERENTIAL_PATH)
    mount_graph = _load_object(_MOUNT_GRAPH_PATH)
    _assert_artifact_hash(_BASELINE_PATH, baseline)
    _assert_artifact_hash(_DIFFERENTIAL_PATH, differential)
    _assert_artifact_hash(_MOUNT_GRAPH_PATH, mount_graph)
    if baseline.get("reviewed_source_sha") != _REVIEWED_START_SHA:
        raise ValueError("baseline is not bound to reviewed P4A start SHA")
    if mount_graph.get("reviewed_start_sha") != _REVIEWED_START_SHA:
        raise ValueError("mount graph is not bound to reviewed P4A start SHA")
    surfaces = [
        *_baseline_commands(baseline),
        *_trusted_core_surfaces(),
        *_mount_surfaces(mount_graph),
    ]
    surface_ids = [cast(str, row["surface_id"]) for row in surfaces]
    if len(surface_ids) != len(set(surface_ids)):
        raise ValueError("cross-language surface inventory contains duplicates")
    evidence = [
        _evidence_reference(_BASELINE_PATH),
        _evidence_reference(_DIFFERENTIAL_PATH),
        _evidence_reference(_MOUNT_GRAPH_PATH),
    ]
    rows = _matrix_rows(surfaces, evidence)
    counts = Counter(cast(str, row["status"]) for row in rows)
    promoted = all(
        row["status"] in {"PASS_EXACT_BYTES", "NOT_APPLICABLE_WITH_REASON"} for row in rows
    )
    artifact: dict[str, object] = {
        "schema": _SCHEMA,
        "reviewed_start_sha": _REVIEWED_START_SHA,
        "generator_path": Path(__file__).resolve().relative_to(_REPO_ROOT).as_posix(),
        "generator_sha256": _sha256(Path(__file__).read_bytes()),
        "closed_statuses": sorted(_CLOSED_STATUSES),
        "consumers": list(_CONSUMERS),
        "surface_count": len(surfaces),
        "row_count": len(rows),
        "rows": rows,
        "status_counts": dict(sorted(counts.items())),
        "pass_exact_bytes_count": counts.get("PASS_EXACT_BYTES", 0),
        "ready_for_mount": promoted,
        "overall_status": "PASS_EXACT_BYTES" if promoted else "MISSING_BLOCKER",
        "nonclaims": [
            "A source file or verifier entrypoint is not cross-language parity evidence.",
            "No P4A row is promoted by implementation-presence inference.",
            "The current differential artifact reports open versioned divergences.",
        ],
    }
    return _with_artifact_hash(artifact)


def _write(artifact: dict[str, object]) -> None:
    _REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    _REPORT_PATH.write_bytes(canonical_json_bytes(artifact))


def main() -> int:
    artifact = build_cross_language_matrix_v1()
    expected = canonical_json_bytes(artifact)
    if "--check" in sys.argv:
        if not _REPORT_PATH.is_file():
            print(f"ERROR: missing {_REPORT_PATH.relative_to(_REPO_ROOT)}", file=sys.stderr)
            return 1
        if _REPORT_PATH.read_bytes() != expected:
            print("ERROR: cross-language matrix is stale", file=sys.stderr)
            return 1
        print(
            "OK: cross-language matrix is current "
            f"(exact_passes={artifact['pass_exact_bytes_count']}, "
            f"ready={artifact['ready_for_mount']})"
        )
        return 0
    _write(artifact)
    print(
        f"OK: wrote {_REPORT_PATH.relative_to(_REPO_ROOT)} "
        f"(exact_passes={artifact['pass_exact_bytes_count']}, "
        f"ready={artifact['ready_for_mount']})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
