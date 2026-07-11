"""Live-gated canonical evidence writer for retained ZRPF V3 replay."""

from __future__ import annotations

import importlib
from pathlib import Path
from typing import Any

_MODULE_PREFIX = "tools." if __package__ else ""
support = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_evidence_support")


def write_after_verified_live(
    path: Path,
    report: dict[str, Any],
    repo_root: Path = support.REPO_ROOT,
) -> None:
    document = support.expected_evidence(repo_root)
    _require_recordable_live_facts(report.get("live"), document)
    if report.get("ok") is not True:
        raise RuntimeError("verified live replay report is required")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as handle:
        handle.write(support.canonical_evidence_bytes(document))


def _require_recordable_live_facts(live: Any, document: dict[str, Any]) -> None:
    if not isinstance(live, dict):
        raise RuntimeError("verified live replay facts are required")
    recorded = document["recorded_execution"]
    build = document["recorded_build"]
    expected_negatives = [row | {"passed": True} for row in recorded["negative_controls"]]
    expected_versions = {
        "cargo": build["cargo_version"],
        "rustc": build["rustc_version"],
        "rustdoc": build["rustdoc_version"],
    }
    required = (
        live.get("executed") is True,
        live.get("verified") is True,
        live.get("normal_and_dev_stdout_identical") is True,
        live.get("stdout_sha256") == recorded["stdout_sha256"],
        live.get("stdout_size_bytes") == recorded["stdout_size_bytes"],
        live.get("negative_controls") == expected_negatives,
        live.get("toolchain_versions") == expected_versions,
        _is_positive_int(live.get("binary_size_bytes")),
        _is_positive_int(live.get("dependency_graph_package_count")),
        _is_sha256(live.get("binary_sha256")),
        _is_sha256(live.get("dependency_graph_sha256")),
    )
    if not all(required):
        raise RuntimeError("live replay facts do not authorize evidence creation")


def _is_positive_int(value: Any) -> bool:
    return type(value) is int and value > 0


def _is_sha256(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )
