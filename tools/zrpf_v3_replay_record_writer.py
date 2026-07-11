"""Live-gated canonical evidence writer for retained ZRPF V3 replay."""

from __future__ import annotations

import importlib
from pathlib import Path
from typing import Any

_MODULE_PREFIX = "tools." if __package__ else ""
support = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_evidence_support")
privacy = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_artifact_privacy")


def write_after_verified_live(
    path: Path,
    report: dict[str, Any],
    repo_root: Path = support.REPO_ROOT,
) -> None:
    live = report.get("live")
    identity = _execution_identity(live)
    document = support.expected_evidence(identity, repo_root)
    _require_recordable_live_facts(live, document)
    if report.get("ok") is not True:
        raise RuntimeError("verified live replay report is required")
    raw = support.canonical_evidence_bytes(document)
    _require_clean_public_artifacts(repo_root, raw)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as handle:
        handle.write(raw)


def _require_clean_public_artifacts(repo_root: Path, candidate: bytes) -> None:
    existing = privacy.scan_artifacts(repo_root, privacy.PRE_RECORD_ARTIFACTS)
    proposed = privacy.scan_candidate_bytes(privacy.EVIDENCE_ARTIFACT, candidate)
    if existing.get("ok") is not True or proposed.get("ok") is not True:
        raise RuntimeError("public artifact privacy scan rejected evidence creation")


def _execution_identity(live: Any) -> dict[str, Any]:
    if not isinstance(live, dict):
        raise RuntimeError("verified live replay facts are required")
    try:
        return support.exact_execution_identity(
            {
                "binary_sha256": live.get("binary_sha256"),
                "binary_size_bytes": live.get("binary_size_bytes"),
                "binary_transport": live.get("binary_transport"),
                "dependency_graph_package_count": live.get(
                    "dependency_graph_package_count"
                ),
                "dependency_graph_sha256": live.get("dependency_graph_sha256"),
            }
        )
    except ValueError as exc:
        raise RuntimeError("live execution identity is malformed") from exc


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
        live.get("binary_sha256") == recorded["executing_binary_sha256"],
        live.get("binary_size_bytes") == recorded["executing_binary_size_bytes"],
        live.get("binary_transport") == recorded["binary_transport"],
        live.get("dependency_graph_package_count")
        == build["dependency_graph_package_count"],
        live.get("dependency_graph_sha256") == build["dependency_graph_sha256"],
    )
    if not all(required):
        raise RuntimeError("live replay facts do not authorize evidence creation")
