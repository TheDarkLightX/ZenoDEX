#!/usr/bin/env python3
"""Bounded privacy scan for the exact final V6 local-evidence artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any

if __package__:
    from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence
    from tools import zrpf_v3_artifact_privacy as privacy
else:
    sys.path.insert(0, Path(__file__).resolve().parents[1].as_posix())
    from tools import check_zrpf_source_opened_spot_v6_local_evidence as evidence
    from tools import zrpf_v3_artifact_privacy as privacy

REPORT_SCHEMA = "zenodex/zrpf_source_opened_spot_v6_artifact_privacy_scan/v1"

FINAL_ARTIFACTS: tuple[privacy.ArtifactSpec, ...] = tuple(
    privacy.ArtifactSpec(path, artifact_id)
    for artifact_id, path, _kind in evidence.ARTIFACT_SPECS
)


def scan_artifact_directory(root: Path) -> dict[str, Any]:
    """Scan exactly the governed flat V6 inventory under one supplied root."""

    expected_names = {artifact.relative_path for artifact in FINAL_ARTIFACTS}
    observed_names, inventory_errors = _read_exact_inventory(root, expected_names)
    base = privacy.scan_artifacts(root, FINAL_ARTIFACTS)
    errors = [*base["errors"], *inventory_errors]
    errors.sort(key=lambda row: (row["path"], row["role"], row["code"]))
    artifact_set_sha256 = _artifact_set_sha256(base["artifacts"])
    return {
        "artifact_count_expected": len(FINAL_ARTIFACTS),
        "artifact_count_observed": len(observed_names),
        "artifact_count_scanned": base["artifact_count_scanned"],
        "artifact_set_sha256": artifact_set_sha256,
        "artifacts": base["artifacts"],
        "complete_artifact_privacy_verified": False,
        "error_count": len(errors),
        "errors": errors,
        "finding_count": base["finding_count"],
        "findings": base["findings"],
        "inventory_names_sha256": _inventory_names_sha256(observed_names),
        "negative_knowledge": (
            "This bounded denylist detects the configured path, email, token, "
            "credential, and private-key patterns in the exact V6 artifact set. "
            "A clean scan does not prove complete artifact privacy or the absence "
            "of unmodeled secrets, covert channels, or side channels."
        ),
        "ok": base["ok"] is True and not inventory_errors,
        "schema": REPORT_SCHEMA,
        "total_bytes_scanned": base["total_bytes_scanned"],
    }


def _read_exact_inventory(
    root: Path,
    expected_names: set[str],
) -> tuple[list[str], list[dict[str, str]]]:
    try:
        descriptor = privacy._open_root(root)
    except privacy.ArtifactReadError as exc:
        return [], [_error(".", "inventory", exc.code)]
    try:
        observed_names = sorted(os.listdir(descriptor))
    except OSError:
        return [], [_error(".", "inventory", "inventory_unavailable")]
    finally:
        os.close(descriptor)

    observed = set(observed_names)
    errors = [
        _error(path, "inventory", "governed_artifact_missing")
        for path in sorted(expected_names - observed)
    ]
    if observed - expected_names:
        # Extra names are not echoed because their names may themselves leak data.
        errors.append(_error(".", "inventory", "extra_governed_inventory"))
    return observed_names, errors


def _inventory_names_sha256(names: list[str]) -> str:
    hasher = hashlib.sha256()
    hasher.update(b"zenodex.zrpf.source_opened_spot_v6.inventory.v1\0")
    for name in names:
        encoded = name.encode("utf-8", errors="surrogateescape")
        hasher.update(len(encoded).to_bytes(4, "big"))
        hasher.update(encoded)
    return hasher.hexdigest()


def _artifact_set_sha256(artifacts: list[dict[str, Any]]) -> str:
    hasher = hashlib.sha256()
    hasher.update(b"zenodex.zrpf.source_opened_spot_v6.artifact_set.v1\0")
    for artifact in artifacts:
        path = artifact["path"].encode("utf-8")
        role = artifact["role"].encode("utf-8")
        digest = bytes.fromhex(artifact["sha256"])
        size = artifact["size_bytes"]
        hasher.update(len(path).to_bytes(4, "big"))
        hasher.update(path)
        hasher.update(len(role).to_bytes(4, "big"))
        hasher.update(role)
        hasher.update(size.to_bytes(8, "big"))
        hasher.update(digest)
    return hasher.hexdigest()


def _error(path: str, role: str, code: str) -> dict[str, str]:
    return {"code": code, "path": path, "role": role}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-directory", type=Path, required=True)
    arguments = parser.parse_args(argv)
    report = scan_artifact_directory(arguments.artifact_directory)
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
