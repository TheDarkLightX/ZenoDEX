#!/usr/bin/env python3
"""Replay and check the exact research-only current-Tau incompatibility artifact."""

# ruff: noqa: E402 -- the isolated-path bootstrap must precede all non-builtin imports.

from __future__ import annotations

import sys as _bootstrap_sys


def _require_isolated_python_main_v1() -> None:
    """Fail before repository imports unless Python excluded ambient paths."""

    if not _bootstrap_sys.flags.isolated or not _bootstrap_sys.flags.safe_path:
        _bootstrap_sys.stdout.write(
            '{"artifact_root":null,"artifact_sha256":"",'
            '"current_tau_compatible":false,"findings":'
            '[{"code":"PYTHON_NOT_ISOLATED","path":"python"}],"o002_implemented":false,'
            '"o003a_evidence_complete":false,"ok":false,'
            '"production_authority":"NONE","release_authority":"NONE",'
            '"route_quarantine_implemented":false,"schema":'
            '"zenodex/current-tau-compatibility-check/v1",'
            '"settlement_authority":"NONE","value_movement_authority":"NONE",'
            '"value_movement_claim_allowed":false,"vm_gates_closed":[]}\n'
        )
        raise SystemExit(1)
    import os as bootstrap_os

    repo_root = bootstrap_os.path.dirname(
        bootstrap_os.path.dirname(bootstrap_os.path.realpath(__file__))
    )
    trusted_runtime_paths = [
        entry
        for entry in _bootstrap_sys.path
        if entry
        and "site-packages" not in entry
        and "dist-packages" not in entry
    ]
    _bootstrap_sys.path[:] = [*trusted_runtime_paths, repo_root]


if __name__ == "__main__":
    _require_isolated_python_main_v1()

import json
import sys
from pathlib import Path
from typing import Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.build_current_tau_compatibility_v1 import (  # noqa: E402
    JSON_OUTPUT,
    MAX_ARTIFACT_BYTES_V1,
    TauReplayPathsV1,
    load_current_tau_compatibility_snapshot_v1,
)
from tools.current_tau_compatibility_core_v1 import (  # noqa: E402
    CHECK_SCHEMA_V1,
    CurrentTauCompatibilityRejectV1,
    canonical_json_bytes_v1,
    check_current_tau_compatibility_artifact_v1,
    decode_json_object_v1,
)
from tools.current_tau_replay_io_v1 import (  # noqa: E402
    FailClosedArgumentParserV1,
    ShellRejectV1,
    _read_bounded_regular_file_v1,
)


def _failure_report(code: str, path: str) -> dict[str, object]:
    return {
        "schema": CHECK_SCHEMA_V1,
        "ok": False,
        "findings": [{"code": code, "path": path}],
        "artifact_sha256": "",
        "artifact_root": None,
        "o003a_evidence_complete": False,
        "route_quarantine_implemented": False,
        "current_tau_compatible": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "value_movement_claim_allowed": False,
        "o002_implemented": False,
        "vm_gates_closed": [],
    }


def check_current_tau_compatibility_v1(
    *,
    paths: TauReplayPathsV1,
    artifact_path: Path | None = None,
) -> dict[str, object]:
    """Recompute source facts, then compare one canonical artifact byte-for-byte."""

    source = artifact_path or paths.root / JSON_OUTPUT
    try:
        raw_artifact = _read_bounded_regular_file_v1(
            source,
            MAX_ARTIFACT_BYTES_V1,
            "current Tau compatibility artifact",
        )
        artifact = decode_json_object_v1(raw_artifact, "current Tau compatibility artifact")
        if canonical_json_bytes_v1(artifact) != raw_artifact:
            return _failure_report("NONCANONICAL_ARTIFACT", str(source))
        snapshot = load_current_tau_compatibility_snapshot_v1(paths)
        return check_current_tau_compatibility_artifact_v1(
            artifact,
            raw_artifact,
            snapshot,
        )
    except (CurrentTauCompatibilityRejectV1, ShellRejectV1) as exc:
        return _failure_report(exc.code, exc.path)
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        return _failure_report("CHECKER_INPUT_ERROR", type(exc).__name__)
    except Exception:
        return _failure_report("CHECKER_INTERNAL_ERROR", "internal")


def main(argv: list[str] | None = None) -> int:
    parser = FailClosedArgumentParserV1(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--tau-testnet-repo", type=Path, required=True)
    parser.add_argument("--tau-lang-repo", type=Path, required=True)
    parser.add_argument("--historical-bridge-repo", type=Path)
    try:
        args = parser.parse_args(argv)
        bridge_repo = args.historical_bridge_repo or args.tau_testnet_repo
        paths = TauReplayPathsV1(
            args.root,
            args.tau_testnet_repo,
            args.tau_lang_repo,
            bridge_repo,
        )
        report = check_current_tau_compatibility_v1(paths=paths)
    except ShellRejectV1 as exc:
        report = _failure_report(exc.code, exc.path)
    except Exception:
        report = _failure_report("CHECKER_INTERNAL_ERROR", "internal")
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
