#!/usr/bin/env python3
"""Fail closed when the exact O-004 operator-surface registry drifts."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.operator_surface_registry_v1 import (  # noqa: E402
    ARTIFACT_RELATIVE_PATH_V1,
    check_registry_v1,
)


def check_operator_surface_registry_v1(
    root: Path = REPO_ROOT,
    artifact_path: Path | None = None,
) -> dict[str, object]:
    """Validate one registry against pinned implementation Git objects."""

    return check_registry_v1(root, artifact_path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument(
        "--registry",
        type=Path,
        help="optional registry path; a relative path is interpreted below --root",
    )
    parser.add_argument("--json", action="store_true", help="emit the machine-readable report")
    args = parser.parse_args(argv)
    artifact_path = args.registry
    if artifact_path is not None and not artifact_path.is_absolute():
        artifact_path = args.root / artifact_path
    if artifact_path is None:
        artifact_path = args.root / ARTIFACT_RELATIVE_PATH_V1
    report = check_operator_surface_registry_v1(args.root, artifact_path)
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
