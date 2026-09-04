#!/usr/bin/env python3
"""Replay the bounded Tau contract against an explicitly supplied toolchain."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SPEC = ROOT / "named_choice_fiber_polynomial_v1.tau"
PROFILE = ROOT / "tau_profile.json"
EXPECTED = [
    "T",
    "T",
    "F",
    "T",
    "T",
    "T",
    "T",
    "T",
    "T",
    "T",
    "T",
    "T",
    "F",
    "T",
    "T",
]
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
VERDICT = re.compile(r"%\d+\s*:\s*([TF])")


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _checked_text(args: list[str], cwd: Path) -> str:
    completed = subprocess.run(
        args,
        cwd=cwd,
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    return completed.stdout.strip()


def _arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tau-bin", type=Path, required=True)
    parser.add_argument("--tau-source", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = _arguments()
    profile = json.loads(PROFILE.read_text(encoding="utf-8"))
    actual_binary_sha = _sha256(args.tau_bin)
    if actual_binary_sha != profile["binary_sha256"]:
        raise SystemExit(f"TAU_BINARY_SHA_MISMATCH:{actual_binary_sha}")
    commit = _checked_text(["git", "rev-parse", "HEAD"], args.tau_source)
    if commit != profile["source_commit"]:
        raise SystemExit(f"TAU_COMMIT_MISMATCH:{commit}")
    version = _checked_text([str(args.tau_bin), "--version"], args.tau_source)
    if version != profile["version"]:
        raise SystemExit(f"TAU_VERSION_MISMATCH:{version}")

    completed = subprocess.run(
        [str(args.tau_bin), "-q"],
        cwd=ROOT,
        input=SPEC.read_text(encoding="utf-8"),
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    combined = ANSI.sub("", completed.stdout + completed.stderr)
    if completed.returncode != 0:
        raise SystemExit(f"TAU_NONZERO_EXIT:{completed.returncode}\n{combined[-2000:]}")
    if re.search(r"\berror\b", combined, flags=re.IGNORECASE):
        raise SystemExit(f"TAU_ERROR_MARKER\n{combined[-2000:]}")
    actual = VERDICT.findall(combined)
    if actual != EXPECTED:
        raise SystemExit(f"TAU_VERDICT_MISMATCH:expected={EXPECTED}:actual={actual}")

    print(
        json.dumps(
            {
                "actual": actual,
                "authority": "NONE",
                "claim_status": "BOUNDED_RESEARCH_ONLY",
                "expected": EXPECTED,
                "object": "named_choice_fiber_polynomial_v1",
                "query_count": len(actual),
                "schema": "zenodex.tau_experiment_receipt.v1",
                "spec_sha256": _sha256(SPEC),
                "tau_binary_sha256": actual_binary_sha,
                "tau_source_commit": commit,
                "tau_version": version,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
