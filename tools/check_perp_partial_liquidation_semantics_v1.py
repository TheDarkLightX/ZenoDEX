#!/usr/bin/env python3
"""Fail-closed Python, Julia, and Lean semantics parity checker."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


from tools.build_perp_partial_liquidation_semantics_v1 import (  # noqa: E402
    DEFAULT_CORPUS,
    DEFAULT_MANIFEST,
    SCHEMA,
    expected_artifacts,
)

JULIA_REPLAY = ROOT / "tools" / "perp_partial_liquidation_semantics_v1.jl"
LEAN_FILES = (
    "Proofs/PerpPartialLiquidationExact.lean",
    "Proofs/PerpMarginRoundingSafety.lean",
)


def _read_bytes(path: Path, label: str, errors: list[str]) -> bytes | None:
    if not path.is_file():
        errors.append(f"{label} is missing: {path}")
        return None
    try:
        return path.read_bytes()
    except OSError as exc:
        errors.append(f"could not read {label}: {exc}")
        return None


def _run_julia(
    *,
    corpus_path: Path,
    corpus_sha256: str,
    julia_executable: str | None,
) -> tuple[dict[str, Any], list[str]]:
    errors: list[str] = []
    julia = julia_executable or shutil.which("julia")
    if not julia:
        return {"ok": False, "status": "missing"}, ["Julia executable is missing"]
    if not JULIA_REPLAY.is_file():
        return {"ok": False, "status": "missing"}, ["Julia replay source is missing"]
    try:
        proc = subprocess.run(
            [julia, str(JULIA_REPLAY), str(corpus_path), corpus_sha256],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=180,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {"ok": False, "status": "error"}, [f"Julia replay failed to run: {exc}"]
    stdout_lines = [line for line in proc.stdout.splitlines() if line.strip()]
    payload: dict[str, Any] = {"ok": False, "status": "invalid_output"}
    if stdout_lines:
        try:
            candidate = json.loads(stdout_lines[-1])
            if isinstance(candidate, dict):
                payload = candidate
        except json.JSONDecodeError as exc:
            errors.append(f"Julia replay emitted invalid JSON: {exc}")
    else:
        errors.append("Julia replay emitted no JSON report")
    if proc.returncode != 0:
        errors.append(f"Julia replay exited with status {proc.returncode}")
    if proc.stderr.strip():
        errors.append(f"Julia replay stderr: {proc.stderr.strip()}")
    if payload.get("schema") != SCHEMA:
        errors.append("Julia replay schema mismatch")
    if payload.get("corpus_sha256") != corpus_sha256:
        errors.append("Julia replay corpus hash mismatch")
    if payload.get("ok") is not True:
        errors.append("Julia replay reported failure")
    payload = dict(payload)
    payload["status"] = "passed" if not errors else "failed"
    return payload, errors


def _run_lean(*, lake_executable: str | None) -> tuple[dict[str, Any], list[str]]:
    lake = lake_executable or shutil.which("lake")
    if not lake:
        return {"ok": False, "status": "missing"}, ["Lean lake executable is missing"]
    errors: list[str] = []
    for lean_file in LEAN_FILES:
        try:
            proc = subprocess.run(
                [lake, "env", "lean", lean_file],
                cwd=ROOT / "lean-mathlib",
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=180,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            errors.append(f"Lean check failed to run for {lean_file}: {exc}")
            continue
        if proc.returncode != 0:
            errors.append(f"Lean check for {lean_file} exited with status {proc.returncode}")
        if proc.stdout.strip():
            errors.append(f"Lean check stdout for {lean_file} was nonempty: {proc.stdout.strip()}")
        if proc.stderr.strip():
            errors.append(f"Lean check stderr for {lean_file} was nonempty: {proc.stderr.strip()}")
    return {
        "files": [f"lean-mathlib/{lean_file}" for lean_file in LEAN_FILES],
        "ok": not errors,
        "status": "passed" if not errors else "failed",
    }, errors


def check_semantics_v1(
    *,
    corpus_path: Path = DEFAULT_CORPUS,
    manifest_path: Path = DEFAULT_MANIFEST,
    require_julia: bool = True,
    require_lean: bool = True,
    julia_executable: str | None = None,
    lake_executable: str | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    expected_corpus, expected_manifest = expected_artifacts()
    actual_corpus = _read_bytes(corpus_path, "corpus", errors)
    actual_manifest = _read_bytes(manifest_path, "manifest", errors)

    manifest_payload: dict[str, Any] = {}
    if actual_manifest is not None:
        try:
            parsed = json.loads(actual_manifest)
            if isinstance(parsed, dict):
                manifest_payload = parsed
            else:
                errors.append("manifest root must be an object")
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            errors.append(f"manifest is not valid UTF-8 JSON: {exc}")

    if actual_corpus is not None and actual_corpus != expected_corpus:
        errors.append("corpus differs from live Python runtime regeneration")
    if actual_manifest is not None and actual_manifest != expected_manifest:
        errors.append("manifest differs from source-pinned regeneration")
    if manifest_payload.get("schema") != SCHEMA:
        errors.append("manifest schema mismatch")

    corpus_meta = manifest_payload.get("corpus")
    corpus_sha256 = ""
    case_count = 0
    if isinstance(corpus_meta, dict):
        corpus_sha256 = str(corpus_meta.get("sha256", ""))
        try:
            case_count = int(corpus_meta.get("case_count", 0))
        except (TypeError, ValueError):
            errors.append("manifest corpus case_count must be an integer")
    else:
        errors.append("manifest corpus metadata is missing")

    backends: dict[str, Any] = {
        "python_runtime": {
            "ok": actual_corpus == expected_corpus,
            "status": "passed" if actual_corpus == expected_corpus else "failed",
        }
    }
    if require_julia and not errors:
        julia_report, julia_errors = _run_julia(
            corpus_path=corpus_path,
            corpus_sha256=corpus_sha256,
            julia_executable=julia_executable,
        )
        backends["julia"] = julia_report
        errors.extend(julia_errors)
    else:
        backends["julia"] = {"ok": False, "status": "not_run"}
    if require_lean and not errors:
        lean_report, lean_errors = _run_lean(lake_executable=lake_executable)
        backends["lean"] = lean_report
        errors.extend(lean_errors)
    else:
        backends["lean"] = {"ok": False, "status": "not_run"}

    full_scope = require_julia and require_lean
    return {
        "schema": SCHEMA,
        "ok": not errors,
        "claim_scope": (
            "python_julia_lean_source_pinned_parity"
            if full_scope
            else "artifact_and_python_runtime_only"
        ),
        "case_count": case_count,
        "corpus_sha256": corpus_sha256,
        "backends": backends,
        "errors": errors,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check source-pinned Python, Julia, and Lean partial-liquidation semantics."
    )
    parser.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--julia", help="Explicit Julia executable path")
    parser.add_argument("--lake", help="Explicit Lean lake executable path")
    parser.add_argument(
        "--artifacts-only",
        action="store_true",
        help="Check generated artifacts against Python only; report reduced claim scope.",
    )
    args = parser.parse_args()

    report = check_semantics_v1(
        corpus_path=args.corpus,
        manifest_path=args.manifest,
        require_julia=not args.artifacts_only,
        require_lean=not args.artifacts_only,
        julia_executable=args.julia,
        lake_executable=args.lake,
    )
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
