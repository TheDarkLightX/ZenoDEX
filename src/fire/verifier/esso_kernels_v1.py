from __future__ import annotations

import json
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

from src.fire.pathing_v1 import default_fire_esso_kernel_model_paths


FIRE_ESSO_KERNEL_CHECK_REPORT_SCHEMA = "zenodex/fire-esso-kernel-check-report/v1"


@dataclass(frozen=True)
class FireEssoKernelCheckResult:
    model_path: Path
    validate_payload: dict[str, object]
    verify_payload: dict[str, object]
    validate_artifact_path: Path | None = None
    verify_artifact_path: Path | None = None

    def to_dict(self) -> dict[str, object]:
        report = self.verify_payload.get("report")
        report_dict = report if isinstance(report, dict) else {}
        payload = {
            "model_path": str(self.model_path.resolve()),
            "ir_hash": self.validate_payload.get("ir_hash"),
            "validate_ok": self.validate_payload.get("ok") is True,
            "verify_ok": self.verify_payload.get("ok") is True,
            "determinism": self.verify_payload.get("determinism"),
            "determinism_trials": self.verify_payload.get("determinism_trials"),
            "solvers": self.verify_payload.get("solvers"),
            "verdict": report_dict.get("verdict"),
            "total_queries": report_dict.get("total_queries"),
            "failed_queries": report_dict.get("failed_queries"),
            "inconclusive_queries": report_dict.get("inconclusive_queries"),
            "solvers_agreed": report_dict.get("solvers_agreed"),
            "notes": report_dict.get("notes"),
        }
        if self.validate_artifact_path is not None:
            payload["validate_artifact_path"] = str(self.validate_artifact_path.resolve())
        if self.verify_artifact_path is not None:
            payload["verify_artifact_path"] = str(self.verify_artifact_path.resolve())
        return payload


def _run_json(cmd: Sequence[str], *, cwd: Path) -> tuple[bool, dict[str, object] | None, str | None]:
    proc = subprocess.run(
        list(cmd),
        cwd=str(cwd),
        capture_output=True,
        text=True,
        check=False,
    )
    raw = proc.stdout if proc.returncode == 0 else proc.stderr
    try:
        payload = json.loads(raw) if raw else None
    except json.JSONDecodeError:
        payload = None
    if proc.returncode != 0:
        return False, payload, raw.strip() or f"command_failed:{' '.join(cmd)}"
    if not isinstance(payload, dict):
        return False, None, f"command_output_not_json_object:{' '.join(cmd)}"
    return True, payload, None


def _run_text(cmd: Sequence[str], *, cwd: Path) -> tuple[bool, str | None]:
    proc = subprocess.run(
        list(cmd),
        cwd=str(cwd),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        return False, (proc.stderr or proc.stdout or "").strip() or f"command_failed:{' '.join(cmd)}"
    return True, (proc.stdout or proc.stderr or "").strip()


def _solver_versions(solvers: str, *, cwd: Path) -> tuple[bool, dict[str, str], list[str]]:
    versions: dict[str, str] = {}
    errors: list[str] = []
    for solver in [item.strip() for item in solvers.split(",") if item.strip()]:
        if shutil.which(solver) is None:
            errors.append(f"missing_solver:{solver}")
            continue
        ok, output = _run_text([solver, "--version"], cwd=cwd)
        if not ok or output is None:
            errors.append(f"solver_version_failed:{solver}")
            continue
        versions[solver] = output.splitlines()[0]
    return not errors, versions, errors


def _esso_module_info(*, python_executable: str, cwd: Path) -> tuple[bool, str | None]:
    ok, output = _run_text(
        [
            python_executable,
            "-c",
            "import ESSO; print(ESSO.__file__)",
        ],
        cwd=cwd,
    )
    return ok, output


def default_fire_esso_kernel_models() -> tuple[Path, ...]:
    return default_fire_esso_kernel_model_paths()


def verify_fire_esso_kernels(
    *,
    model_paths: Sequence[str | Path] | None = None,
    solvers: str = "z3,cvc5",
    determinism_trials: int = 2,
    timeout_ms: int = 5000,
    python_executable: str = sys.executable,
    repo_root: Path | None = None,
    output_dir: Path | None = None,
) -> tuple[bool, str | None, dict[str, object]]:
    root = repo_root or Path(__file__).resolve().parents[3]
    models = tuple(Path(path) for path in (model_paths or default_fire_esso_kernel_models()))
    if not models:
        return False, "no_fire_esso_models_configured", {
            "schema": FIRE_ESSO_KERNEL_CHECK_REPORT_SCHEMA,
            "ok": False,
            "case_count": 0,
            "cases": [],
        }

    solvers_ok, solver_versions, solver_errors = _solver_versions(solvers, cwd=root)
    esso_ok, esso_module_path = _esso_module_info(python_executable=python_executable, cwd=root)
    if not solvers_ok or not esso_ok:
        payload = {
            "schema": FIRE_ESSO_KERNEL_CHECK_REPORT_SCHEMA,
            "ok": False,
            "case_count": 0,
            "solvers": solvers.split(","),
            "determinism_trials": determinism_trials,
            "timeout_ms": timeout_ms,
            "python_executable": python_executable,
            "esso_module_path": esso_module_path,
            "solver_versions": solver_versions,
            "cases": [],
        }
        if solver_errors:
            payload["solver_errors"] = solver_errors
        if not esso_ok:
            payload["esso_error"] = esso_module_path or "esso_module_import_failed"
        return False, "fire_esso_toolchain_unavailable", payload

    cases: list[dict[str, object]] = []
    all_ok = True
    for model_path in models:
        validate_artifact_path = None
        verify_artifact_path = None
        validate_ok, validate_payload, validate_err = _run_json(
            [python_executable, "-m", "ESSO", "validate", str(model_path)],
            cwd=root,
        )
        if output_dir is not None and validate_payload is not None:
            model_out = output_dir / model_path.stem
            model_out.mkdir(parents=True, exist_ok=True)
            validate_artifact_path = model_out / "validate.json"
            validate_artifact_path.write_text(json.dumps(validate_payload, indent=2, sort_keys=True), encoding="utf-8")
        if not validate_ok or validate_payload is None or validate_payload.get("ok") is not True:
            all_ok = False
            cases.append(
                {
                    "model_path": str(model_path.resolve()),
                    "ok": False,
                    "stage": "validate",
                    "error": validate_err or "esso_validate_failed",
                    "validate_payload": validate_payload,
                }
            )
            continue

        verify_ok, verify_payload, verify_err = _run_json(
            [
                python_executable,
                "-m",
                "ESSO",
                "verify-multi",
                str(model_path),
                "--solvers",
                solvers,
                "--determinism-trials",
                str(determinism_trials),
                "--timeout-ms",
                str(timeout_ms),
            ],
            cwd=root,
        )
        report = verify_payload.get("report") if isinstance(verify_payload, dict) else None
        report_dict = report if isinstance(report, dict) else {}
        if output_dir is not None and verify_payload is not None:
            model_out = output_dir / model_path.stem
            model_out.mkdir(parents=True, exist_ok=True)
            verify_artifact_path = model_out / "verify_multi.json"
            verify_artifact_path.write_text(json.dumps(verify_payload, indent=2, sort_keys=True), encoding="utf-8")
        verdict = report_dict.get("verdict")
        inconclusive_queries = report_dict.get("inconclusive_queries")
        solvers_agreed = report_dict.get("solvers_agreed")
        deterministic = verify_payload.get("determinism") if isinstance(verify_payload, dict) else None
        if (
            not verify_ok
            or verify_payload is None
            or verify_payload.get("ok") is not True
            or verdict != "VERIFIED"
            or inconclusive_queries != 0
            or solvers_agreed is not True
            or deterministic is not True
        ):
            all_ok = False
            cases.append(
                {
                    "model_path": str(model_path.resolve()),
                    "ok": False,
                    "stage": "verify-multi",
                    "error": verify_err or "esso_verify_multi_failed",
                    "validate_payload": validate_payload,
                    "verify_payload": verify_payload,
                }
            )
            continue

        cases.append(
            {
                "ok": True,
                **FireEssoKernelCheckResult(
                    model_path=model_path,
                    validate_payload=validate_payload,
                    verify_payload=verify_payload,
                    validate_artifact_path=validate_artifact_path,
                    verify_artifact_path=verify_artifact_path,
                ).to_dict(),
            }
        )

    payload = {
        "schema": FIRE_ESSO_KERNEL_CHECK_REPORT_SCHEMA,
        "ok": all_ok,
        "case_count": len(cases),
        "solvers": solvers.split(","),
        "determinism_trials": determinism_trials,
        "timeout_ms": timeout_ms,
        "python_executable": python_executable,
        "esso_module_path": esso_module_path,
        "solver_versions": solver_versions,
        "cases": cases,
    }
    return all_ok, None if all_ok else "fire_esso_kernel_check_failed", payload


__all__ = [
    "FIRE_ESSO_KERNEL_CHECK_REPORT_SCHEMA",
    "FireEssoKernelCheckResult",
    "default_fire_esso_kernel_models",
    "verify_fire_esso_kernels",
]
