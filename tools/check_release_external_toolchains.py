#!/usr/bin/env python3
"""Fail-fast preflight for release-gate external toolchain availability."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import shutil
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
RESULT_SCHEMA = "zenodex.release_external_toolchains_check.v1"


def _module_available(name: str) -> bool:
    return importlib.util.find_spec(name) is not None


def _esso_available(root: Path) -> tuple[bool, str]:
    vendored = root / "external" / "ESSO"
    if vendored.is_dir():
        sys.path.insert(0, str(vendored))
        try:
            from ESSO.verify import ltlf_synth  # type: ignore[import-not-found]

            if not hasattr(ltlf_synth, "synthesize_ltlf_multi_property"):
                return False, f"{vendored.relative_to(root)}:missing_ltlf_multi_property"
        except Exception as exc:
            return False, f"{vendored.relative_to(root)}:ltlf_api_error:{exc}"
        finally:
            try:
                sys.path.remove(str(vendored))
            except ValueError:
                pass
        return True, str(vendored.relative_to(root))
    if _module_available("ESSO"):
        try:
            from ESSO.verify import ltlf_synth  # type: ignore[import-not-found]

            if not hasattr(ltlf_synth, "synthesize_ltlf_multi_property"):
                return False, "importable:ESSO:missing_ltlf_multi_property"
        except Exception as exc:
            return False, f"importable:ESSO:ltlf_api_error:{exc}"
        spec = importlib.util.find_spec("ESSO")
        origin = getattr(spec, "origin", None)
        return True, str(origin or "importable:ESSO")
    return False, "missing"


def _tau_available(root: Path) -> tuple[bool, str]:
    env_tau = os.environ.get("TAU_BIN")
    if env_tau:
        path = Path(env_tau)
        if path.is_file() and os.access(path, os.X_OK):
            return True, str(path)
        return False, f"TAU_BIN_not_executable:{env_tau}"

    candidates = (
        root / "external" / "tau-nightly" / "usr" / "bin" / "tau",
        root / "external" / "tau-lang" / "build-Release" / "tau",
        root / "external" / "tau-lang" / "build-Debug" / "tau",
    )
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return True, str(candidate.relative_to(root))

    path_tau = shutil.which("tau")
    if path_tau:
        return True, path_tau

    return False, "missing"


def _tla_available(root: Path) -> tuple[bool, str]:
    env_tla = os.environ.get("TLA_JAR")
    if env_tla:
        path = Path(env_tla)
        if path.is_file():
            return True, str(path)
        return False, f"TLA_JAR_not_found:{env_tla}"

    candidate = root / "external" / "tla-tools" / "tla2tools.jar"
    if candidate.is_file():
        return True, str(candidate.relative_to(root))

    return False, "missing"


def _mathlib_available(root: Path) -> tuple[bool, str]:
    candidate = root / "external" / "mathlib4"
    if candidate.is_dir():
        return True, str(candidate.relative_to(root))
    return False, "missing"


def run_check(*, root: Path = ROOT) -> dict[str, Any]:
    errors: list[str] = []

    pytest_ok = _module_available("pytest")
    pip_audit_ok = _module_available("pip_audit")
    esso_ok, esso_source = _esso_available(root)
    tau_ok, tau_source = _tau_available(root)
    tla_ok, tla_source = _tla_available(root)
    mathlib_ok, mathlib_source = _mathlib_available(root)

    if not pytest_ok:
        errors.append("missing_module:pytest")
    if not pip_audit_ok:
        errors.append("missing_module:pip_audit")
    if not esso_ok:
        errors.append("missing_toolchain:ESSO")
    if not tau_ok:
        errors.append("missing_toolchain:Tau")
    if not tla_ok:
        errors.append("missing_toolchain:TLA")
    if not mathlib_ok:
        errors.append("missing_toolchain:mathlib4")

    return {
        "schema": RESULT_SCHEMA,
        "ok": not errors,
        "errors": errors,
        "root": str(root),
        "python": sys.executable,
        "python_modules": {
            "pytest": pytest_ok,
            "pip_audit": pip_audit_ok,
        },
        "external_toolchains": {
            "ESSO": {
                "available": esso_ok,
                "source": esso_source,
                "expected_vendored_path": "external/ESSO",
            },
            "Tau": {
                "available": tau_ok,
                "source": tau_source,
                "expected_vendored_path": "external/tau-lang/build-Release/tau",
            },
            "TLA": {
                "available": tla_ok,
                "source": tla_source,
                "expected_vendored_path": "external/tla-tools/tla2tools.jar",
            },
            "mathlib4": {
                "available": mathlib_ok,
                "source": mathlib_source,
                "expected_vendored_path": "external/mathlib4",
            }
        },
        "operator_hints": [
            "Install Python dev tooling with: PYTHON=<python> tools/install_python_hash_locked_deps.sh dev",
            "Provide the matching ESSO checkout at external/ESSO or use a Python environment where import ESSO exposes the LTLf multi-property API.",
            "Provide Tau by setting TAU_BIN=/path/to/tau or building external/tau-lang/build-Release/tau.",
            "Provide TLC/TLA tools by setting TLA_JAR=/path/to/tla2tools.jar or running tools/install_tla_tools.sh.",
            "Provide mathlib4 at external/mathlib4 because lean-mathlib/lakefile.lean requires that relative path.",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)

    result = run_check(root=args.root.resolve())
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
