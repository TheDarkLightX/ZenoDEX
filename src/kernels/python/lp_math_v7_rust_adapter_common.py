"""Shared Rust CLI bridge for LP math v7 ESSO shell adapters."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
from functools import lru_cache
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[3]
RUST_MANIFEST = ROOT / "src/kernels/rust/lp_math_v7/Cargo.toml"


def _binary_suffix() -> str:
    return ".exe" if os.name == "nt" else ""


@lru_cache(maxsize=1)
def rust_lp_math_cli() -> Path:
    override = os.environ.get("ZENODEX_LP_MATH_V7_CLI")
    if override:
        path = Path(override)
        if not path.exists():
            raise FileNotFoundError(f"ZENODEX_LP_MATH_V7_CLI does not exist: {path}")
        return path

    target_dir = Path(tempfile.gettempdir()) / "zenodex_lp_math_v7_rust_target"
    subprocess.check_call(
        [
            "cargo",
            "build",
            "--quiet",
            "--manifest-path",
            str(RUST_MANIFEST),
            "--bin",
            "lp_math_v7_cli",
            "--target-dir",
            str(target_dir),
        ],
        cwd=ROOT,
    )
    binary = target_dir / "debug" / f"lp_math_v7_cli{_binary_suffix()}"
    if not binary.exists():
        raise FileNotFoundError(f"lp_math_v7_cli build did not produce {binary}")
    return binary


def run_rust_lp_math(*args: object) -> dict[str, Any]:
    proc = subprocess.run(
        [str(rust_lp_math_cli()), *(str(arg) for arg in args)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"lp_math_v7_cli emitted invalid JSON: {proc.stdout!r}") from exc
    if not isinstance(payload, dict):
        raise RuntimeError(f"lp_math_v7_cli emitted non-object JSON: {payload!r}")
    return payload


def is_rust_ok(payload: dict[str, Any]) -> bool:
    return bool(payload.get("ok") is True and isinstance(payload.get("result"), dict))
