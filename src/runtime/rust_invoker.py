"""Production Rust-engine invocation through the ``zenodex-runtime`` CLI.

This is the live counterpart to the test-only ``tools/runtime`` shadow
harnesses. It locates the packaged Rust runtime binary, sends one JSON request
to a subcommand, and fails closed on missing binaries in Rust-authoritative
modes through :func:`src.runtime.authority.decide`.
"""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import Any

from .authority import RustUnavailable

_REPO = Path(__file__).resolve().parents[2]
_RUST_RUNTIME_DIR = _REPO / "rust-runtime"
_DEFAULT_TIMEOUT_SECONDS = 5.0


class RustInvocationError(RuntimeError):
    """The Rust engine errored, timed out, or returned malformed output."""


def locate_runtime_binary() -> Path:
    env_bin = os.environ.get("ZENODEX_RUNTIME_BIN")
    if env_bin:
        path = Path(env_bin)
        if not path.is_file():
            raise RustUnavailable(f"ZENODEX_RUNTIME_BIN points at a missing file: {path}")
        return path
    for profile in ("release", "debug"):
        candidate = _RUST_RUNTIME_DIR / "target" / profile / "zenodex-runtime"
        if candidate.is_file():
            return candidate
    raise RustUnavailable("zenodex-runtime binary not found; set ZENODEX_RUNTIME_BIN or build rust-runtime")


def invoke(subcommand: str, request: dict[str, Any], *, timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS) -> Any:
    """Run ``zenodex-runtime <subcommand> -`` with a JSON request on stdin."""

    bin_path = locate_runtime_binary()
    try:
        proc = subprocess.run(
            [str(bin_path), subcommand, "-"],
            input=json.dumps(request),
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as exc:
        raise RustInvocationError(f"rust {subcommand} timed out after {timeout_seconds}s") from exc
    if proc.returncode != 0:
        stderr = proc.stderr.strip()[:200]
        raise RustInvocationError(f"rust {subcommand} exited {proc.returncode}: {stderr}")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RustInvocationError(f"rust {subcommand} produced malformed output") from exc


def canonical_domain_json_hash(
    label: str,
    value: Any,
    *,
    version: int = 1,
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> str:
    """Rust ``sha256(domain_sep(label, version) + canonical_json_bytes(value))``."""

    out = invoke(
        "canonical-hash",
        {
            "cases": [
                {
                    "op": "domain_json_hash",
                    "label": label,
                    "version": int(version),
                    "value": value,
                }
            ]
        },
        timeout_seconds=timeout_seconds,
    )
    results = out.get("results") if isinstance(out, dict) else None
    if not isinstance(results, list) or len(results) != 1:
        raise RustInvocationError("canonical-hash: unexpected results shape")
    result = results[0]
    if not isinstance(result, dict) or not result.get("ok") or "hash" not in result:
        code = result.get("code") if isinstance(result, dict) else "malformed"
        raise RustInvocationError(f"canonical-hash domain_json_hash rejected: {code}")
    return str(result["hash"])
