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


def state_root_hash(
    state: dict[str, Any],
    *,
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> str:
    """Rust ``compute_state_root`` for one normalized state-root v5 state."""

    out = invoke(
        "verify-state-root",
        {"cases": [state]},
        timeout_seconds=timeout_seconds,
    )
    results = out.get("results") if isinstance(out, dict) else None
    if not isinstance(results, list) or len(results) != 1:
        raise RustInvocationError("verify-state-root: unexpected results shape")
    result = results[0]
    if not isinstance(result, dict) or not result.get("ok") or "state_root" not in result:
        code = result.get("code") if isinstance(result, dict) else "malformed"
        raise RustInvocationError(f"verify-state-root rejected: {code}")
    return str(result["state_root"])


def replay_guard_admit(
    *,
    state_entries: list[dict[str, Any]],
    sender: Any,
    nonce: Any,
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Rust replay/idempotency guard for one transition from an explicit state."""

    out = invoke(
        "replay-guard-admit",
        {
            "version": 1,
            "state_entries": state_entries,
            "tx": {"kind": "admit", "sender": sender, "nonce": nonce},
        },
        timeout_seconds=timeout_seconds,
    )
    if not isinstance(out, dict):
        raise RustInvocationError("replay-guard-admit: output must be an object")
    if out.get("version") != 1 or out.get("kernel") != "replay_guard":
        raise RustInvocationError("replay-guard-admit: unsupported output header")
    if not isinstance(out.get("accept"), bool):
        raise RustInvocationError("replay-guard-admit: accept must be a bool")
    for key in ("pre_state_root", "post_state_root"):
        if not isinstance(out.get(key), str):
            raise RustInvocationError(f"replay-guard-admit: {key} must be a string")
    if not isinstance(out.get("post_state_entries"), list):
        raise RustInvocationError("replay-guard-admit: post_state_entries must be a list")
    for entry in out["post_state_entries"]:
        if not isinstance(entry, dict):
            raise RustInvocationError("replay-guard-admit: state entry must be an object")
        if not isinstance(entry.get("sender"), str) or not isinstance(entry.get("last_nonce"), int):
            raise RustInvocationError("replay-guard-admit: malformed state entry")
    if out["accept"]:
        receipt = out.get("receipt")
        if not isinstance(out.get("receipt_hash"), str) or not isinstance(receipt, dict):
            raise RustInvocationError("replay-guard-admit: accepted output missing receipt")
        if (
            not isinstance(receipt.get("sender"), str)
            or not isinstance(receipt.get("nonce"), int)
            or not isinstance(receipt.get("prev_nonce"), int)
        ):
            raise RustInvocationError("replay-guard-admit: malformed receipt")
    else:
        if not isinstance(out.get("reject_reason"), str):
            raise RustInvocationError("replay-guard-admit: rejected output missing reason")
    return out


def balance_op(
    *,
    state_entries: list[dict[str, Any]],
    tx: dict[str, Any],
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Rust balance accounting for one credit/transfer from an explicit state."""

    out = invoke(
        "balance-op",
        {
            "version": 1,
            "state_entries": state_entries,
            "tx": tx,
        },
        timeout_seconds=timeout_seconds,
    )
    if not isinstance(out, dict):
        raise RustInvocationError("balance-op: output must be an object")
    if out.get("version") != 1 or out.get("kernel") != "balances":
        raise RustInvocationError("balance-op: unsupported output header")
    if not isinstance(out.get("accept"), bool):
        raise RustInvocationError("balance-op: accept must be a bool")
    for key in ("pre_state_root", "post_state_root"):
        if not isinstance(out.get(key), str):
            raise RustInvocationError(f"balance-op: {key} must be a string")
    if not isinstance(out.get("post_state_entries"), list):
        raise RustInvocationError("balance-op: post_state_entries must be a list")
    for entry in out["post_state_entries"]:
        if not isinstance(entry, dict):
            raise RustInvocationError("balance-op: state entry must be an object")
        if (
            not isinstance(entry.get("pubkey"), str)
            or not isinstance(entry.get("asset"), str)
            or not isinstance(entry.get("amount"), str)
        ):
            raise RustInvocationError("balance-op: malformed state entry")
    if out["accept"]:
        receipt = out.get("receipt")
        if not isinstance(out.get("receipt_hash"), str) or not isinstance(receipt, dict):
            raise RustInvocationError("balance-op: accepted output missing receipt")
        if (
            not isinstance(receipt.get("kind"), str)
            or not (receipt.get("sender") is None or isinstance(receipt.get("sender"), str))
            or not isinstance(receipt.get("recipient"), str)
            or not isinstance(receipt.get("asset"), str)
            or not isinstance(receipt.get("amount"), str)
        ):
            raise RustInvocationError("balance-op: malformed receipt")
    else:
        if not isinstance(out.get("reject_reason"), str):
            raise RustInvocationError("balance-op: rejected output missing reason")
    return out
