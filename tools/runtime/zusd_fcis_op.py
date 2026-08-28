#!/usr/bin/env python3
"""Canonical one-line Python-authority bridge for the ZenoFCIS zUSD mount.

This module owns no transition semantics. It strictly admits one explicit
state and command, calls ``src.core.zusd._step_python``, and emits the existing
ZenoDEX authority document in one byte-canonical JSON-line representation.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.zusd import (  # noqa: E402
    ZUSDCommand,
    ZUSDState,
    ZUSD_STATE_FIELD_ORDER,
    _result_to_authority_doc,
    _step_python,
)

MAX_LINE_BYTES = 64 * 1024
TOP_FIELDS = ("version", "state", "tx", "require_oracle_authorization")
COMMAND_FIELDS: dict[str, tuple[str, ...]] = {
    "advance_epoch": ("kind", "delta"),
    "bootstrap_oracle": ("kind", "auth_ok", "price_e8"),
    "oracle_report": ("kind", "auth_ok", "price_e8"),
    "oracle_commit": ("kind", "auth_ok"),
    "deposit_collateral": ("kind", "amount_e8"),
    "withdraw_collateral": ("kind", "amount_e8"),
    "mint_zusd": ("kind", "amount_e8"),
    "repay_zusd": ("kind", "amount_e8"),
    "deposit_sp": ("kind", "amount_e8"),
    "withdraw_sp": ("kind", "amount_e8"),
    "redeem_zusd": ("kind", "amount_e8"),
    "liquidate": ("kind",),
}


class MountInputError(ValueError):
    """The shell transport was malformed or outside the mounted profile."""


def _object_no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise MountInputError(f"duplicate field: {key}")
        output[key] = value
    return output


def _require_exact_fields(value: dict[str, Any], expected: tuple[str, ...], label: str) -> None:
    if tuple(value) != expected:
        raise MountInputError(f"{label} fields must be exactly {expected!r}")

def _parse_state(value: Any) -> ZUSDState:
    if not isinstance(value, dict):
        raise MountInputError("state must be an object")
    _require_exact_fields(value, ZUSD_STATE_FIELD_ORDER, "state")
    kwargs: dict[str, Any] = {}
    for name in ZUSD_STATE_FIELD_ORDER:
        field = value[name]
        if name == "oracle_seen":
            if not isinstance(field, bool):
                raise MountInputError("state.oracle_seen must be a bool")
            kwargs[name] = field
        else:
            if not isinstance(field, int) or isinstance(field, bool) or field < 0:
                raise MountInputError(f"state.{name} must be a non-negative integer")
            kwargs[name] = field
    return ZUSDState(**kwargs)


def _parse_command(value: Any) -> ZUSDCommand:
    if not isinstance(value, dict):
        raise MountInputError("tx must be an object")
    kind = value.get("kind")
    if not isinstance(kind, str) or kind not in COMMAND_FIELDS:
        raise MountInputError("tx.kind is outside the mounted registry")
    _require_exact_fields(value, COMMAND_FIELDS[kind], "tx")
    args = {key: item for key, item in value.items() if key != "kind"}
    for key, item in args.items():
        if key == "auth_ok":
            if not isinstance(item, bool):
                raise MountInputError("tx.auth_ok must be a bool")
        elif not isinstance(item, int) or isinstance(item, bool) or item < 0:
            raise MountInputError(f"tx.{key} must be a non-negative integer")
    return ZUSDCommand(tag=kind, args=args)


def run_request(request: Any) -> dict[str, Any]:
    """Validate one request and invoke the exact Python zUSD authority."""
    if not isinstance(request, dict):
        raise MountInputError("request must be an object")
    _require_exact_fields(request, TOP_FIELDS, "request")
    if request["version"] != 1:
        raise MountInputError("unsupported request version")
    if request["require_oracle_authorization"] is not False:
        raise MountInputError("mounted Python profile requires explicit false Oracle policy")
    state = _parse_state(request["state"])
    command = _parse_command(request["tx"])
    return _result_to_authority_doc(state, command, _step_python(state, command))


def main() -> int:
    raw = sys.stdin.buffer.read(MAX_LINE_BYTES + 1)
    if not raw or len(raw) > MAX_LINE_BYTES:
        raise MountInputError("request exceeds its byte bound")
    if not raw.endswith(b"\n") or b"\n" in raw[:-1] or b"\r" in raw:
        raise MountInputError("request must be exactly one LF-terminated line")
    request = json.loads(raw[:-1], object_pairs_hook=_object_no_duplicates)
    canonical_request = json.dumps(request, separators=(",", ":")).encode("ascii") + b"\n"
    if canonical_request != raw:
        raise MountInputError("request is not byte-canonical")
    output = json.dumps(run_request(request), separators=(",", ":")).encode("ascii") + b"\n"
    if len(output) > MAX_LINE_BYTES:
        raise MountInputError("response exceeds its byte bound")
    sys.stdout.buffer.write(output)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (MountInputError, TypeError, ValueError, json.JSONDecodeError) as exc:
        print(f"zusd-fcis-op: {exc}", file=sys.stderr)
        raise SystemExit(2) from None
