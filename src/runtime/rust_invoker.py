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


def fee_route(
    *,
    accumulator: dict[str, Any],
    tx: dict[str, Any],
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Rust protocol fee router for one transition from an explicit accumulator."""

    out = invoke(
        "fee-route",
        {
            "version": 1,
            "accumulator": accumulator,
            "tx": tx,
        },
        timeout_seconds=timeout_seconds,
    )
    if not isinstance(out, dict):
        raise RustInvocationError("fee-route: output must be an object")
    if out.get("version") != 1 or out.get("kernel") != "fee_router":
        raise RustInvocationError("fee-route: unsupported output header")
    if not isinstance(out.get("accept"), bool):
        raise RustInvocationError("fee-route: accept must be a bool")
    for key in ("pre_state_root", "post_state_root"):
        if not isinstance(out.get(key), str):
            raise RustInvocationError(f"fee-route: {key} must be a string")
    _validate_fee_accumulator_doc(out.get("post_accumulator"))
    if out["accept"]:
        receipt = out.get("receipt")
        if not isinstance(out.get("receipt_hash"), str) or not isinstance(receipt, dict):
            raise RustInvocationError("fee-route: accepted output missing receipt")
        for key in ("source", "asset", "amount", "buyburn", "stakers", "reserve", "hosts", "dust"):
            if not isinstance(receipt.get(key), str):
                raise RustInvocationError(f"fee-route: receipt.{key} must be a string")
    else:
        if not isinstance(out.get("reject_reason"), str):
            raise RustInvocationError("fee-route: rejected output missing reason")
        if out.get("receipt") is not None or out.get("receipt_hash") is not None:
            raise RustInvocationError("fee-route: rejected output must not carry receipt")
    return out


def _validate_fee_accumulator_doc(value: Any) -> None:
    if not isinstance(value, dict):
        raise RustInvocationError("fee-route: post_accumulator must be an object")
    for key in ("dust_by_stream", "cum_buyburn", "cum_stakers", "cum_reserve", "cum_hosts"):
        if not isinstance(value.get(key), list):
            raise RustInvocationError(f"fee-route: post_accumulator.{key} must be a list")
    for entry in value["dust_by_stream"]:
        if not isinstance(entry, dict):
            raise RustInvocationError("fee-route: dust entry must be an object")
        if (
            not isinstance(entry.get("source"), str)
            or not isinstance(entry.get("asset"), str)
            or not isinstance(entry.get("amount"), str)
        ):
            raise RustInvocationError("fee-route: malformed dust entry")
    for bucket in ("cum_buyburn", "cum_stakers", "cum_reserve", "cum_hosts"):
        for entry in value[bucket]:
            if not isinstance(entry, dict):
                raise RustInvocationError(f"fee-route: {bucket} entry must be an object")
            if not isinstance(entry.get("asset"), str) or not isinstance(entry.get("amount"), str):
                raise RustInvocationError(f"fee-route: malformed {bucket} entry")


def burn_rails_verify(
    *,
    tx: dict[str, Any],
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Rust burn accounting rails for one stateless rail tuple."""

    out = invoke(
        "verify-burn-trace",
        {
            "version": 1,
            "kernel": "burn_receipts",
            "steps": [{"tx": tx}],
        },
        timeout_seconds=timeout_seconds,
    )
    if not isinstance(out, dict):
        raise RustInvocationError("verify-burn-trace: output must be an object")
    if out.get("version") != 1 or out.get("kernel") != "burn_receipts":
        raise RustInvocationError("verify-burn-trace: unsupported output header")
    if not isinstance(out.get("initial_state_root"), str) or not isinstance(
        out.get("final_state_root"), str
    ):
        raise RustInvocationError("verify-burn-trace: malformed state roots")
    results = out.get("results")
    if not isinstance(results, list) or len(results) != 1:
        raise RustInvocationError("verify-burn-trace: expected exactly one result")
    result = results[0]
    if not isinstance(result, dict):
        raise RustInvocationError("verify-burn-trace: result must be an object")
    if result.get("index") != 0 or not isinstance(result.get("accept"), bool):
        raise RustInvocationError("verify-burn-trace: malformed result header")
    for key in ("pre_state_root", "post_state_root"):
        if not isinstance(result.get(key), str):
            raise RustInvocationError(f"verify-burn-trace: {key} must be a string")
    if result["accept"]:
        if not isinstance(result.get("receipt_hash"), str):
            raise RustInvocationError("verify-burn-trace: accepted result missing receipt hash")
        if result.get("reject_reason") is not None:
            raise RustInvocationError("verify-burn-trace: accepted result carried reject reason")
    else:
        if not isinstance(result.get("reject_reason"), str):
            raise RustInvocationError("verify-burn-trace: rejected result missing reason")
        if result.get("receipt_hash") is not None:
            raise RustInvocationError("verify-burn-trace: rejected result carried receipt hash")
    return {
        "version": 1,
        "kernel": "burn_receipts",
        "accept": bool(result["accept"]),
        "reject_reason": None if result["accept"] else str(result["reject_reason"]),
        "receipt_hash": result.get("receipt_hash"),
        "pre_state_root": str(result["pre_state_root"]),
        "post_state_root": str(result["post_state_root"]),
    }


def cpmm_op(
    *,
    pool: dict[str, Any],
    tx: dict[str, Any],
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Rust CPMM per-pool settlement for one init/swap transition."""

    out = invoke(
        "cpmm-op",
        {
            "version": 1,
            "pool": pool,
            "tx": tx,
        },
        timeout_seconds=timeout_seconds,
    )
    if not isinstance(out, dict):
        raise RustInvocationError("cpmm-op: output must be an object")
    if out.get("version") != 1 or out.get("kernel") != "cpmm_settlement":
        raise RustInvocationError("cpmm-op: unsupported output header")
    if not isinstance(out.get("accept"), bool):
        raise RustInvocationError("cpmm-op: accept must be a bool")
    for key in ("pre_state_root", "post_state_root"):
        if not isinstance(out.get(key), str):
            raise RustInvocationError(f"cpmm-op: {key} must be a string")
    _validate_cpmm_pool_doc(out.get("post_pool"))
    if out["accept"]:
        receipt = out.get("receipt")
        if not isinstance(out.get("receipt_hash"), str) or not isinstance(receipt, dict):
            raise RustInvocationError("cpmm-op: accepted output missing receipt")
        if not isinstance(receipt.get("kind"), str) or not isinstance(receipt.get("zero_for_one"), bool):
            raise RustInvocationError("cpmm-op: malformed receipt header")
        for key in (
            "amount_in",
            "amount_out",
            "fee_total",
            "amount_out_quote",
            "overdelivery_gap",
            "gap_bps",
            "new_reserve0",
            "new_reserve1",
        ):
            if not isinstance(receipt.get(key), str):
                raise RustInvocationError(f"cpmm-op: receipt.{key} must be a string")
        if out.get("reject_reason") is not None:
            raise RustInvocationError("cpmm-op: accepted output carried reject reason")
    else:
        if not isinstance(out.get("reject_reason"), str):
            raise RustInvocationError("cpmm-op: rejected output missing reason")
        if out.get("receipt") is not None or out.get("receipt_hash") is not None:
            raise RustInvocationError("cpmm-op: rejected output carried receipt")
    return out


def _validate_cpmm_pool_doc(value: Any) -> None:
    if not isinstance(value, dict):
        raise RustInvocationError("cpmm-op: post_pool must be an object")
    if not isinstance(value.get("initialized"), bool):
        raise RustInvocationError("cpmm-op: post_pool.initialized must be a bool")
    for key in ("reserve0", "reserve1", "fee_bps"):
        if not isinstance(value.get(key), str):
            raise RustInvocationError(f"cpmm-op: post_pool.{key} must be a string")


def perp_math_eval(
    case: dict[str, Any],
    *,
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Rust stateless perps math for one pure arithmetic case."""

    out = invoke("perp-math", {"cases": [case]}, timeout_seconds=timeout_seconds)
    if not isinstance(out, dict) or out.get("version") != 1:
        raise RustInvocationError("perp-math: unsupported output header")
    results = out.get("results")
    if not isinstance(results, list) or len(results) != 1:
        raise RustInvocationError("perp-math: unexpected results shape")
    result = results[0]
    if not isinstance(result, dict):
        raise RustInvocationError("perp-math: result must be an object")
    allowed = {"index", "ok", "value", "flag", "code"}
    extra = set(result) - allowed
    if extra:
        raise RustInvocationError(f"perp-math: unexpected result fields {sorted(extra)!r}")
    if result.get("index") != 0:
        raise RustInvocationError("perp-math: result index mismatch")
    if not isinstance(result.get("ok"), bool):
        raise RustInvocationError("perp-math: ok must be a bool")
    if result["ok"]:
        has_value = "value" in result
        has_flag = "flag" in result
        if has_value == has_flag:
            raise RustInvocationError("perp-math: accepted result must carry exactly one value or flag")
        if has_value and not isinstance(result["value"], str):
            raise RustInvocationError("perp-math: accepted value must be a string")
        if has_flag and not isinstance(result["flag"], bool):
            raise RustInvocationError("perp-math: accepted flag must be a bool")
        if "code" in result:
            raise RustInvocationError("perp-math: accepted result carried reject code")
    else:
        if not isinstance(result.get("code"), str):
            raise RustInvocationError("perp-math: rejected result missing code")
        if "value" in result or "flag" in result:
            raise RustInvocationError("perp-math: rejected result carried success payload")
    return result


_PERP_STATEFUL_SUBCOMMANDS = frozenset(
    {
        "advance-epoch",
        "funding-auto",
        "publish-clearing-price",
        "settle-epoch",
        "partial-liquidate",
        "account-op",
        "set-market-params",
    }
)


def perp_stateful_case(
    subcommand: str,
    case: dict[str, Any],
    *,
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Rust stateful isolated-perps checker for one accepted transition case."""

    if subcommand not in _PERP_STATEFUL_SUBCOMMANDS:
        raise RustInvocationError(f"perp-stateful: unsupported subcommand {subcommand!r}")
    out = invoke(
        subcommand,
        {"cases": [case]},
        timeout_seconds=timeout_seconds,
    )
    if not isinstance(out, dict) or out.get("version") != 1:
        raise RustInvocationError(f"{subcommand}: unexpected output header")
    results = out.get("results")
    if not isinstance(results, list) or len(results) != 1:
        raise RustInvocationError(f"{subcommand}: unexpected results shape")
    result = results[0]
    if not isinstance(result, dict) or result.get("index") != 0:
        raise RustInvocationError(f"{subcommand}: malformed result")
    if not isinstance(result.get("ok"), bool):
        raise RustInvocationError(f"{subcommand}: result.ok must be a bool")
    if result["ok"]:
        if "code" in result:
            raise RustInvocationError(f"{subcommand}: accepted result carried code")
    else:
        if not isinstance(result.get("code"), str):
            raise RustInvocationError(f"{subcommand}: rejected result missing code")
    return result


def zusd_op(
    *,
    state: dict[str, Any],
    tx: dict[str, Any],
    timeout_seconds: float = _DEFAULT_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Rust zUSD single-vault transition from an explicit state."""

    out = invoke(
        "zusd-op",
        {"version": 1, "state": state, "tx": tx},
        timeout_seconds=timeout_seconds,
    )
    if not isinstance(out, dict):
        raise RustInvocationError("zusd-op: output must be an object")
    if out.get("version") != 1 or out.get("kernel") != "zusd":
        raise RustInvocationError("zusd-op: unsupported output header")
    if not isinstance(out.get("accept"), bool):
        raise RustInvocationError("zusd-op: accept must be a bool")
    for key in ("pre_state_root", "post_state_root"):
        if not isinstance(out.get(key), str):
            raise RustInvocationError(f"zusd-op: {key} must be a string")
    _validate_zusd_state_doc(out.get("post_state"))
    if out["accept"]:
        receipt = out.get("receipt")
        if not isinstance(out.get("receipt_hash"), str) or not isinstance(receipt, dict):
            raise RustInvocationError("zusd-op: accepted output missing receipt")
        if not isinstance(receipt.get("tag"), str):
            raise RustInvocationError("zusd-op: malformed receipt")
        if out.get("reject_reason") is not None:
            raise RustInvocationError("zusd-op: accepted output carried reject reason")
    else:
        if not isinstance(out.get("reject_reason"), str):
            raise RustInvocationError("zusd-op: rejected output missing reason")
        if out.get("receipt") is not None or out.get("receipt_hash") is not None:
            raise RustInvocationError("zusd-op: rejected output carried receipt")
    return out


def _validate_zusd_state_doc(value: Any) -> None:
    if not isinstance(value, dict):
        raise RustInvocationError("zusd-op: post_state must be an object")
    if not isinstance(value.get("oracle_seen"), bool):
        raise RustInvocationError("zusd-op: post_state.oracle_seen must be a bool")
    for key in (
        "now_epoch",
        "oracle_last_update_epoch",
        "price_e8",
        "price_pending_e8",
        "max_oracle_staleness_epochs",
        "collateral_e8",
        "debt_e8",
        "free_debt_e8",
        "sp_debt_e8",
        "sp_coll_e8",
        "protocol_collateral_e8",
        "protocol_revenue_zusd_cum_e8",
        "liquidator_compensation_collateral_cum_e8",
        "mcr_bps",
        "ccr_bps",
        "min_debt_open_e8",
        "max_debt_e8",
        "max_debt_supply_e8",
        "max_sp_coll_e8",
        "max_protocol_coll_e8",
        "base_rate_bps",
        "base_rate_last_epoch",
        "base_rate_decay_per_epoch_bps",
        "base_rate_borrow_bump_bps",
        "base_rate_redeem_bump_bps",
        "borrow_fee_floor_bps",
        "borrow_fee_max_bps",
        "redemption_fee_floor_bps",
        "redemption_fee_max_bps",
        "liquidation_gas_comp_fixed_collateral_e8",
        "liquidation_gas_comp_bps",
    ):
        if not isinstance(value.get(key), str):
            raise RustInvocationError(f"zusd-op: post_state.{key} must be a string")
