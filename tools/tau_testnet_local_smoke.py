#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import os
import shlex
import sqlite3
import subprocess
import sys
import time
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.tau_net_client import (
    TauNetTcpClient,
    TauNetTcpConfig,
    bls_pubkey_hex_from_privkey,
    sign_dex_intent_for_engine,
)


DEFAULT_PRIVKEY_HEX = "11cebd90117355080b392cb7ef2fbdeff1150a124d29058ae48b19bebecd4f09"


BalanceKey = Tuple[str, str]
BalanceMap = Dict[BalanceKey, int]


def _now() -> int:
    return int(time.time())


def _hex32(prefix_byte: int) -> str:
    if not (0 <= prefix_byte <= 255):
        raise ValueError("prefix_byte out of range")
    return "0x" + f"{prefix_byte:02x}" * 32


def _rand_intent_id() -> str:
    return "0x" + os.urandom(32).hex()


def _must_load_json(text: str, *, name: str) -> Dict[str, Any]:
    try:
        obj = json.loads(text)
    except Exception as exc:
        raise RuntimeError(f"failed to parse {name} JSON: {exc}") from exc
    if not isinstance(obj, dict):
        raise RuntimeError(f"{name} must be a JSON object")
    return obj


def _find_pool(state: Dict[str, Any], *, pool_id: str) -> Dict[str, Any]:
    pools = state.get("pools")
    if not isinstance(pools, list):
        raise RuntimeError("app_state.pools missing or not a list")
    for p in pools:
        if isinstance(p, dict) and p.get("pool_id") == pool_id:
            return p
    raise RuntimeError(f"pool not found in app_state: {pool_id}")


def _bool_env(name: str, *, default: bool) -> bool:
    raw = os.environ.get(name)
    if raw is None:
        return bool(default)
    v = raw.strip().lower()
    if v in {"1", "true", "yes", "on"}:
        return True
    if v in {"0", "false", "no", "off"}:
        return False
    return bool(default)


def _require_env(name: str, *, hint: str) -> str:
    raw = os.environ.get(name, "").strip()
    if not raw:
        raise RuntimeError(f"{name} is required ({hint})")
    return raw


def _float_env(name: str, *, default: float) -> float:
    raw = os.environ.get(name)
    if raw is None or not str(raw).strip():
        return float(default)
    try:
        value = float(str(raw).strip())
    except Exception as exc:
        raise RuntimeError(f"{name} must be a float") from exc
    if value <= 0:
        raise RuntimeError(f"{name} must be positive")
    return value


def _parse_cmd(cmd: str) -> list[str]:
    try:
        parts = shlex.split(cmd)
    except Exception as exc:
        raise RuntimeError("TAU_STATE_PROOF_VERIFY_CMD must be a valid shell-like command string") from exc
    if not parts:
        raise RuntimeError("TAU_STATE_PROOF_VERIFY_CMD must be non-empty")
    return parts


def _enforce_cmd_path_policy(cmd: list[str]) -> None:
    allow_path = _bool_env("TAU_STATE_PROOF_ALLOW_PATH_LOOKUP", default=False)
    if allow_path:
        return
    exe = cmd[0]
    if not os.path.isabs(exe):
        raise RuntimeError(
            "TAU_STATE_PROOF_VERIFY_CMD must use an absolute executable path "
            "(set TAU_STATE_PROOF_ALLOW_PATH_LOOKUP=1 to allow PATH lookup)"
        )
    if not (os.path.isfile(exe) and os.access(exe, os.X_OK)):
        raise RuntimeError(f"verifier command not executable: {exe}")


@dataclass(frozen=True)
class _VerifierSubprocessConfig:
    timeout_s: float
    max_stdout_bytes: int
    max_stderr_bytes: int


def _verifier_subprocess_config() -> _VerifierSubprocessConfig:
    return _VerifierSubprocessConfig(
        timeout_s=_float_env("TAU_STATE_PROOF_SUBPROCESS_TIMEOUT_S", default=10.0),
        max_stdout_bytes=int(os.environ.get("TAU_STATE_PROOF_MAX_STDOUT_BYTES", "2000000")),
        max_stderr_bytes=int(os.environ.get("TAU_STATE_PROOF_MAX_STDERR_BYTES", "16000")),
    )


def _read_local_state_proof_inputs_from_db(db_path: str) -> Tuple[str, str, str]:
    with sqlite3.connect(db_path) as conn:
        cur = conn.cursor()

        cur.execute("SELECT value FROM chain_state WHERE key='state_proof'")
        row = cur.fetchone()
        proof_json = str(row[0] or "") if row else ""

        cur.execute("SELECT value FROM chain_state WHERE key='app_hash'")
        row2 = cur.fetchone()
        app_hash = str(row2[0] or "") if row2 else ""

        cur.execute("SELECT block_data FROM blocks ORDER BY block_number DESC LIMIT 1")
        row3 = cur.fetchone()
        block_data = str(row3[0] or "") if row3 else ""

    if not proof_json.strip():
        raise RuntimeError("state_proof missing in DB (chain_state['state_proof'])")
    if not app_hash.strip():
        raise RuntimeError("app_hash missing in DB (chain_state['app_hash'])")
    if not block_data.strip():
        raise RuntimeError("block_data missing in DB (blocks table)")
    return proof_json, app_hash, block_data


def _run_verifier_cmd(*, cmd: list[str], payload: Dict[str, Any]) -> Dict[str, Any]:
    _enforce_cmd_path_policy(cmd)
    cfg = _verifier_subprocess_config()
    proc = subprocess.run(
        cmd,
        input=json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8"),
        capture_output=True,
        timeout=cfg.timeout_s,
        check=False,
    )
    if proc.returncode != 0:
        err = proc.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"verifier subprocess failed (exit {proc.returncode}): {err or 'no stderr'}")
    if len(proc.stdout or b"") > cfg.max_stdout_bytes:
        raise RuntimeError("verifier subprocess stdout too large")
    if len(proc.stderr or b"") > cfg.max_stderr_bytes:
        raise RuntimeError("verifier subprocess stderr too large")
    out = proc.stdout.decode("utf-8", errors="replace").strip()
    return _must_load_json(out, name="verifier output")


def _verify_state_proof_from_db(*, state_hash: str, prev_app_hash: str) -> None:
    db_path = _require_env("TAU_DB_PATH", hint="local proof verification reads state_proof and latest block from the node DB")
    verify_cmd = _require_env("TAU_STATE_PROOF_VERIFY_CMD", hint="local proof verification runs an external verifier")
    cmd = _parse_cmd(verify_cmd)

    proof_json, app_hash, block_data = _read_local_state_proof_inputs_from_db(db_path)
    proof_obj = _must_load_json(proof_json, name="state_proof")
    block_obj = json.loads(block_data)
    if not isinstance(block_obj, dict):
        raise RuntimeError("block_data must be a JSON object")

    payload: Dict[str, Any] = {
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": state_hash,
        "proof": proof_obj,
        "block": block_obj,
        "tau_state": {"app_hash": app_hash},
        "context": {
            "app_hash_pre": prev_app_hash,
            "block_timestamp": int(block_obj.get("header", {}).get("timestamp", 0)),
        },
    }
    resp = _run_verifier_cmd(cmd=cmd, payload=payload)
    if not resp.get("ok"):
        raise RuntimeError(f"verifier rejected: {resp.get('error') or 'invalid'}")


def _check_state_proof(client: TauNetTcpClient, *, label: str, prev_app_hash: str) -> None:
    resp = client.getstateproof(full=True)
    meta = _must_load_json(resp, name="getstateproof")
    if not meta.get("present"):
        raise RuntimeError(f"missing state proof ({label})")
    state_hash = meta.get("state_hash")
    if not isinstance(state_hash, str) or len(state_hash) != 64:
        raise RuntimeError(f"invalid state_hash in getstateproof ({label})")
    print(
        f"[smoke] state_proof ({label}): present=1 state_hash={state_hash} proof_type={meta.get('proof_type')} proof_bytes={meta.get('proof_bytes')}"
    )

    if _bool_env("TAU_STATE_PROOF_VERIFY_LOCAL", default=False):
        _verify_state_proof_from_db(state_hash=state_hash, prev_app_hash=prev_app_hash)
        print(f"[smoke] state_proof ({label}): local verify -> ok")


@dataclass(frozen=True)
class _SmokeParams:
    host: str
    port: int
    privkey_hex: str
    chain_id: str


@dataclass(frozen=True)
class _SmokeCtx:
    params: _SmokeParams
    client: TauNetTcpClient
    sender_pubkey: str
    asset0: str
    asset1: str
    app_hash: str = ""
    pool_id: str = ""
    balances_before: Optional[BalanceMap] = None
    before_in: int = 0
    before_out: int = 0


def _get_app_state(client: TauNetTcpClient) -> Tuple[str, Dict[str, Any]]:
    app_resp = client.getappstate(full=True)
    payload = _must_load_json(app_resp, name="getappstate")
    app_hash = payload.get("app_hash") or ""
    app_state = payload.get("app_state")

    if not isinstance(app_hash, str) or not app_hash:
        raise RuntimeError("missing app_hash (is TAU_APP_BRIDGE_MODULE enabled?)")
    if not isinstance(app_state, dict):
        raise RuntimeError("missing app_state object (bridge enabled but no state?)")
    return app_hash, app_state


def _extract_first_pool_id(app_state: Dict[str, Any]) -> str:
    pools = app_state.get("pools")
    if not isinstance(pools, list) or not pools:
        raise RuntimeError("expected at least one pool in app_state.pools")
    pool0 = pools[0]
    if not isinstance(pool0, dict):
        raise RuntimeError("pool entry must be an object")
    pool_id = pool0.get("pool_id")
    if not isinstance(pool_id, str) or not pool_id:
        raise RuntimeError("pool entry missing pool_id")
    return pool_id


def _balances_from_app_state(app_state: Dict[str, Any]) -> BalanceMap:
    raw = app_state.get("balances") or []
    if not isinstance(raw, list):
        raise RuntimeError("app_state.balances must be a list")
    out: BalanceMap = {}
    for i, entry in enumerate(raw):
        if not isinstance(entry, dict):
            raise RuntimeError(f"app_state.balances[{i}] must be an object")
        pk = entry.get("pubkey")
        asset = entry.get("asset")
        amount = entry.get("amount")
        if not isinstance(pk, str) or not pk:
            raise RuntimeError(f"app_state.balances[{i}].pubkey invalid")
        if not isinstance(asset, str) or not asset:
            raise RuntimeError(f"app_state.balances[{i}].asset invalid")
        if not isinstance(amount, int) or isinstance(amount, bool):
            raise RuntimeError(f"app_state.balances[{i}].amount must be an int")
        out[(pk, asset)] = int(amount)
    return out


def _send_and_mine(
    client: TauNetTcpClient,
    *,
    privkey_hex: str,
    operations: Dict[str, Any],
    print_suffix: str,
    proof_label: str,
    prev_app_hash: str,
) -> None:
    send_resp = client.send_signed_tx(privkey=privkey_hex, operations=operations, expiration_seconds=3600)
    print(f"[smoke] sendtx{print_suffix} -> {send_resp}")

    mine_resp = client.createblock()
    mine_first = mine_resp.splitlines()[0] if mine_resp else mine_resp
    print(f"[smoke] createblock{print_suffix} -> {mine_first!r}")

    if _bool_env("TAU_EXPECT_STATE_PROOF", default=False):
        _check_state_proof(client, label=proof_label, prev_app_hash=prev_app_hash)


def _assert_swap_changed_balances(
    *,
    before: BalanceMap,
    after: BalanceMap,
    sender_pubkey: str,
    asset_in: str,
    asset_out: str,
) -> Tuple[int, int, int, int]:
    before_in = before.get((sender_pubkey, asset_in), 0)
    before_out = before.get((sender_pubkey, asset_out), 0)
    after_in = after.get((sender_pubkey, asset_in), 0)
    after_out = after.get((sender_pubkey, asset_out), 0)

    if not (after_in < before_in):
        raise RuntimeError("swap did not decrease asset_in balance")
    if not (after_out > before_out):
        raise RuntimeError("swap did not increase asset_out balance")
    return before_in, before_out, after_in, after_out


def _init_smoke_ctx(params: _SmokeParams) -> _SmokeCtx:
    client = TauNetTcpClient(TauNetTcpConfig(host=params.host, port=params.port, timeout_s=5.0))
    sender_pubkey = bls_pubkey_hex_from_privkey(params.privkey_hex)
    asset0 = _hex32(0x11)
    asset1 = _hex32(0x22)
    return _SmokeCtx(
        params=params,
        client=client,
        sender_pubkey=sender_pubkey,
        asset0=asset0,
        asset1=asset1,
    )


def _step_hello(ctx: _SmokeCtx) -> _SmokeCtx:
    hello = ctx.client.rpc("hello version=1").strip()
    print(f"[smoke] hello -> {hello}")
    print(f"[smoke] sender_pubkey={ctx.sender_pubkey}")
    return ctx


def _step_create_pool(ctx: _SmokeCtx) -> _SmokeCtx:
    intent: Dict[str, Any] = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": _rand_intent_id(),
        "sender_pubkey": ctx.sender_pubkey,
        "deadline": _now() + 3600,
        "asset0": ctx.asset0,
        "asset1": ctx.asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }
    sig = sign_dex_intent_for_engine(intent, privkey=ctx.params.privkey_hex, chain_id=ctx.params.chain_id)
    ops: Dict[str, Any] = {
        # Test-only: mint assets inside DEX state for local dev.
        "4": {"mint": [[ctx.sender_pubkey, ctx.asset0, 10_000], [ctx.sender_pubkey, ctx.asset1, 10_000]]},
        "2": [[intent, sig]],
    }
    _send_and_mine(
        ctx.client,
        privkey_hex=ctx.params.privkey_hex,
        operations=ops,
        print_suffix="",
        proof_label="after create_pool",
        prev_app_hash="",
    )

    app_hash, app_state = _get_app_state(ctx.client)
    print(f"[smoke] app_hash={app_hash}")

    pool_id = _extract_first_pool_id(app_state)
    print(f"[smoke] pool_id={pool_id}")
    pool0 = _find_pool(app_state, pool_id=pool_id)
    print(
        f"[smoke] pool reserves after create: reserve0={pool0.get('reserve0')} reserve1={pool0.get('reserve1')} fee_bps={pool0.get('fee_bps')}"
    )

    balances_before = _balances_from_app_state(app_state)
    before_in = balances_before.get((ctx.sender_pubkey, ctx.asset0), 0)
    before_out = balances_before.get((ctx.sender_pubkey, ctx.asset1), 0)
    print(f"[smoke] balances before swap: in={before_in} out={before_out}")

    return replace(ctx, app_hash=app_hash, pool_id=pool_id, balances_before=balances_before, before_in=before_in, before_out=before_out)


def _step_swap(ctx: _SmokeCtx) -> _SmokeCtx:
    if not ctx.pool_id:
        raise RuntimeError("internal error: missing pool_id")
    if ctx.balances_before is None:
        raise RuntimeError("internal error: missing balances_before")

    intent: Dict[str, Any] = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": _rand_intent_id(),
        "sender_pubkey": ctx.sender_pubkey,
        "deadline": _now() + 3600,
        "pool_id": ctx.pool_id,
        "asset_in": ctx.asset0,
        "asset_out": ctx.asset1,
        "amount_in": 100,
        "min_amount_out": 1,
        "recipient": ctx.sender_pubkey,
    }
    sig = sign_dex_intent_for_engine(intent, privkey=ctx.params.privkey_hex, chain_id=ctx.params.chain_id)
    _send_and_mine(
        ctx.client,
        privkey_hex=ctx.params.privkey_hex,
        operations={"2": [[intent, sig]]},
        print_suffix=" (swap)",
        proof_label="after swap",
        prev_app_hash=str(ctx.app_hash),
    )

    _app_hash2, app_state2 = _get_app_state(ctx.client)
    balances_after = _balances_from_app_state(app_state2)
    before_in, before_out, after_in, after_out = _assert_swap_changed_balances(
        before=ctx.balances_before,
        after=balances_after,
        sender_pubkey=ctx.sender_pubkey,
        asset_in=ctx.asset0,
        asset_out=ctx.asset1,
    )

    pool_after = _find_pool(app_state2, pool_id=ctx.pool_id)
    print(f"[smoke] pool reserves after swap: reserve0={pool_after.get('reserve0')} reserve1={pool_after.get('reserve1')}")
    print(f"[smoke] balances after swap:  in={after_in} out={after_out}")
    print(f"[smoke] balance deltas:       d_in={after_in - before_in} d_out={after_out - before_out}")
    print("[smoke] OK: pool created and swap executed")
    return replace(ctx, before_in=before_in, before_out=before_out)


def run_smoke(
    *,
    host: str,
    port: int,
    privkey_hex: str,
    chain_id: str,
) -> None:
    params = _SmokeParams(host=host, port=port, privkey_hex=privkey_hex, chain_id=chain_id)
    ctx = _init_smoke_ctx(params)
    ctx = _step_hello(ctx)
    ctx = _step_create_pool(ctx)
    _ = _step_swap(ctx)


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Tau Testnet local-node smoke test (DEX app bridge)")
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=65432)
    parser.add_argument("--privkey", default=DEFAULT_PRIVKEY_HEX, help="32-byte hex (no 0x) or 0x-prefixed")
    parser.add_argument("--chain-id", default="tau-local")
    args = parser.parse_args(argv)

    try:
        run_smoke(host=args.host, port=args.port, privkey_hex=args.privkey, chain_id=args.chain_id)
    except Exception as exc:
        print(f"[smoke] FAIL: {exc}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
