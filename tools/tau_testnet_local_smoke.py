#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import math
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


def _ordered_random_asset_pair() -> Tuple[str, str]:
    """
    Return two distinct random asset ids in canonical lexical order.

    CREATE_POOL requires asset0 < asset1 in the DEX core.
    """
    while True:
        a0 = "0x" + os.urandom(32).hex()
        a1 = "0x" + os.urandom(32).hex()
        if a0 == a1:
            continue
        return (a0, a1) if a0 < a1 else (a1, a0)


def _must_load_json(text: str, *, name: str) -> Dict[str, Any]:
    try:
        obj = json.loads(text)
    except Exception as exc:
        raise RuntimeError(f"failed to parse {name} JSON: {exc}") from exc
    if not isinstance(obj, dict):
        raise RuntimeError(f"{name} must be a JSON object")
    return obj


def _try_load_json_object(text: str) -> Optional[Dict[str, Any]]:
    try:
        obj = json.loads(text)
    except Exception:
        return None
    if not isinstance(obj, dict):
        return None
    return obj


def _supports_app_bridge(client: TauNetTcpClient) -> bool:
    """
    Detect whether the connected Tau node exposes app-bridge RPCs.

    Upstream Tau Testnet at commit 2deccad supports custom operation inputs
    but does not expose getappstate/getstateproof.
    """
    resp = client.rpc("getappstate full").strip()
    obj = _try_load_json_object(resp)
    if obj is not None and "app_hash" in obj:
        return True
    return False


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
    if raw is None or not raw.strip():
        return bool(default)
    v = raw.strip().lower()
    if v in {"1", "true", "yes", "on"}:
        return True
    if v in {"0", "false", "no", "off"}:
        return False
    raise RuntimeError(
        f"{name} must be one of 1,true,yes,on,0,false,no,off; got {raw!r}"
    )


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
    except ValueError as exc:
        raise RuntimeError(f"{name} must be a float") from exc
    if not math.isfinite(value) or value <= 0:
        raise RuntimeError(f"{name} must be positive")
    return value


def _int_env(name: str, *, default: int, minimum: int, maximum: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not str(raw).strip():
        return int(default)
    try:
        value = int(str(raw).strip())
    except ValueError as exc:
        raise RuntimeError(f"{name} must be an integer") from exc
    if value < minimum:
        raise RuntimeError(f"{name} must be >= {minimum}")
    if value > maximum:
        raise RuntimeError(f"{name} must be <= {maximum}")
    return int(value)


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
        max_stdout_bytes=_int_env(
            "TAU_STATE_PROOF_MAX_STDOUT_BYTES",
            default=2_000_000,
            minimum=1,
            maximum=100_000_000,
        ),
        max_stderr_bytes=_int_env(
            "TAU_STATE_PROOF_MAX_STDERR_BYTES",
            default=16_000,
            minimum=1,
            maximum=10_000_000,
        ),
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
    # Fresh DBs can return app_hash + no materialized app_state yet.
    app_state = payload.get("app_state") if "app_state" in payload else {}
    if app_state is None:
        app_state = {}

    if not isinstance(app_hash, str):
        raise RuntimeError("invalid app_hash type from getappstate")
    if not isinstance(app_state, dict):
        raise RuntimeError("invalid app_state type from getappstate")
    return app_hash, app_state


def _find_pool_for_assets(app_state: Dict[str, Any], *, asset_a: str, asset_b: str) -> Dict[str, Any]:
    pools = app_state.get("pools")
    if not isinstance(pools, list):
        raise RuntimeError("app_state.pools missing or not a list")
    target = {asset_a, asset_b}
    for p in pools:
        if not isinstance(p, dict):
            continue
        p0 = p.get("asset0")
        p1 = p.get("asset1")
        if not isinstance(p0, str) or not isinstance(p1, str):
            continue
        if {p0, p1} == target:
            return p
    raise RuntimeError("pool for requested asset pair not found in app_state")


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


def _next_intent_nonce(app_state: Dict[str, Any], *, sender_pubkey: str) -> int:
    raw = app_state.get("nonces") or []
    if not isinstance(raw, list):
        raise RuntimeError("app_state.nonces must be a list")
    last_nonce = 0
    sender_norm = str(sender_pubkey).lower()
    if sender_norm.startswith("0x"):
        sender_norm = sender_norm[2:]

    for i, entry in enumerate(raw):
        if not isinstance(entry, dict):
            raise RuntimeError(f"app_state.nonces[{i}] must be an object")
        pk = entry.get("pubkey")
        if not isinstance(pk, str):
            continue
        pk_norm = pk.lower()
        if pk_norm.startswith("0x"):
            pk_norm = pk_norm[2:]
        if pk_norm != sender_norm:
            continue
        ln = entry.get("last_nonce", 0)
        if not isinstance(ln, int) or isinstance(ln, bool) or ln < 0:
            raise RuntimeError(f"app_state.nonces[{i}].last_nonce invalid")
        last_nonce = int(ln)
    return last_nonce + 1


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
    if isinstance(mine_first, str):
        lower = mine_first.lower()
        if "all transactions rejected" in lower or "mempool is empty" in lower:
            raise RuntimeError(f"createblock{print_suffix} did not include tx: {mine_first}")

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
    # createblock can legitimately take >5s on cold start (DHT/network bootstrap, Tau warmup).
    client = TauNetTcpClient(TauNetTcpConfig(host=params.host, port=params.port, timeout_s=30.0))
    sender_pubkey = bls_pubkey_hex_from_privkey(params.privkey_hex)
    # Use per-run assets so pool creation is not polluted by prior local runs.
    # Keep canonical order to satisfy CREATE_POOL kernel preconditions.
    asset0, asset1 = _ordered_random_asset_pair()
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
    app_hash_before, app_state_before = _get_app_state(ctx.client)
    create_nonce = _next_intent_nonce(app_state_before, sender_pubkey=ctx.sender_pubkey)

    intent: Dict[str, Any] = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": _rand_intent_id(),
        "sender_pubkey": ctx.sender_pubkey,
        "deadline": _now() + 3600,
        "nonce": create_nonce,
        "asset0": ctx.asset0,
        "asset1": ctx.asset1,
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
    }
    sig = sign_dex_intent_for_engine(intent, privkey=ctx.params.privkey_hex, chain_id=ctx.params.chain_id)
    ops: Dict[str, Any] = {
        # Upstream-safe app streams: 5=intents, 7=faucet-mint.
        # (2/3/4 are reserved in tau-testnet commit 2deccad)
        "21": {"mint": [[ctx.sender_pubkey, ctx.asset0, 10_000], [ctx.sender_pubkey, ctx.asset1, 10_000]]},
        "19": [[intent, sig]],
    }
    _send_and_mine(
        ctx.client,
        privkey_hex=ctx.params.privkey_hex,
        operations=ops,
        print_suffix="",
        proof_label="after create_pool",
        prev_app_hash=str(app_hash_before),
    )

    app_hash, app_state = _get_app_state(ctx.client)
    print(f"[smoke] app_hash={app_hash}")

    pool = _find_pool_for_assets(app_state, asset_a=ctx.asset0, asset_b=ctx.asset1)
    pool_id = str(pool.get("pool_id") or "")
    if not pool_id:
        raise RuntimeError("matched pool missing pool_id")
    print(f"[smoke] pool_id={pool_id}")
    print(
        f"[smoke] pool reserves after create: reserve0={pool.get('reserve0')} reserve1={pool.get('reserve1')} fee_bps={pool.get('fee_bps')}"
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

    app_hash_before, app_state_before = _get_app_state(ctx.client)
    swap_nonce = _next_intent_nonce(app_state_before, sender_pubkey=ctx.sender_pubkey)

    intent: Dict[str, Any] = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": _rand_intent_id(),
        "sender_pubkey": ctx.sender_pubkey,
        "deadline": _now() + 3600,
        "nonce": swap_nonce,
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
        operations={"19": [[intent, sig]]},
        print_suffix=" (swap)",
        proof_label="after swap",
        prev_app_hash=str(app_hash_before),
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


def _step_upstream_custom_input_probe(ctx: _SmokeCtx) -> None:
    """
    Upstream Tau Testnet probe (no app bridge):
    - submit a tx with custom operation stream >=5
    - mine a block
    - verify inclusion via getblocks
    """
    sequence_before = ctx.client.get_sequence(ctx.sender_pubkey)
    ops: Dict[str, Any] = {"19": ["dex_probe", "v1", 42]}
    send_resp = ctx.client.send_signed_tx(
        privkey=ctx.params.privkey_hex,
        operations=ops,
        expiration_seconds=3600,
        sequence_number=sequence_before,
    )
    print(f"[smoke] sendtx (upstream custom op) -> {send_resp}")
    if not send_resp.startswith("SUCCESS"):
        raise RuntimeError(f"custom-op transaction rejected: {send_resp}")

    mine_resp = ctx.client.createblock()
    mine_first = mine_resp.splitlines()[0] if mine_resp else mine_resp
    print(f"[smoke] createblock (upstream custom op) -> {mine_first!r}")

    blocks_resp = ctx.client.rpc("getblocks").strip()
    blocks_payload = _must_load_json(blocks_resp, name="getblocks")
    blocks = blocks_payload.get("blocks")
    if not isinstance(blocks, list) or not blocks:
        raise RuntimeError("getblocks returned no blocks")

    found = False
    for blk in reversed(blocks):
        if not isinstance(blk, dict):
            continue
        txs = blk.get("transactions")
        if not isinstance(txs, list):
            continue
        for tx in txs:
            if not isinstance(tx, dict):
                continue
            if tx.get("sender_pubkey") != ctx.sender_pubkey:
                continue
            if int(tx.get("sequence_number", -1)) != int(sequence_before):
                continue
            tx_ops = tx.get("operations")
            if isinstance(tx_ops, dict) and tx_ops.get("5") == ops["5"]:
                found = True
                break
        if found:
            break

    if not found:
        raise RuntimeError("custom-op tx not found in recent blocks")

    sequence_after = ctx.client.get_sequence(ctx.sender_pubkey)
    if sequence_after != sequence_before + 1:
        raise RuntimeError(
            f"sequence number did not advance after mined tx: before={sequence_before}, after={sequence_after}"
        )

    print("[smoke] upstream mode OK: custom operation input tx mined and indexed")


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

    if _supports_app_bridge(ctx.client):
        print("[smoke] detected app-bridge mode")
        ctx = _step_create_pool(ctx)
        _ = _step_swap(ctx)
        return

    print("[smoke] detected upstream mode (no getappstate); running custom-input probe")
    _step_upstream_custom_input_probe(ctx)


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
