#!/usr/bin/env python3
"""Run deterministic synthetic market agents against live ZenoLedger nodes.

The swarm is intentionally replayable. It submits real testnet HTTP writes to
the node API, records receipts, and emits JSONL rows that can seed WES/energy
models without letting any model decide ledger validity.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import sys
import time
from http import HTTPStatus
from pathlib import Path
from typing import Any, Mapping
from urllib.error import HTTPError
from urllib.parse import urljoin, urlparse
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.zeno_ledger_make_testnet_bundle import DEFAULT_ASSET0, DEFAULT_ASSET1  # noqa: E402


REPORT_SCHEMA = "zenodex.zeno_ledger.market_swarm_report.v0"
ROW_SCHEMA = "zenodex.zeno_ledger.market_swarm_telemetry_row.v0"
DEFAULT_TOKEN_ENV = "ZENO_LEDGER_WRITER_TOKEN"
DEFAULT_TOKEN = "local-multidocker-token"
MAX_HTTP_JSON_BYTES = 2 * 1024 * 1024


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--writer-url", default="http://127.0.0.1:8787")
    parser.add_argument("--forwarder-url", default="http://127.0.0.1:8788")
    parser.add_argument("--readonly-url", default="http://127.0.0.1:8789")
    parser.add_argument("--token", default=os.environ.get(DEFAULT_TOKEN_ENV, DEFAULT_TOKEN))
    parser.add_argument("--seed", default="zenodex-market-swarm-v0")
    parser.add_argument("--run-id")
    parser.add_argument("--agents", type=int, default=8)
    parser.add_argument("--steps", type=int, default=64)
    parser.add_argument("--initial-faucet", type=int, default=1_000_000)
    parser.add_argument("--out-dir", type=Path, default=Path("runs/market_swarm/latest"))
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--telemetry-jsonl", type=Path)
    parser.add_argument("--no-forwarder", action="store_true")
    parser.add_argument("--no-readonly-probes", action="store_true")
    args = parser.parse_args()

    forwarder_url = None if args.no_forwarder else _optional_url(args.forwarder_url)
    readonly_url = None if args.no_readonly_probes else _optional_url(args.readonly_url)
    run_id = args.run_id or f"market-swarm-{_short_hash(args.seed)}-{int(time.time())}"
    report = run_market_swarm_v0(
        writer_url=_require_base_url(args.writer_url, name="writer_url"),
        forwarder_url=forwarder_url,
        readonly_url=readonly_url,
        token=str(args.token),
        seed=str(args.seed),
        run_id=run_id,
        agent_count=max(1, int(args.agents)),
        steps=max(1, int(args.steps)),
        initial_faucet=max(1, int(args.initial_faucet)),
    )

    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    output_json = args.output_json or out_dir / "report.json"
    telemetry_jsonl = args.telemetry_jsonl or out_dir / "telemetry.jsonl"
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    with telemetry_jsonl.open("w", encoding="utf-8") as out:
        for row in report["telemetry_rows"]:
            out.write(json.dumps(row, sort_keys=True) + "\n")
    print(json.dumps({**report, "telemetry_rows": f"{len(report['telemetry_rows'])} rows"}, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def run_market_swarm_v0(
    *,
    writer_url: str,
    forwarder_url: str | None,
    readonly_url: str | None,
    token: str,
    seed: str,
    run_id: str,
    agent_count: int,
    steps: int,
    initial_faucet: int,
) -> dict[str, Any]:
    rng = random.Random(seed)
    agents = [_agent(seed, index) for index in range(agent_count)]
    rows: list[dict[str, Any]] = []
    target_urls = [writer_url] + ([forwarder_url] if forwarder_url else [])

    for agent in agents:
        for asset in (DEFAULT_ASSET0, DEFAULT_ASSET1):
            target_url = target_urls[(agent["index"] + (0 if asset == DEFAULT_ASSET0 else 1)) % len(target_urls)]
            row = _submit_faucet(
                run_id=run_id,
                seed=seed,
                step=-1,
                agent=agent,
                target_url=target_url,
                token=token,
                asset=asset,
                amount=initial_faucet,
                expected_valid=True,
                action_family="bootstrap_faucet",
            )
            rows.append(row)

    strategies = ("momentum", "mean_reversion", "noise", "whale", "liquidity", "high_min_out_probe")
    for step in range(steps):
        snapshot = _latest_snapshot(writer_url)
        pool = _choose_pool(snapshot)
        if pool is None:
            rows.append(_local_error_row(run_id=run_id, seed=seed, step=step, error="no_active_pool"))
            break
        agent = agents[step % len(agents)]
        strategy = strategies[step % len(strategies)]
        target_url = target_urls[step % len(target_urls)]

        if readonly_url and step % 17 == 0:
            rows.append(
                _submit_faucet(
                    run_id=run_id,
                    seed=seed,
                    step=step,
                    agent=agent,
                    target_url=readonly_url,
                    token=token,
                    asset=DEFAULT_ASSET0,
                    amount=1,
                    expected_valid=False,
                    action_family="readonly_rejection_probe",
                )
            )
            continue
        if step % 19 == 0:
            rows.append(
                _submit_tx(
                    run_id=run_id,
                    seed=seed,
                    step=step,
                    agent=agent,
                    target_url=target_url,
                    token=token,
                    tx={"tx_id": f"{run_id}-malformed-{step}", "operations": "bad"},
                    expected_valid=False,
                    action_family="malformed_tx_probe",
                    context={"pool": pool},
                )
            )
            continue

        if strategy == "liquidity":
            row = _liquidity_action(
                run_id=run_id,
                seed=seed,
                step=step,
                agent=agent,
                target_url=target_url,
                token=token,
                snapshot=snapshot,
                pool=pool,
                rng=rng,
            )
        else:
            row = _swap_action(
                run_id=run_id,
                seed=seed,
                step=step,
                agent=agent,
                target_url=target_url,
                token=token,
                snapshot=snapshot,
                pool=pool,
                strategy=strategy,
                rng=rng,
            )
        rows.append(row)

    node_trade_telemetry: dict[str, Any] | None = None
    try:
        node_trade_telemetry = _get_json(_join(writer_url, "telemetry/summary?limit=10000"))
    except Exception:
        node_trade_telemetry = None
    summary = _summarize_rows(rows)
    invalid_accept_count = sum(1 for row in rows if row.get("expected_valid") is False and row.get("accepted") is True)
    ok = invalid_accept_count == 0 and summary["submission_count"] > 0 and summary["accepted_count"] > 0
    return {
        "schema": REPORT_SCHEMA,
        "ok": ok,
        "run_id": run_id,
        "seed": seed,
        "writer_url": writer_url,
        "forwarder_url": forwarder_url,
        "readonly_url": readonly_url,
        "agent_count": len(agents),
        "requested_steps": steps,
        "summary": summary,
        "invalid_accept_count": invalid_accept_count,
        "node_trade_telemetry_summary": node_trade_telemetry,
        "safety": {
            "uses_testnet_faucet": True,
            "synthetic_agents_only": True,
            "deterministic_seeded_plan": True,
            "receipts_are_authoritative": True,
            "models_do_not_authorize_settlement": True,
        },
        "telemetry_rows": rows,
    }


def _require_base_url(value: str, *, name: str) -> str:
    parsed = urlparse(value)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc or parsed.query or parsed.fragment:
        raise ValueError(f"{name} must be an http(s) base URL without query or fragment")
    if parsed.username or parsed.password:
        raise ValueError(f"{name} must not contain embedded credentials")
    return value.rstrip("/")


def _optional_url(value: str | None) -> str | None:
    if value is None or value.strip() == "":
        return None
    return _require_base_url(value.strip(), name="url")


def _join(base_url: str, path: str) -> str:
    return urljoin(_require_base_url(base_url, name="base_url") + "/", path.lstrip("/"))


def _read_response(response: Any, *, url: str) -> dict[str, Any]:
    payload = response.read(MAX_HTTP_JSON_BYTES + 1)
    if len(payload) > MAX_HTTP_JSON_BYTES:
        raise ValueError(f"response too large from {url}")
    obj = json.loads(payload.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{url} returned non-object JSON")
    return obj


def _get_json(url: str) -> dict[str, Any]:
    with urlopen(url, timeout=30.0) as response:  # noqa: S310 - local/operator supplied testnet URL
        return _read_response(response, url=url)


def _post_json(url: str, body: Mapping[str, Any], *, token: str | None) -> tuple[int, dict[str, Any]]:
    payload = json.dumps(body, sort_keys=True).encode("utf-8")
    if len(payload) > MAX_HTTP_JSON_BYTES:
        raise ValueError("request body too large")
    headers = {"Content-Type": "application/json"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    request = Request(url, data=payload, headers=headers, method="POST")
    try:
        with urlopen(request, timeout=30.0) as response:  # noqa: S310 - local/operator supplied testnet URL
            return int(response.status), _read_response(response, url=url)
    except HTTPError as exc:
        payload = exc.read(MAX_HTTP_JSON_BYTES + 1)
        if len(payload) > MAX_HTTP_JSON_BYTES:
            raise ValueError(f"error response too large from {url}") from exc
        try:
            obj = json.loads(payload.decode("utf-8"))
        except Exception:
            obj = {"ok": False, "error": payload.decode("utf-8", errors="replace")}
        if not isinstance(obj, dict):
            obj = {"ok": False, "error": str(obj)}
        return int(exc.code), obj


def _latest_snapshot(writer_url: str) -> dict[str, Any]:
    live = _get_json(_join(writer_url, "live"))
    state = live.get("state")
    if not isinstance(state, Mapping):
        raise ValueError("writer live state missing")
    height = int(state["latest_height"])
    snapshot = _get_json(_join(writer_url, f"live/snapshot/{height}"))
    snapshot["_height"] = height
    return snapshot


def _choose_pool(snapshot: Mapping[str, Any]) -> Mapping[str, Any] | None:
    pools = snapshot.get("pools")
    if not isinstance(pools, list):
        return None
    for pool in pools:
        if isinstance(pool, Mapping) and pool.get("status") == "ACTIVE":
            return pool
    return None


def _agent(seed: str, index: int) -> dict[str, Any]:
    material = (
        hashlib.sha256(f"{seed}:agent:{index}:0".encode("utf-8")).hexdigest()
        + hashlib.sha256(f"{seed}:agent:{index}:1".encode("utf-8")).hexdigest()
    )
    return {
        "index": index,
        "agent_id": f"agent-{index:03d}",
        "pubkey": "0x" + material[:96],
    }


def _short_hash(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()[:12]


def _object_hash(value: object) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return "0x" + hashlib.sha256(payload).hexdigest()


def _nonce(snapshot: Mapping[str, Any], pubkey: str) -> int:
    nonces = snapshot.get("nonces")
    if isinstance(nonces, list):
        for row in nonces:
            if isinstance(row, Mapping) and row.get("pubkey") == pubkey:
                return int(row.get("last_nonce", 0))
    return 0


def _balance(snapshot: Mapping[str, Any], pubkey: str, asset: str) -> int:
    balances = snapshot.get("balances")
    if isinstance(balances, list):
        for row in balances:
            if isinstance(row, Mapping) and row.get("pubkey") == pubkey and row.get("asset") == asset:
                return int(row.get("amount", 0))
    return 0


def _lp_balance(snapshot: Mapping[str, Any], pubkey: str, pool_id: str) -> int:
    balances = snapshot.get("lp_balances")
    if isinstance(balances, list):
        for row in balances:
            if isinstance(row, Mapping) and row.get("pubkey") == pubkey and row.get("pool_id") == pool_id:
                return int(row.get("amount", 0))
    return 0


def _quote_exact_in(pool: Mapping[str, Any], asset_in: str, amount_in: int) -> int:
    reserve_in = int(pool["reserve0"]) if asset_in == pool["asset0"] else int(pool["reserve1"])
    reserve_out = int(pool["reserve1"]) if asset_in == pool["asset0"] else int(pool["reserve0"])
    fee_bps = int(pool.get("fee_bps", 30))
    amount_after_fee = amount_in * (10_000 - fee_bps) // 10_000
    if amount_after_fee <= 0 or reserve_in <= 0 or reserve_out <= 0:
        return 0
    return (amount_after_fee * reserve_out) // (reserve_in + amount_after_fee)


def _swap_action(
    *,
    run_id: str,
    seed: str,
    step: int,
    agent: Mapping[str, Any],
    target_url: str,
    token: str,
    snapshot: Mapping[str, Any],
    pool: Mapping[str, Any],
    strategy: str,
    rng: random.Random,
) -> dict[str, Any]:
    asset0 = str(pool["asset0"])
    asset1 = str(pool["asset1"])
    reserve0 = int(pool["reserve0"])
    reserve1 = int(pool["reserve1"])
    if strategy == "momentum":
        asset_in = asset0 if reserve0 < reserve1 else asset1
    elif strategy == "mean_reversion":
        asset_in = asset1 if reserve0 < reserve1 else asset0
    else:
        asset_in = asset0 if rng.randrange(2) == 0 else asset1
    asset_out = asset1 if asset_in == asset0 else asset0
    reserve_in = reserve0 if asset_in == asset0 else reserve1
    spendable = max(1, _balance(snapshot, str(agent["pubkey"]), asset_in))
    if strategy == "whale":
        amount_in = max(1, min(spendable, max(1, reserve_in * rng.randint(250, 2_500) // 10_000)))
    else:
        amount_in = max(1, min(spendable, max(1, reserve_in * rng.randint(5, 180) // 10_000)))
    quoted_out = _quote_exact_in(pool, asset_in, amount_in)
    if strategy == "high_min_out_probe":
        min_amount_out = max(quoted_out + 1, reserve0 + reserve1)
        expected_valid = True
        expected_economic_fill = False
    else:
        min_amount_out = max(1, quoted_out * 8_500 // 10_000)
        expected_valid = True
        expected_economic_fill = True
    now_ms = int(time.time() * 1000)
    tx = {
        "tx_id": f"{run_id}-swap-{step}",
        "block_timestamp": now_ms // 1000,
        "tx_sender_pubkey": agent["pubkey"],
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "SWAP_EXACT_IN",
                    "intent_id": "0x" + hashlib.sha256(f"{run_id}:swap:{step}".encode("utf-8")).hexdigest(),
                    "sender_pubkey": agent["pubkey"],
                    "deadline": now_ms // 1000 + 3600,
                    "nonce": _nonce(snapshot, str(agent["pubkey"])) + 1,
                    "pool_id": pool["pool_id"],
                    "asset_in": asset_in,
                    "asset_out": asset_out,
                    "amount_in": amount_in,
                    "min_amount_out": min_amount_out,
                    "recipient": agent["pubkey"],
                }
            ]
        },
    }
    return _submit_tx(
        run_id=run_id,
        seed=seed,
        step=step,
        agent=agent,
        target_url=target_url,
        token=token,
        tx=tx,
        expected_valid=expected_valid,
        action_family=strategy,
        context={
            "pool": dict(pool),
            "quoted_out": quoted_out,
            "stress_bps": amount_in * 10_000 // max(1, reserve_in),
            "expected_economic_fill": expected_economic_fill,
        },
    )


def _liquidity_action(
    *,
    run_id: str,
    seed: str,
    step: int,
    agent: Mapping[str, Any],
    target_url: str,
    token: str,
    snapshot: Mapping[str, Any],
    pool: Mapping[str, Any],
    rng: random.Random,
) -> dict[str, Any]:
    pool_id = str(pool["pool_id"])
    lp_balance = _lp_balance(snapshot, str(agent["pubkey"]), pool_id)
    do_remove = lp_balance > 0 and rng.randrange(3) == 0
    now_ms = int(time.time() * 1000)
    if do_remove:
        op = {
            "module": "TauSwap",
            "version": "0.1",
            "kind": "REMOVE_LIQUIDITY",
            "intent_id": "0x" + hashlib.sha256(f"{run_id}:remove:{step}".encode("utf-8")).hexdigest(),
            "sender_pubkey": agent["pubkey"],
            "deadline": now_ms // 1000 + 3600,
            "nonce": _nonce(snapshot, str(agent["pubkey"])) + 1,
            "pool_id": pool_id,
            "lp_amount": max(1, min(lp_balance, rng.randint(1, max(1, lp_balance // 4)))),
            "amount0_min": 0,
            "amount1_min": 0,
            "recipient": agent["pubkey"],
        }
        family = "liquidity_remove"
    else:
        amount0 = max(1, min(_balance(snapshot, str(agent["pubkey"]), str(pool["asset0"])), rng.randint(10, 500)))
        amount1 = max(1, min(_balance(snapshot, str(agent["pubkey"]), str(pool["asset1"])), rng.randint(10, 500)))
        op = {
            "module": "TauSwap",
            "version": "0.1",
            "kind": "ADD_LIQUIDITY",
            "intent_id": "0x" + hashlib.sha256(f"{run_id}:add:{step}".encode("utf-8")).hexdigest(),
            "sender_pubkey": agent["pubkey"],
            "deadline": now_ms // 1000 + 3600,
            "nonce": _nonce(snapshot, str(agent["pubkey"])) + 1,
            "pool_id": pool_id,
            "amount0_desired": amount0,
            "amount1_desired": amount1,
            "amount0_min": 0,
            "amount1_min": 0,
            "recipient": agent["pubkey"],
        }
        family = "liquidity_add"
    tx = {
        "tx_id": f"{run_id}-{family}-{step}",
        "block_timestamp": now_ms // 1000,
        "tx_sender_pubkey": agent["pubkey"],
        "operations": {"2": [op]},
    }
    return _submit_tx(
        run_id=run_id,
        seed=seed,
        step=step,
        agent=agent,
        target_url=target_url,
        token=token,
        tx=tx,
        expected_valid=True,
        action_family=family,
        context={"pool": dict(pool), "lp_balance": lp_balance},
    )


def _submit_faucet(
    *,
    run_id: str,
    seed: str,
    step: int,
    agent: Mapping[str, Any],
    target_url: str,
    token: str,
    asset: str,
    amount: int,
    expected_valid: bool,
    action_family: str,
) -> dict[str, Any]:
    now_ms = int(time.time() * 1000)
    body = {
        "to_pubkey": agent["pubkey"],
        "asset": asset,
        "amount": amount,
        "time_ms": now_ms,
        "tx_id": f"{run_id}-faucet-{agent['index']}-{asset[-4:]}-{step}-{now_ms}",
    }
    status, response = _post_json(_join(target_url, "faucet"), body, token=token)
    return _row(
        run_id=run_id,
        seed=seed,
        step=step,
        agent=agent,
        target_url=target_url,
        request_kind="faucet",
        action_family=action_family,
        request_body=body,
        http_status=status,
        response=response,
        expected_valid=expected_valid,
        context={"asset": asset, "amount": amount},
    )


def _submit_tx(
    *,
    run_id: str,
    seed: str,
    step: int,
    agent: Mapping[str, Any],
    target_url: str,
    token: str,
    tx: Mapping[str, Any],
    expected_valid: bool,
    action_family: str,
    context: Mapping[str, Any],
) -> dict[str, Any]:
    body = {"time_ms": int(time.time() * 1000), "tx": dict(tx)}
    status, response = _post_json(_join(target_url, "tx"), body, token=token)
    return _row(
        run_id=run_id,
        seed=seed,
        step=step,
        agent=agent,
        target_url=target_url,
        request_kind="tx",
        action_family=action_family,
        request_body=body,
        http_status=status,
        response=response,
        expected_valid=expected_valid,
        context=context,
    )


def _row(
    *,
    run_id: str,
    seed: str,
    step: int,
    agent: Mapping[str, Any],
    target_url: str,
    request_kind: str,
    action_family: str,
    request_body: Mapping[str, Any],
    http_status: int,
    response: Mapping[str, Any],
    expected_valid: bool,
    context: Mapping[str, Any],
) -> dict[str, Any]:
    receipt = response.get("receipt")
    receipt_accepted = receipt.get("accepted") if isinstance(receipt, Mapping) else None
    accepted = response.get("tx_accepted") is True or receipt_accepted is True or (
        request_kind == "faucet" and http_status == HTTPStatus.OK and response.get("ok") is True
    )
    rejected = response.get("tx_accepted") is False or receipt_accepted is False or response.get("ok") is not True
    return {
        "schema": ROW_SCHEMA,
        "run_id": run_id,
        "seed": seed,
        "step": step,
        "agent_id": agent.get("agent_id"),
        "agent_index": agent.get("index"),
        "agent_pubkey": agent.get("pubkey"),
        "target_url": target_url,
        "request_kind": request_kind,
        "action_family": action_family,
        "request_hash": _object_hash(request_body),
        "http_status": http_status,
        "response_ok": response.get("ok"),
        "accepted": bool(accepted),
        "rejected": bool(rejected),
        "expected_valid": expected_valid,
        "invalid_accepted": bool(not expected_valid and accepted),
        "height": response.get("height"),
        "tx_hash": response.get("tx_hash"),
        "receipt_hash": receipt.get("receipt_hash") if isinstance(receipt, Mapping) else None,
        "error": response.get("error") or (receipt.get("error_code") if isinstance(receipt, Mapping) else None),
        "context": dict(context),
        "response": dict(response),
    }


def _local_error_row(*, run_id: str, seed: str, step: int, error: str) -> dict[str, Any]:
    return {
        "schema": ROW_SCHEMA,
        "run_id": run_id,
        "seed": seed,
        "step": step,
        "agent_id": "local",
        "target_url": "",
        "request_kind": "local",
        "action_family": "local_error",
        "request_hash": "",
        "http_status": 0,
        "response_ok": False,
        "accepted": False,
        "rejected": True,
        "expected_valid": False,
        "invalid_accepted": False,
        "height": None,
        "tx_hash": None,
        "receipt_hash": None,
        "error": error,
        "context": {},
        "response": {"ok": False, "error": error},
    }


def _summarize_rows(rows: list[Mapping[str, Any]]) -> dict[str, Any]:
    action_counts: dict[str, int] = {}
    accepted_count = 0
    rejected_count = 0
    invalid_probe_count = 0
    for row in rows:
        action = str(row.get("action_family", "unknown"))
        action_counts[action] = action_counts.get(action, 0) + 1
        accepted_count += 1 if row.get("accepted") is True else 0
        rejected_count += 1 if row.get("rejected") is True else 0
        invalid_probe_count += 1 if row.get("expected_valid") is False else 0
    return {
        "submission_count": len(rows),
        "accepted_count": accepted_count,
        "rejected_count": rejected_count,
        "invalid_probe_count": invalid_probe_count,
        "action_counts": dict(sorted(action_counts.items())),
    }


if __name__ == "__main__":
    raise SystemExit(main())
