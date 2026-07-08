#!/usr/bin/env python3
"""End-to-end smoke test for the local testnet UI + backend.

Tests every API lane that the UI depends on, then verifies the UI
HTML is served correctly. Run after `zenoctl testnet local up`.

Usage:
    python3 tools/zenoctl_testnet_local/e2e_smoke.py [--base http://localhost:18082]
"""
from __future__ import annotations

import argparse
import json
import sys
import time
import urllib.error
import urllib.request

DEFAULT_BASE = "http://localhost:18082"
TIMEOUT_S = 15.0


def _get_json(url: str, timeout_s: float = TIMEOUT_S) -> dict:
    req = urllib.request.Request(url, headers={"Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout_s) as resp:
        return json.loads(resp.read().decode("utf-8"))


def _get_text(url: str, timeout_s: float = TIMEOUT_S) -> str:
    req = urllib.request.Request(url)
    with urllib.request.urlopen(req, timeout=timeout_s) as resp:
        return resp.read().decode("utf-8")


def _check(name: str, condition: bool, detail: str = "") -> bool:
    status = "PASS" if condition else "FAIL"
    line = f"  [{status}] {name}"
    if detail:
        line += f" — {detail}"
    print(line)
    return condition


def run_smoke(base: str) -> int:
    failures = 0

    print(f"\n{'='*60}")
    print(f"  ZenoDEX Local Testnet E2E Smoke Test")
    print(f"  Base URL: {base}")
    print(f"{'='*60}\n")

    # ── 1. UI HTML is served ──────────────────────────────────────────
    print("── UI HTML ──")
    try:
        html = _get_text(f"{base}/")
        failures += not _check("UI HTML served", "<html" in html.lower(), f"{len(html)} bytes")
        failures += not _check("UI has root div", 'id="root"' in html, "")
        failures += not _check("UI has script tags", "<script" in html, "")
    except Exception as exc:
        failures += not _check("UI HTML served", False, str(exc))

    # ── 2. Spot / Pools lane ──────────────────────────────────────────
    print("\n── Spot / Pools ──")
    try:
        pools = _get_json(f"{base}/api/pools")
        failures += not _check("pools ok", pools.get("ok") is True, "")
        pool_list = pools.get("pools", [])
        failures += not _check("at least 1 pool", len(pool_list) >= 1, f"{len(pool_list)} pools")
        if pool_list:
            p = pool_list[0]
            failures += not _check(
                "pool has reserves",
                "reserve0" in p or "reserves" in p,
                f"keys: {list(p.keys())[:6]}",
            )
    except Exception as exc:
        failures += not _check("pools lane", False, str(exc))

    # ── 3. zUSD Wallet lane ───────────────────────────────────────────
    print("\n── zUSD Wallet ──")
    try:
        zusd_wallet = _get_json(f"{base}/api/zusd/wallet/status")
        status = zusd_wallet.get("status", {})
        failures += not _check("zusd_wallet ok", zusd_wallet.get("ok") is True, "")
        failures += not _check("node_reachable", status.get("node_reachable") is True, "")
    except Exception as exc:
        failures += not _check("zusd_wallet lane", False, str(exc))

    # ── 4. zUSD Monetary lane ─────────────────────────────────────────
    print("\n── zUSD Monetary ──")
    try:
        zusd_mon = _get_json(f"{base}/api/zusd/monetary/status")
        status = zusd_mon.get("status", {})
        failures += not _check("zusd_monetary ok", zusd_mon.get("ok") is True, "")
        failures += not _check("node_reachable", status.get("node_reachable") is True, "")
        failures += not _check(
            "monetary_state_present",
            status.get("monetary_state_present") is True,
            "",
        )
    except Exception as exc:
        failures += not _check("zusd_monetary lane", False, str(exc))

    # ── 5. Perps Wallet lane ──────────────────────────────────────────
    print("\n── Perps Wallet ──")
    try:
        perps = _get_json(f"{base}/api/perps/wallet/status", timeout_s=20.0)
        status = perps.get("status", {})
        failures += not _check("perps_wallet ok", perps.get("ok") is True, "")
        failures += not _check("node_reachable", status.get("node_reachable") is True, "")
        market_count = int(status.get("market_count") or 0)
        failures += not _check("market_count >= 1", market_count >= 1, f"{market_count} markets")
        wa = status.get("wallet_authority", {})
        failures += not _check("wallet_authority ok", wa.get("ok") is True, "")
        oa = status.get("oracle_authority", {})
        failures += not _check("oracle_authority ok", oa.get("ok") is True, "")
    except Exception as exc:
        failures += not _check("perps_wallet lane", False, str(exc))

    # ── 6. Autotrader / Strategy lane ─────────────────────────────────
    print("\n── Autotrader / Strategy ──")
    try:
        auto = _get_json(f"{base}/api/strategy/autotrader/status")
        supervisor = auto.get("status", {}).get("supervisor", {})
        failures += not _check("autotrader ok", auto.get("ok") is True, "")
        failures += not _check("supervisor ok", supervisor.get("ok") is True, "")
    except Exception as exc:
        failures += not _check("autotrader lane", False, str(exc))

    # ── 7. Oracle Health lane ─────────────────────────────────────────
    print("\n── Oracle Health ──")
    try:
        oracle = _get_json(f"{base}/api/oracle/health")
        failures += not _check("oracle_health ok", oracle.get("ok") is True, "")
    except Exception as exc:
        failures += not _check("oracle_health lane", False, str(exc))

    # ── 8. Oracle Dashboard lane ──────────────────────────────────────
    print("\n── Oracle Dashboard ──")
    try:
        dash = _get_json(f"{base}/api/oracle/dashboard")
        failures += not _check("oracle_dashboard ok", dash.get("ok") is True, "")
    except Exception as exc:
        failures += not _check("oracle_dashboard lane", False, str(exc))

    # ── 9. Confidential lane ──────────────────────────────────────────
    print("\n── Confidential ──")
    try:
        conf = _get_json(f"{base}/api/confidential/status")
        failures += not _check("confidential ok", conf.get("ok") is True, "")
    except Exception as exc:
        failures += not _check("confidential lane", False, str(exc))

    # ── 10. Swap quote — client-side path verification ────────────────
    # The UI computes quotes client-side using pool data from /api/pools.
    # Verify the pool data has the fields needed for CPMM quote computation.
    print("\n── Swap Quote Data (client-side path) ──")
    try:
        pools = _get_json(f"{base}/api/pools")
        pool_list = pools.get("pools", [])
        if pool_list:
            p = pool_list[0]
            has_reserves = (
                p.get("reserve0") is not None and p.get("reserve1") is not None
            ) or (
                p.get("reserves") and len(p["reserves"]) >= 2
            )
            failures += not _check(
                "pool has reserve data",
                has_reserves,
                f"reserve0={p.get('reserve0')}, reserve1={p.get('reserve1')}",
            )
            failures += not _check(
                "pool has asset IDs",
                bool(p.get("asset0")) and bool(p.get("asset1")),
                f"asset0={str(p.get('asset0'))[:16]}...",
            )
            failures += not _check(
                "pool has fee",
                p.get("feeBps") is not None or p.get("fee_bps") is not None,
                f"feeBps={p.get('feeBps')}",
            )
        else:
            failures += not _check("pool data for quote", False, "no pools")
    except Exception as exc:
        failures += not _check("swap quote data", False, str(exc))

    # ── Summary ───────────────────────────────────────────────────────
    print(f"\n{'='*60}")
    if failures == 0:
        print("  ALL CHECKS PASSED")
    else:
        print(f"  {failures} CHECK(S) FAILED")
    print(f"{'='*60}\n")

    return 1 if failures > 0 else 0


def main() -> int:
    parser = argparse.ArgumentParser(description="ZenoDEX local testnet E2E smoke test")
    parser.add_argument("--base", default=DEFAULT_BASE, help="Base URL (default: http://localhost:18082)")
    parser.add_argument("--wait", type=int, default=0, help="Wait N seconds before testing")
    args = parser.parse_args()

    if args.wait > 0:
        print(f"Waiting {args.wait}s for stack to settle...")
        time.sleep(args.wait)

    return run_smoke(args.base)


if __name__ == "__main__":
    sys.exit(main())
