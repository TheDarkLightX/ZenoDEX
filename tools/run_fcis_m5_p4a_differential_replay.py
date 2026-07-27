#!/usr/bin/env python3
"""Exact-vs-legacy differential replay harness for FCIS M5-P4A.

Replays every fixture from the golden baseline through the exact FCIS
evaluator (via the spot shadow adapter) and compares observable projections.
Produces a machine-readable JSON report with per-fixture parity status.

M5-P4A-DIFF-001: every baseline fixture is replayed through the exact path.
M5-P4A-DIFF-002: observable projections are compared field-by-field.
M5-P4A-DIFF-003: any divergence is reported as a BLOCKED parity failure.
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import Any

from src.core.batch_clearing import apply_settlement_pure, compute_settlement
from src.core.dex import DexConfig, DexState, step
from src.core.fees import FeeSplitParams, split_fee_with_dust_carry
from src.core.liquidity import create_pool
from src.core.settlement import Settlement
from src.integration.fcis_spot_shadow import (
    FCISSpotShadowContextV1,
    FCISStepShadowContextV1,
    FCISStepShadowPhaseV1,
    FCISStepShadowReceiptV1,
    FCISStepShadowRejectV1,
    evaluate_fcis_spot_candidate_shadow_v1,
    evaluate_fcis_step_shadow_v1,
)
from src.integration.lp_position_age_gate import LPDurationRiskPolicy
from src.state import BalanceTable, LPTable
from src.state.canonical import canonical_json_bytes, sha256_hex
from src.state.intents import Intent, IntentKind
from src.core.settlement_strong_validator import (
    StrongSettlementRejectV1,
    StrongSettlementStateCandidateV1,
)
from src.state.legacy_state_snapshots import (
    admit_legacy_balance_for_differential_v1,
    admit_legacy_lp_for_differential_v1,
    admit_legacy_pool_map_for_differential_v1,
)

_REPO_ROOT = Path(__file__).resolve().parents[1]
_BASELINE_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_LEGACY_BASELINE_V1.json"
_REPORT_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_DIFFERENTIAL_REPLAY_V1.json"
_SCHEMA = "zenodex/fcis-m5-p4a-differential-replay/v1"

_PUBKEY_A = "0x" + "11" * 48
_PUBKEY_B = "0x" + "22" * 48
_ASSET_0 = "0x" + "01" * 32
_ASSET_1 = "0x" + "02" * 32
_ASSET_2 = "0x" + "03" * 32


def _iid(value: int) -> str:
    return "0x" + f"{value:064x}"


def _base_pool_state() -> tuple[DexState, str]:
    pool_id, pool, lp_minted = create_pool(
        asset0=_ASSET_0,
        asset1=_ASSET_1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=_PUBKEY_A,
    )
    balances = BalanceTable()
    balances.set(_PUBKEY_A, _ASSET_0, 10_000_000)
    balances.set(_PUBKEY_A, _ASSET_1, 10_000_000)
    balances.set(_PUBKEY_B, _ASSET_0, 10_000_000)
    balances.set(_PUBKEY_B, _ASSET_1, 10_000_000)
    lp_balances = LPTable()
    lp_balances.set(_PUBKEY_A, pool_id, lp_minted)
    lp_balances.set("0x" + "00" * 48, pool_id, pool.lp_supply - lp_minted)
    lp_balances.set_last_mint_timestamp(_PUBKEY_A, pool_id, 100)
    state = DexState(
        balances=balances,
        pools={pool_id: pool},
        lp_balances=lp_balances,
    )
    return state, pool_id


def _second_pool_state(
    state: DexState,
) -> tuple[DexState, str]:
    pool_id_1, pool_1, lp_minted_1 = create_pool(
        asset0=_ASSET_1,
        asset1=_ASSET_2,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=_PUBKEY_A,
    )
    new_balances = BalanceTable()
    for (pubkey, asset), amount in state.balances.get_all_balances().items():
        new_balances.set(pubkey, asset, amount)
    new_balances.set(_PUBKEY_A, _ASSET_2, 10_000_000)
    new_balances.set(_PUBKEY_B, _ASSET_2, 10_000_000)
    new_pools = dict(state.pools)
    new_pools[pool_id_1] = pool_1
    new_lp = LPTable()
    for (pubkey, pool_pid), amount in state.lp_balances.get_all_balances().items():
        new_lp.set(pubkey, pool_pid, amount)
    for (pubkey, pool_pid), ts in state.lp_balances.get_all_last_mint_timestamps().items():
        new_lp.set_last_mint_timestamp(pubkey, pool_pid, ts)
    new_lp.set(_PUBKEY_A, pool_id_1, lp_minted_1)
    new_lp.set("0x" + "00" * 48, pool_id_1, pool_1.lp_supply - lp_minted_1)
    new_lp.set_last_mint_timestamp(_PUBKEY_A, pool_id_1, 100)
    return (
        DexState(
            balances=new_balances,
            pools=new_pools,
            lp_balances=new_lp,
        ),
        pool_id_1,
    )


def _build_intent_from_fixture(fixture: dict[str, Any]) -> Intent:
    """Reconstruct an Intent from the fixture's command bytes."""
    raise NotImplementedError("Use fixture index mapping instead")


def _build_all_fixtures() -> list[tuple[DexState, list[Intent], DexConfig, str, str]]:
    """Rebuild the same fixtures as the baseline builder."""
    from tools.build_fcis_m5_p4a_baseline import _build_fixture_inputs

    inputs = _build_fixture_inputs()
    return [
        (fi.state, fi.intents, fi.config, fi.fixture_id, fi.command_kind)
        for fi in inputs
    ]


def _run_exact_shadow(
    state: DexState,
    intents: list[Intent],
    config: DexConfig,
) -> dict[str, Any]:
    """Run the exact FCIS evaluator via the spot shadow adapter."""

    settlement = compute_settlement(
        intents=intents,
        pools=state.pools,
        balances=state.balances,
        lp_balances=state.lp_balances,
        swap_ordering=str(config.swap_ordering),
        protocol_fee_share_bps=config.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=config.protocol_fee_recipient_pubkey,
    )
    shadow_context = FCISSpotShadowContextV1(
        now=700,
        min_lp_position_age_seconds=0,
        mode="strong_replay",
        allow_cow_netting=False,
        allow_snapshot_bound_quote_bindings=False,
        protocol_fee_share_bps=config.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=config.protocol_fee_recipient_pubkey,
    )
    policy = LPDurationRiskPolicy(
        base_age_seconds=60,
        max_age_seconds=3_600,
        churn_window_seconds=600,
        decay_seconds=900,
        multiplier=2,
        max_churn_tier=5,
    )
    result = evaluate_fcis_spot_candidate_shadow_v1(
        state=state,
        settlement=settlement,
        intents=intents,
        context=shadow_context,
        lp_duration_policy=policy,
    )
    if type(result) is StrongSettlementStateCandidateV1:
        return {
            "exact_ok": True,
            "exact_balances": result.balances,
            "exact_pools": result.pools,
            "exact_lp_balances": result.lp_balances,
            "exact_error": None,
        }
    if type(result) is StrongSettlementRejectV1:
        return {
            "exact_ok": False,
            "exact_balances": None,
            "exact_pools": None,
            "exact_lp_balances": None,
            "exact_error": result.reason,
        }
    return {
        "exact_ok": False,
        "exact_balances": None,
        "exact_pools": None,
        "exact_lp_balances": None,
        "exact_error": f"unexpected result type: {type(result).__name__}",
    }


def _run_legacy(
    state: DexState,
    intents: list[Intent],
    config: DexConfig,
) -> dict[str, Any]:
    """Run the mounted legacy path via step()."""
    result = step(config=config, state=state, intents=intents)
    legacy_balances = None
    legacy_pools = None
    legacy_lp = None
    if result.ok and result.state is not None:
        legacy_balances = admit_legacy_balance_for_differential_v1(result.state.balances)
        legacy_pools = admit_legacy_pool_map_for_differential_v1(result.state.pools)
        legacy_lp = admit_legacy_lp_for_differential_v1(result.state.lp_balances)
    return {
        "legacy_ok": result.ok,
        "legacy_balances": legacy_balances,
        "legacy_pools": legacy_pools,
        "legacy_lp": legacy_lp,
        "legacy_error": result.error,
    }


def _compare(
    legacy: dict[str, Any],
    exact: dict[str, Any],
) -> dict[str, Any]:
    """Compare observable projections at the snapshot level."""
    accept_match = legacy["legacy_ok"] == exact["exact_ok"]
    snapshot_match = True
    if legacy["legacy_ok"] and exact["exact_ok"]:
        snapshot_match = (
            legacy["legacy_balances"] == exact["exact_balances"]
            and legacy["legacy_pools"] == exact["exact_pools"]
            and legacy["legacy_lp"] == exact["exact_lp_balances"]
        )
    parity = accept_match and snapshot_match
    return {
        "parity": "MATCH" if parity else "DIVERGENCE",
        "accept_match": accept_match,
        "snapshot_match": snapshot_match,
        "legacy_ok": legacy["legacy_ok"],
        "exact_ok": exact["exact_ok"],
        "legacy_error": legacy["legacy_error"],
        "exact_error": exact["exact_error"],
    }


def _classify_divergence(
    comparison: dict[str, Any],
    fixture_id: str,
) -> str:
    """Classify a divergence into a known category."""
    if not comparison["accept_match"]:
        if comparison["legacy_ok"] is False and comparison["exact_ok"] is True:
            return "legacy_rejects_exact_accepts"
        return "legacy_accepts_exact_rejects"
    if not comparison["snapshot_match"]:
        return "snapshot_divergence_on_accept"
    return "unclassified_divergence"


def _build_report() -> dict[str, Any]:
    fixtures = _build_all_fixtures()
    results: list[dict[str, Any]] = []
    match_count = 0
    divergence_count = 0
    divergence_categories: dict[str, int] = {}
    for state, intents, config, fixture_id, command_kind in fixtures:
        legacy = _run_legacy(state, intents, config)
        exact = _run_exact_shadow(state, intents, config)
        comparison = _compare(legacy, exact)
        if comparison["parity"] == "MATCH":
            match_count += 1
        else:
            divergence_count += 1
            category = _classify_divergence(comparison, fixture_id)
            divergence_categories[category] = divergence_categories.get(category, 0) + 1
            comparison["divergence_category"] = category
        results.append({
            "fixture_id": fixture_id,
            "command_kind": command_kind,
            **comparison,
        })
    report: dict[str, Any] = {
        "schema": _SCHEMA,
        "fixture_count": len(fixtures),
        "match_count": match_count,
        "divergence_count": divergence_count,
        "divergence_categories": divergence_categories,
        "overall_parity": "MATCH" if divergence_count == 0 else "DIVERGENCE",
        "results": results,
    }
    report_bytes = canonical_json_bytes(report)
    report["report_sha256"] = "0x" + hashlib.sha256(report_bytes).hexdigest()
    return report


def _write_report(report: dict[str, Any]) -> None:
    _REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    _REPORT_PATH.write_bytes(canonical_json_bytes(report))


def main() -> int:
    check_mode = "--check" in sys.argv
    report = _build_report()
    if check_mode:
        if not _REPORT_PATH.exists():
            print("ERROR: differential replay report does not exist", file=sys.stderr)
            return 1
        existing = _REPORT_PATH.read_bytes()
        new_bytes = canonical_json_bytes(report)
        if existing != new_bytes:
            print("ERROR: differential replay report changed", file=sys.stderr)
            return 1
        print(f"OK: differential replay report matches (sha256={report['report_sha256']})")
        return 0
    _write_report(report)
    parity = report["overall_parity"]
    print(
        f"OK: wrote {_REPORT_PATH} "
        f"(parity={parity}, matches={report['match_count']}, "
        f"divergences={report['divergence_count']})"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
