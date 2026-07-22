from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.agents.local_policy import dump_local_policy_document
from src.agents.policy_compiler import compile_policy_candidate
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.state.immutable_json import snapshot_json_mapping
from src.state.pools import PoolState, PoolStatus

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "zenograph_autotrader_ranking_stage.py"


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _policy_document() -> dict[str, object]:
    strategy = compile_policy_candidate(
        {
            "strategy_id": "zenograph.stage.cli.1",
            "owner_pubkey": "owner.pubkey.1",
            "policy_backend": "local",
            "template": "dca",
            "asset_universe": ["A", "B"],
            "notional_caps": {
                "per_order_max": 100,
                "per_window_max": 500,
                "lifetime_max": 1_000,
            },
            "risk_limits": {
                "max_slippage_bps": 50,
                "max_oracle_staleness_epochs": 3,
            },
            "strategy_window": {
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
                "min_order_spacing_epochs": 0,
            },
            "controls": {
                "kill_switch_enabled": True,
                "max_live_orders": 3,
            },
            "template_params": {
                "fixed_order_size": 100,
                "cadence_epochs": 4,
                "asset_in": "A",
                "asset_out": "B",
            },
        }
    ).strategy
    return dump_local_policy_document(strategy)


def _receipt_and_pools() -> tuple[dict[str, object], list[dict[str, object]]]:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = snapshot_json_mapping(
        make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5),
        name="test_receipt",
    )
    payloads = [
        {
            "pool_id": pool.pool_id,
            "asset0": pool.asset0,
            "asset1": pool.asset1,
            "reserve0": pool.reserve0,
            "reserve1": pool.reserve1,
            "fee_bps": pool.fee_bps,
            "lp_supply": pool.lp_supply,
            "status": pool.status.value,
            "created_at": pool.created_at,
            "curve_tag": pool.curve_tag,
            "curve_params": pool.curve_params,
        }
        for pool in pools.values()
    ]
    return receipt, payloads


def test_zenograph_autotrader_ranking_stage_cli_emits_blocked_stage(tmp_path: Path) -> None:
    policy_path = tmp_path / "policy.json"
    receipt_path = tmp_path / "receipt.json"
    pools_path = tmp_path / "pools.json"
    facts_path = tmp_path / "facts.json"
    gate_report_path = tmp_path / "gate_report.json"

    policy_path.write_text(json.dumps(_policy_document(), indent=2, sort_keys=True), encoding="utf-8")
    receipt, pools = _receipt_and_pools()
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8")
    pools_path.write_text(json.dumps({"pools": pools}, indent=2, sort_keys=True), encoding="utf-8")
    facts_path.write_text(
        json.dumps({"protocol": {"governance_attack_risk": "elevated"}}, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    gate_report_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/zenograph-autotrader-ranking-promotion-gate-report/v1",
                "gate": {
                    "ranking_influence_allowed": False,
                    "block_reason": "submit_vs_block_disagreement",
                    "unmet_criteria": ["submit_vs_block_zero", "block_vs_allow_zero"],
                },
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    completed = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--gate-report-file",
            str(gate_report_path),
            "--zenograph-facts-file",
            str(facts_path),
            "--zenograph-source-trust",
            "trusted",
            "--zenograph-liquidity-state",
            "deep",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    payload = json.loads(completed.stdout)
    assert payload["risk_disclosure"]["advanced_feature"] is True
    assert payload["ranking_stage"]["stage_tag"] == "blocked"
    assert payload["ranking_stage"]["effective_ranking_template_id"] == "dca"
    assert payload["ranking_stage"]["block_reason"] == "submit_vs_block_disagreement"
    assert payload["zenograph_advisory"]["tactic_evaluation"]["admissible"] is False
