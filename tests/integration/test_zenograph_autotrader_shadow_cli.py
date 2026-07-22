from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.agents.krr_bundle_artifacts import KRRReviewRecord
from src.agents.local_policy import dump_local_policy_document
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.zenograph_fact_pack import (
    ZenoGraphFactRecord,
    build_zenograph_fact_pack,
    sign_zenograph_fact_pack,
)
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.state.immutable_json import snapshot_json_mapping
from src.state.pools import PoolState, PoolStatus

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "autotrader_shadow.py"


def _fact_pack_review(pack_name: str) -> KRRReviewRecord:
    return KRRReviewRecord(
        review_id=f"{pack_name}.review.runtime",
        target_kind="bundle",
        target_id=pack_name,
        decision="approve",
        reviewer="security.review",
        reviewed_at="2026-03-26T00:10:00Z",
        rationale="fact pack provenance complete and safe for advisory runtime use",
        approved_for_runtime=True,
        provenance_ok=True,
    )


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


def _policy_and_market(tmp_path: Path) -> tuple[Path, Path, Path]:
    strategy = compile_policy_candidate(
        {
            "strategy_id": "zenograph.shadow.cli.1",
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
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = snapshot_json_mapping(
        make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5),
        name="test_receipt",
    )

    policy_path = tmp_path / "policy.json"
    policy_path.write_text(json.dumps(dump_local_policy_document(strategy), indent=2), encoding="utf-8")
    pools_path = tmp_path / "pools.json"
    pools_path.write_text(
        json.dumps(
            {
                pid: {
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
                for pid, pool in pools.items()
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    receipt_path = tmp_path / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8")
    return policy_path, pools_path, receipt_path


def test_autotrader_shadow_cli_emits_zenograph_advisory_without_changing_controller_path(
    tmp_path: Path,
) -> None:
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path)
    facts_path = tmp_path / "zenograph_facts.json"
    facts_path.write_text(
        json.dumps({"protocol": {"governance_attack_risk": "elevated"}}, indent=2, sort_keys=True),
        encoding="utf-8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
            "--chain-id",
            "tau-net-alpha",
            "--zenograph-enable",
            "--zenograph-facts-file",
            str(facts_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    payload = json.loads(result.stdout)

    assert payload["schema"] == "zenodex/autotrader-shadow-report/v1"
    assert payload["risk_disclosure"]["advanced_feature"] is True
    assert payload["risk_disclosure"]["experimental"] is True
    assert payload["risk_disclosure"]["direct_capital_loss_possible"] is False
    assert payload["inputs"]["zenograph_enabled"] is True
    assert payload["decision"]["tag"] == "submit"
    assert payload["zenograph_advisory"] is not None
    assert payload["zenograph_advisory"]["strategy_template"] == "dca"
    assert payload["zenograph_advisory"]["tactic_evaluation"]["admissible"] is False
    assert "governance_risk_elevated" in payload["zenograph_advisory"]["tactic_evaluation"][
        "blocked_reasons"
    ]
    assert payload["zenograph_advisory"]["selected_template_id"] is None


def test_autotrader_shadow_cli_accepts_signed_zenograph_fact_pack(tmp_path: Path) -> None:
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path)
    fact_pack_path = tmp_path / "zenograph_fact_pack.json"
    signed_pack = sign_zenograph_fact_pack(
        build_zenograph_fact_pack(
            pack_name="zenograph.shadow.cli.pack1",
            built_at="2026-03-26T00:15:00Z",
            compiler_version="zenograph_fact_pack_v1",
            facts=(
                ZenoGraphFactRecord(
                    fact_id="protocol.governance_attack_risk",
                    subject_id="protocol",
                    predicate="governance_attack_risk",
                    value="elevated",
                    source_id="feed.news.alpha",
                    microtheory="RiskPolicy",
                    observed_at="2026-03-26T00:00:00Z",
                ),
            ),
            review_records=(_fact_pack_review("zenograph.shadow.cli.pack1"),),
        ),
        privkey=21,
    )
    fact_pack_path.write_text(
        json.dumps(signed_pack.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
            "--chain-id",
            "tau-net-alpha",
            "--zenograph-enable",
            "--zenograph-fact-pack-file",
            str(fact_pack_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stderr
    payload = json.loads(result.stdout)
    assert payload["risk_disclosure"]["advanced_feature"] is True
    assert payload["risk_disclosure"]["at_your_own_risk"] is True
    assert payload["zenograph_advisory"] is not None
    assert payload["zenograph_advisory"]["tactic_evaluation"]["admissible"] is False
    assert "governance_risk_elevated" in payload["zenograph_advisory"]["tactic_evaluation"][
        "blocked_reasons"
    ]
