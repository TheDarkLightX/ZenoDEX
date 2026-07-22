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
CLI_PATH = REPO_ROOT / "tools" / "zenograph_autotrader_shadow_compare.py"


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


def _policy_document() -> dict[str, object]:
    strategy = compile_policy_candidate(
        {
            "strategy_id": "zenograph.compare.cli.1",
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


def test_zenograph_autotrader_shadow_compare_cli_roundtrip(tmp_path: Path) -> None:
    policy_document = _policy_document()
    receipt, pools = _receipt_and_pools()
    input_path = tmp_path / "compare_input.json"
    report_path = tmp_path / "compare_report.json"
    log_path = tmp_path / "compare_log.jsonl"
    input_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/zenograph-autotrader-shadow-compare-input/v1",
                "cases": [
                    {
                        "case_id": "aligned-dca",
                        "policy_document": policy_document,
                        "receipt": receipt,
                        "pools": pools,
                        "current_epoch": 5,
                        "intent_deadline": 99,
                        "chain_id": "tau-net-alpha",
                        "zenograph_source_trust": "trusted",
                        "zenograph_liquidity_state": "deep",
                    },
                    {
                        "case_id": "governance-block-disagreement",
                        "policy_document": policy_document,
                        "receipt": receipt,
                        "pools": pools,
                        "current_epoch": 5,
                        "intent_deadline": 99,
                        "chain_id": "tau-net-alpha",
                        "zenograph_source_trust": "trusted",
                        "zenograph_liquidity_state": "deep",
                        "zenograph_facts": {
                            "protocol": {"governance_attack_risk": "elevated"}
                        },
                    },
                    {
                        "case_id": "slippage-limit-disagreement",
                        "policy_document": policy_document,
                        "receipt": receipt,
                        "pools": pools,
                        "current_epoch": 5,
                        "intent_deadline": 99,
                        "chain_id": "tau-net-alpha",
                        "controller_slippage_bps": 60,
                        "zenograph_source_trust": "trusted",
                        "zenograph_liquidity_state": "deep",
                    },
                ],
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
            "--input",
            str(input_path),
            "--report-out",
            str(report_path),
            "--log-out",
            str(log_path),
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    stdout_payload = json.loads(completed.stdout)
    report_payload = json.loads(report_path.read_text(encoding="utf-8"))
    log_rows = [json.loads(line) for line in log_path.read_text(encoding="utf-8").splitlines() if line.strip()]

    assert stdout_payload["case_count"] == 3
    assert report_payload["case_count"] == 3
    assert len(log_rows) == 3
    assert report_payload["controller_tag_summary"] == {"reject": 1, "submit": 2}
    assert report_payload["template_summary"] == {"dca": 3}
    assert report_payload["disagreement_rate"] == 2.0 / 3.0
    assert report_payload["selected_template_mismatch_rate"] == 0.0
    assert report_payload["controller_submit_vs_zenograph_block_rate"] == 1.0 / 3.0
    assert report_payload["controller_block_vs_zenograph_allow_rate"] == 1.0 / 3.0
    assert report_payload["first_disagreement"]["case_id"] == "governance-block-disagreement"
    assert log_rows[0]["disagreement"]["disagreement"] is False
    assert log_rows[1]["disagreement"]["controller_submit_vs_zenograph_block"] is True
    assert log_rows[2]["disagreement"]["controller_block_vs_zenograph_allow"] is True


def test_zenograph_autotrader_shadow_compare_cli_accepts_fact_pack_file(
    tmp_path: Path,
) -> None:
    policy_document = _policy_document()
    receipt, pools = _receipt_and_pools()
    input_path = tmp_path / "compare_input_single.json"
    report_path = tmp_path / "compare_report_single.json"
    fact_pack_path = tmp_path / "zenograph_fact_pack.json"
    signed_pack = sign_zenograph_fact_pack(
        build_zenograph_fact_pack(
            pack_name="zenograph.compare.cli.pack1",
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
            review_records=(_fact_pack_review("zenograph.compare.cli.pack1"),),
        ),
        privkey=21,
    )
    fact_pack_path.write_text(
        json.dumps(signed_pack.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )
    input_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/zenograph-autotrader-shadow-compare-input/v1",
                "cases": [
                    {
                        "case_id": "fact-pack-disagreement",
                        "policy_document": policy_document,
                        "receipt": receipt,
                        "pools": pools,
                        "current_epoch": 5,
                        "intent_deadline": 99,
                        "chain_id": "tau-net-alpha",
                        "zenograph_source_trust": "trusted",
                        "zenograph_liquidity_state": "deep",
                    }
                ],
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
            "--input",
            str(input_path),
            "--zenograph-fact-pack-file",
            str(fact_pack_path),
            "--report-out",
            str(report_path),
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    stdout_payload = json.loads(completed.stdout)
    report_payload = json.loads(report_path.read_text(encoding="utf-8"))
    assert stdout_payload["case_count"] == 1
    assert report_payload["disagreement_rate"] == 1.0
    assert report_payload["controller_submit_vs_zenograph_block_rate"] == 1.0
    assert report_payload["first_disagreement"]["case_id"] == "fact-pack-disagreement"
