#!/usr/bin/env python3
"""Generate a bounded signed-pack replay baseline for controller vs ZenoGraph shadow comparison."""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from collections.abc import Mapping
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.krr_bundle_artifacts import KRRReviewRecord  # noqa: E402
from src.agents.local_policy import dump_local_policy_document  # noqa: E402
from src.agents.policy_compiler import compile_policy_candidate  # noqa: E402
from src.agents.zenograph_fact_pack import (  # noqa: E402
    build_zenograph_fact_pack,
    sign_zenograph_fact_pack,
    zenograph_fact_record_from_accepted_fact,
    zenograph_runtime_facts,
)
from src.agents.zenograph_rules import ZGTrustTier  # noqa: E402
from src.agents.zenograph_schema import ZGFact, ZGFactStatus, ZGSourceKind  # noqa: E402
from src.agents.zenograph_store import ZenoGraphStore  # noqa: E402
from src.core.quote_receipts import make_route_quote_receipt  # noqa: E402
from src.core.routing import best_route_exact_in_2hop  # noqa: E402
from src.integration.autotrader_controller import AutoTraderControllerState  # noqa: E402
from src.integration.zenograph_shadow_compare import (  # noqa: E402
    build_zenograph_autotrader_shadow_comparison,
)
from src.state.pools import PoolState, PoolStatus  # noqa: E402


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


def _strategy():
    return compile_policy_candidate(
        {
            "strategy_id": "zenograph.baseline.dca.1",
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


def _market() -> tuple[dict[str, PoolState], Mapping[str, object]]:
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)
    return pools, receipt


def _review(pack_name: str) -> KRRReviewRecord:
    return KRRReviewRecord(
        review_id=f"{pack_name}.review.runtime",
        target_kind="bundle",
        target_id=pack_name,
        decision="approve",
        reviewer="security.review",
        reviewed_at="2026-03-26T00:10:00Z",
        rationale="bounded baseline fact pack approved for advisory runtime use",
        approved_for_runtime=True,
        provenance_ok=True,
    )


def _accepted_fact(
    *,
    fact_id: str,
    subject_id: str,
    predicate: str,
    value: object,
    source_id: str,
) -> ZGFact:
    return ZGFact(
        fact_id=fact_id,
        status=ZGFactStatus.ACCEPTED,
        subject_id=subject_id,
        predicate=predicate,
        value=value,
        source_id=source_id,
        source_kind=ZGSourceKind.NEWS,
        microtheory="RiskPolicy",
        validator_status="validated",
        validation_receipt_ids=(f"receipt.{fact_id}",),
        accepted_by="validator.local.1",
    )


def _build_family_cases() -> list[dict[str, object]]:
    families: list[dict[str, object]] = []
    for idx in range(4):
        families.append(
            {
                "family": "aligned_neutral",
                "current_epoch": 5,
                "controller_slippage_bps": None,
                "facts": (
                    _accepted_fact(
                        fact_id=f"fact.aligned_neutral.{idx}",
                        subject_id="protocol",
                        predicate="governance_attack_risk",
                        value="low",
                        source_id=f"feed.news.neutral.{idx}",
                    ),
                ),
            }
        )
    for idx in range(4):
        families.append(
            {
                "family": "aligned_irrelevant",
                "current_epoch": 5,
                "controller_slippage_bps": None,
                "facts": (
                    _accepted_fact(
                        fact_id=f"fact.aligned_irrelevant.{idx}",
                        subject_id=f"theme.{idx}",
                        predicate="watch_state",
                        value="observe",
                        source_id=f"feed.news.irrelevant.{idx}",
                    ),
                ),
            }
        )
    for idx in range(4):
        families.append(
            {
                "family": "governance_block",
                "current_epoch": 5,
                "controller_slippage_bps": None,
                "facts": (
                    _accepted_fact(
                        fact_id=f"fact.governance_block.{idx}",
                        subject_id="protocol",
                        predicate="governance_attack_risk",
                        value="elevated",
                        source_id=f"feed.news.block.{idx}",
                    ),
                ),
            }
        )
    for idx in range(4):
        families.append(
            {
                "family": "oracle_stale_block",
                "current_epoch": 9,
                "controller_slippage_bps": None,
                "facts": (
                    _accepted_fact(
                        fact_id=f"fact.oracle_stale_block.{idx}",
                        subject_id="protocol",
                        predicate="governance_attack_risk",
                        value="low",
                        source_id=f"feed.news.stale.{idx}",
                    ),
                ),
            }
        )
    for idx in range(4):
        families.append(
            {
                "family": "slippage_limit_block",
                "current_epoch": 5,
                "controller_slippage_bps": 60,
                "facts": (
                    _accepted_fact(
                        fact_id=f"fact.slippage_limit_block.{idx}",
                        subject_id="protocol",
                        predicate="governance_attack_risk",
                        value="low",
                        source_id=f"feed.news.slippage.{idx}",
                    ),
                ),
            }
        )
    return families


def run_baseline(
    *,
    report_path: Path | None = None,
    log_path: Path | None = None,
) -> dict[str, object]:
    strategy = _strategy()
    pools, receipt = _market()
    rows: list[dict[str, object]] = []
    family_rows: dict[str, list[dict[str, object]]] = {}

    with tempfile.TemporaryDirectory(prefix="zenograph_baseline_") as tmp_dir:
        tmp_root = Path(tmp_dir)
        for index, case in enumerate(_build_family_cases()):
            family = str(case["family"])
            facts = tuple(case["facts"])
            current_epoch = int(case["current_epoch"])
            controller_slippage_bps = (
                None
                if case.get("controller_slippage_bps") is None
                else int(case["controller_slippage_bps"])
            )
            store_root = tmp_root / f"store_{index}"
            store = ZenoGraphStore(store_root)
            for fact in facts:
                store.append_fact(fact)
            pack_name = f"zenograph.baseline.{family}.{index}"
            accepted_rows = tuple(store.iter_facts(status=ZGFactStatus.ACCEPTED))
            signed_pack = sign_zenograph_fact_pack(
                build_zenograph_fact_pack(
                    pack_name=pack_name,
                    built_at="2026-03-26T00:15:00Z",
                    compiler_version="zenograph_baseline_v1",
                    facts=tuple(
                        zenograph_fact_record_from_accepted_fact(fact)
                        for fact in accepted_rows
                    ),
                    review_records=(_review(pack_name),),
                ),
                privkey=21,
            )
            observation = build_zenograph_autotrader_shadow_comparison(
                strategy=strategy,
                controller_state=AutoTraderControllerState(),
                receipt=receipt,
                pools_by_id=pools,
                current_epoch=current_epoch,
                intent_deadline=99,
                chain_id="tau-net-alpha",
                facts=zenograph_runtime_facts(signed_pack),
                source_trust=ZGTrustTier.TRUSTED,
                liquidity_state="deep",
                controller_slippage_bps=controller_slippage_bps,
            )
            row = observation.to_dict()
            row["case_id"] = f"{family}-{index}"
            row["family"] = family
            row["baseline_current_epoch"] = current_epoch
            row["baseline_controller_slippage_bps"] = controller_slippage_bps
            row["fact_pack_hash"] = signed_pack.pack_hash_hex()
            row["runtime_fact_count"] = len(signed_pack.facts)
            rows.append(row)
            family_rows.setdefault(family, []).append(row)

    case_count = float(len(rows))
    report = {
        "schema": "zenodex/zenograph-autotrader-shadow-compare-baseline/v1",
        "case_count": len(rows),
        "input_kind": "accepted_store_exports",
        "strategy_template": strategy.template.value,
        "policy_document": dump_local_policy_document(strategy),
        "disagreement_rate": sum(int(bool(row["disagreement"]["disagreement"])) for row in rows)
        / case_count,
        "controller_submit_vs_zenograph_block_rate": sum(
            int(bool(row["disagreement"]["controller_submit_vs_zenograph_block"])) for row in rows
        )
        / case_count,
        "controller_block_vs_zenograph_allow_rate": sum(
            int(bool(row["disagreement"]["controller_block_vs_zenograph_allow"])) for row in rows
        )
        / case_count,
        "selected_template_mismatch_rate": sum(
            int(bool(row["disagreement"]["selected_template_mismatch"])) for row in rows
        )
        / case_count,
        "family_summary": {
            family: {
                "case_count": len(items),
                "disagreement_rate": sum(
                    int(bool(row["disagreement"]["disagreement"])) for row in items
                )
                / float(len(items)),
                "controller_submit_vs_zenograph_block_rate": sum(
                    int(bool(row["disagreement"]["controller_submit_vs_zenograph_block"]))
                    for row in items
                )
                / float(len(items)),
                "controller_block_vs_zenograph_allow_rate": sum(
                    int(bool(row["disagreement"]["controller_block_vs_zenograph_allow"]))
                    for row in items
                )
                / float(len(items)),
            }
            for family, items in sorted(family_rows.items())
        },
        "first_disagreement": next(
            (row for row in rows if bool(row["disagreement"]["disagreement"])),
            None,
        ),
        "log_path": None if log_path is None else str(log_path),
    }

    if log_path is not None:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        with log_path.open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, sort_keys=True) + "\n")

    if report_path is not None:
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-out", type=Path, default=None)
    parser.add_argument("--log-out", type=Path, default=None)
    args = parser.parse_args()

    report = run_baseline(
        report_path=args.report_out,
        log_path=args.log_out,
    )
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
