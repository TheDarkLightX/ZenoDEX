from __future__ import annotations

import sys
from pathlib import Path


def _import_miner():
    root = Path(__file__).resolve().parents[2]
    if str(root) not in sys.path:
        sys.path.insert(0, str(root))
    from tools.pokayoke.pokayoke_flip_miner import mine_pokayoke_adjacent_amount_flips

    return mine_pokayoke_adjacent_amount_flips


def test_pokayoke_flip_miner_finds_known_adjacent_drop_and_rise() -> None:
    mine = _import_miner()
    report = mine(
        reserve_in_values=[500],
        reserve_out_values=[500],
        fee_bps_values=[0],
        pending_volume_values=[0],
        confidence_bps_values=[9000],
        user_slippage_bps_values=[10],
        max_attacker_amount_in_values=[500],
        slippage_options_bps=[10, 50, 100, 300, 500],
        amount_min=18,
        amount_max=25,
        max_witnesses=16,
    )

    assert report["schema"] == "zenodex/pokayoke-flip-miner/v1"
    witnesses = report["witnesses"]
    assert any(
        w["kind"] == "severity_drop_adjacent"
        and w["amount_before"] == 20
        and w["amount_after"] == 21
        and w["action_before"] == "typed_confirm"
        and w["action_after"] == "confirm"
        and w["reasons_before"] == ["high_price_impact"]
        and w["reasons_after"] == ["moderate_price_impact"]
        for w in witnesses
    )
    assert any(
        w["kind"] == "severity_rise_adjacent"
        and w["amount_before"] == 22
        and w["amount_after"] == 23
        and w["action_before"] == "confirm"
        and w["action_after"] == "typed_confirm"
        and w["reasons_before"] == ["moderate_price_impact"]
        and w["reasons_after"] == ["mev_conflict", "high_price_impact"]
        for w in witnesses
    )


def test_pokayoke_flip_miner_reports_transition_clusters() -> None:
    mine = _import_miner()
    report = mine(
        reserve_in_values=[500],
        reserve_out_values=[500],
        fee_bps_values=[0],
        pending_volume_values=[0],
        confidence_bps_values=[9000],
        user_slippage_bps_values=[10],
        max_attacker_amount_in_values=[500],
        slippage_options_bps=[10, 50, 100, 300, 500],
        amount_min=18,
        amount_max=25,
        max_witnesses=16,
    )

    counts = {row["transition_key"]: row["count"] for row in report["transition_counts"]}
    assert counts["typed_confirm->confirm|high_price_impact=>moderate_price_impact"] == 1
    assert counts["confirm->typed_confirm|moderate_price_impact=>mev_conflict,high_price_impact"] == 1
    assert report["kind_counts"]["severity_drop_adjacent"] >= 1
    assert report["kind_counts"]["severity_rise_adjacent"] >= 1
