from __future__ import annotations

from tools.api_server_boundary_concolic import explore_all_targets, explore_target


def _labels(report) -> set[str]:
    return {case.outcome_label for case in report.cases}


def test_api_server_boundary_concolic_price_history_discovers_reject_paths() -> None:
    report = explore_target("price_history")
    labels = _labels(report)
    assert "ok" in labels
    assert "ValueError:price_history must be a 3-item array: [price_pp, price_prev, price_curr]" in labels
    assert "ValueError:price_history[0] must be a non-negative int" in labels
    assert "ValueError:price_history[1] must be a non-negative int" in labels
    assert "ValueError:price_history[2] must be a non-negative int" in labels
    assert report.unique_path_count >= 5


def test_api_server_boundary_concolic_proof_flags_discovers_reject_paths() -> None:
    report = explore_target("settlement_proof_flags")
    labels = _labels(report)
    assert "ok" in labels
    assert "ValueError:proof_flags must be an object" in labels
    assert "ValueError:proof_flags.cpmm_ok must be 0 or 1" in labels
    assert "ValueError:proof_flags.binding_ok must be 0 or 1" in labels
    assert "ValueError:proof_flags.proof_ok must be 0 or 1" in labels
    assert report.unique_path_count >= 5


def test_api_server_boundary_concolic_balance_parsers_discovers_reject_paths() -> None:
    balances = explore_target("balance_table")
    balance_labels = _labels(balances)
    assert "ok" in balance_labels
    assert "ValueError:balances must be a list" in balance_labels
    assert "ValueError:balances entries must be objects" in balance_labels
    assert "ValueError:balance pubkey must be a non-empty string" in balance_labels
    assert "ValueError:balance asset must be a non-empty string" in balance_labels
    assert "ValueError:balance amount must be a non-negative int" in balance_labels
    assert "ValueError:duplicate balance entry" in balance_labels
    assert balances.unique_path_count >= 9

    lp_balances = explore_target("lp_balances")
    lp_labels = _labels(lp_balances)
    assert "ok" in lp_labels
    assert "ValueError:lp_balances must be a list" in lp_labels
    assert "ValueError:lp_balances entries must be objects" in lp_labels
    assert "ValueError:lp balance pubkey must be a non-empty string" in lp_labels
    assert "ValueError:lp balance pool_id must be a non-empty string" in lp_labels
    assert "ValueError:lp balance amount must be a non-negative int" in lp_labels
    assert "ValueError:duplicate lp balance entry" in lp_labels
    assert lp_balances.unique_path_count >= 10


def test_api_server_boundary_concolic_feature_extension_discovers_reject_paths() -> None:
    report = explore_target("feature_extension_inputs")
    labels = _labels(report)
    assert "ok" in labels
    assert "ValueError:feature_extension_inputs must be an object" in labels
    assert "ValueError:missing feature extension input field: trade_amount" in labels
    assert "ValueError:missing feature extension input field: supply_after" in labels
    assert "ValueError:missing feature extension input field: weight_claimed" in labels
    assert "ValueError:trade_amount out of u16 range: 65536" in labels
    assert "ValueError:weighted_stake out of u16 range: 65536" in labels
    assert "ValueError:supply_before out of u32 range: 4294967296" in labels
    assert "ValueError:supply_floor out of u32 range: 4294967296" in labels
    assert "ValueError:supply_after must be an int" in labels
    assert report.unique_path_count >= 10


def test_api_server_boundary_concolic_all_targets_are_covered() -> None:
    reports = explore_all_targets()
    by_name = {report.target: report for report in reports}
    assert set(by_name) == {
        "price_history",
        "settlement_proof_flags",
        "balance_table",
        "lp_balances",
        "feature_extension_inputs",
    }
    assert by_name["price_history"].total_cases >= 5
    assert by_name["settlement_proof_flags"].total_cases >= 5
    assert by_name["balance_table"].total_cases >= 9
    assert by_name["lp_balances"].total_cases >= 10
    assert by_name["feature_extension_inputs"].total_cases >= 10
