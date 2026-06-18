from __future__ import annotations

import json

from src.core import split_routing as split_routing_mod
from src.core.split_routing import PoolXY, exact_out_for_pool_exact_in
from tools.benchmark_split_routing_profiles import (
    SplitRoutingBenchmarkCase,
    build_split_routing_profile_report,
    main,
)


def test_split_routing_profile_report_binds_profiles_to_bruteforce_oracle() -> None:
    cases = (
        SplitRoutingBenchmarkCase(
            name="known_gap",
            pool0=PoolXY(x=87, y=80, fee_bps=75),
            pool1=PoolXY(x=46, y=66, fee_bps=11),
            amount_in=6_539,
            tags=("known_gap",),
        ),
        SplitRoutingBenchmarkCase(
            name="skewed_endpoint",
            pool0=PoolXY(x=999_983, y=257, fee_bps=250),
            pool1=PoolXY(x=257, y=999_983, fee_bps=250),
            amount_in=3_000,
            tags=("endpoint",),
        ),
    )

    report = build_split_routing_profile_report(
        cases=cases,
        profiles=("adaptive_v6", "staircase_exact"),
    )

    assert report["schema"] == "zenodex/split_routing_profile_benchmark/v1"
    assert report["case_count"] == 2
    assert report["summary"]["staircase_exact"]["oracle_match_count"] == 2
    assert report["summary"]["staircase_exact"]["total_quote_count"] > 0
    for case in report["cases"]:
        assert case["oracle"]["status"] == "ok"
        assert case["profiles"]["staircase_exact"]["matches_oracle"] is True


def test_split_routing_profile_report_restores_live_quote_after_counting() -> None:
    assert split_routing_mod.exact_out_for_pool_exact_in is exact_out_for_pool_exact_in
    before = exact_out_for_pool_exact_in(PoolXY(x=1_000, y=1_000, fee_bps=0), 10)

    report = build_split_routing_profile_report(
        cases=(
            SplitRoutingBenchmarkCase(
                name="bad_profile",
                pool0=PoolXY(x=1_000, y=1_000, fee_bps=0),
                pool1=PoolXY(x=1_000, y=1_000, fee_bps=0),
                amount_in=100,
                tags=("reject",),
            ),
        ),
        profiles=("unsupported_profile",),
    )

    after = exact_out_for_pool_exact_in(PoolXY(x=1_000, y=1_000, fee_bps=0), 10)
    assert split_routing_mod.exact_out_for_pool_exact_in is exact_out_for_pool_exact_in
    assert before == after
    assert report["summary"]["unsupported_profile"]["reject_count"] == 1


def test_split_routing_profile_report_cli_writes_json(tmp_path, capsys) -> None:
    output_path = tmp_path / "split-routing-report.json"

    assert main(["--profiles", "staircase_exact", "--output-json", str(output_path)]) == 0

    stdout_report = json.loads(capsys.readouterr().out)
    file_report = json.loads(output_path.read_text(encoding="utf-8"))
    assert stdout_report == file_report
    assert file_report["summary"]["staircase_exact"]["oracle_match_count"] == file_report["case_count"]
