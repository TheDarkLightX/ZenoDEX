from __future__ import annotations

import json
import subprocess
import sys

from src.agents.cross_pool_subset_dp_advisor import (
    CROSS_POOL_SUBSET_DP_ADVISOR_SCHEMA,
    advise_two_pool_cpmm_batch,
)
from src.core.cross_pool_subset_dp import SubsetDPLimits, TwoPoolCPMM


def test_advisor_reports_candidate_gap_for_known_counterexample() -> None:
    advisory = advise_two_pool_cpmm_batch(
        TwoPoolCPMM(1, 2, 0),
        TwoPoolCPMM(2, 2, 0),
        [1, 1, 2],
        candidate_amount_out_total=1,
        include_execution_preview=True,
    )

    packet = advisory.to_dict()
    assert packet["schema"] == CROSS_POOL_SUBSET_DP_ADVISOR_SCHEMA
    assert packet["status"] == "exact_available"
    assert packet["solver_kind"] == "multiset_dp"
    assert packet["exact_amount_out_total"] == 2
    assert packet["candidate_amount_out_total"] == 1
    assert packet["missed_output"] == 1
    assert packet["candidate_gap_bps"] == 5000
    assert packet["production_security_claim"] is False
    assert packet["settlement_authority"] is False
    assert packet["solver_authorizes_settlement"] is False
    assert len(packet["execution_preview"]) == 3


def test_advisor_fails_closed_when_exact_search_exceeds_limits() -> None:
    advisory = advise_two_pool_cpmm_batch(
        TwoPoolCPMM(10, 10, 0),
        TwoPoolCPMM(10, 10, 0),
        [1, 1],
        candidate_amount_out_total=0,
        limits=SubsetDPLimits(max_intents=1),
    )

    packet = advisory.to_dict()
    assert packet["status"] == "exact_unavailable"
    assert packet["exact_available"] is False
    assert packet["solver_kind"] == "unavailable"
    assert packet["exact_amount_out_total"] is None
    assert packet["candidate_amount_out_total"] == 0
    assert packet["missed_output"] is None
    assert "intent count exceeds" in packet["reason"]
    assert packet["settlement_authority"] is False


def test_cross_pool_subset_dp_advisor_cli_smoke() -> None:
    payload = {
        "pool0": {"x": 1, "y": 2, "fee_bps": 0},
        "pool1": {"x": 2, "y": 2, "fee_bps": 0},
        "intents": [1, 1, 2],
        "candidate_amount_out_total": 1,
    }

    proc = subprocess.run(
        [sys.executable, "tools/cross_pool_subset_dp_advisor.py"],
        input=json.dumps(payload),
        text=True,
        capture_output=True,
        check=True,
    )
    packet = json.loads(proc.stdout)

    assert packet["schema"] == CROSS_POOL_SUBSET_DP_ADVISOR_SCHEMA
    assert packet["status"] == "exact_available"
    assert packet["solver_kind"] == "multiset_dp"
    assert packet["exact_amount_out_total"] == 2
    assert packet["missed_output"] == 1
    assert packet["execution_preview"] == []
