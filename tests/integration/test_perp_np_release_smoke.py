"""CI gate for the N-party perps release smoke (3+ wallets, long/short, settle).

Wraps ``tools/zenodex_perp_np_release_smoke.py`` so the release-relevant
participation invariants are enforced deterministically in the test suite, not
only when the tool is run by hand.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.zenodex_perp_np_release_smoke import run_smoke  # noqa: E402


def test_perp_np_release_smoke_all(tmp_path):
    report = run_smoke(out_dir=tmp_path, scenario="all")
    assert report["ok"] is True
    assert report["production_security_claim"] is False
    assert report["market_kind"] == "clearinghouse_np_v1"
    assert report["oracle_signed_clearing_price"] is True
    assert report["case_count"] == 3
    seen_counts = set()
    for c in report["cases"]:
        assert c["ok"], c
        assert c["active_participants"] >= 3
        assert c["longs"] >= 1 and c["shorts"] >= 1, "must be genuinely two-sided"
        assert c["net_position"] == 0
        assert c["conservation_ok"] and c["insurance_ledger_ok"]
        assert c["deterministic_replay_ok"], "state-header agreement (deterministic replay)"
        assert c["snapshot_roundtrip_ok"]
        seen_counts.add(c["accounts"])
    # The scenarios genuinely exercise 3-, 4-, and 5-wallet markets.
    assert {3, 4, 5} <= seen_counts
