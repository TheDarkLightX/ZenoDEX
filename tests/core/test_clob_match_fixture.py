"""The CLOB matcher parity fixture must stay current (Stage 2 I2).

The Rust matcher-parity test (zk/state_proof_risc0/cli/tests/clob_match_parity.rs)
pins clob::apply_clob_order against shared/src/clob_match_cases_v1.json. This test
ensures that fixture still matches the LIVE Python clob_matching.apply_order, so
the cross-language matcher parity cannot silently drift from the authority.
"""
from __future__ import annotations

from tools.gen_clob_match_fixture import main as gen_main


def test_clob_match_fixture_is_current():
    assert gen_main(["--check"]) == 0, "fixture stale; run tools/gen_clob_match_fixture.py"
