"""The CLOB matching-LAW parity fixture must stay current (Stage 2 I6).

The Rust law-parity test (zk/state_proof_risc0/cli/tests/clob_law_parity.rs)
pins clob::check_no_skip_law + clob_matching_law_rule_hash against
shared/src/clob_law_cases_v1.json. This test ensures that fixture still matches
the LIVE Python law checker (tools.clob_matching_law), so the cross-language law
verdicts -- and the journal-committed law identity -- cannot silently drift from
the authority.
"""
from __future__ import annotations

from tools.gen_clob_law_fixture import main as gen_main


def test_clob_law_fixture_is_current():
    assert gen_main(["--check"]) == 0, "fixture stale; run tools/gen_clob_law_fixture.py"
