"""The CLOB book-root parity fixture must stay current (Stage 2).

The Rust parity test (zk/state_proof_risc0/cli/tests/clob_book_root_parity.rs)
pins the Rust ClobBookV1.state_root against shared/src/clob_book_roots_v1.json.
This test ensures that fixture still matches the LIVE Python clob_book.state_root,
so the cross-language parity fixture cannot silently drift from the authority.
"""
from __future__ import annotations

from tools.gen_clob_book_root_fixture import main as gen_main


def test_clob_book_root_fixture_is_current():
    assert gen_main(["--check"]) == 0, "fixture stale; run tools/gen_clob_book_root_fixture.py"
