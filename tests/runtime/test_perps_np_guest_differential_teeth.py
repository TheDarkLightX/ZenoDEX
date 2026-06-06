"""P0-3 perps-NP differential: NON-VACUITY TEETH (required before commit).

A green corpus proves the guest matches the authority ONLY if the harness would
actually CATCH a divergence. These tests deliberately inject ONE defect each and
require ``run_case`` to FAIL -- the non-vacuity proof the advisor + the owner
mandated. They are kept in a SEPARATE file from the corpus suite.

  * mutate one numeric post-state field  -> harness fails (transition diff)
  * mutate one journal hash field        -> harness fails (encoder assertion)
  * break the adapter mapping            -> harness fails (transition diff)

(The fourth required tooth -- a reject case where both sides reject for the same
semantic class -- lives in the corpus's REJECT_CORPUS.)

SKIP (not fail) if the host-executed guest CLI is unavailable.
"""

from __future__ import annotations

import copy

import pytest

import tools.runtime.perps_np_guest_differential as diff
from tests.runtime import perps_np_differential_corpus as corpus

_CASE = {
    "name": "teeth_base",
    "actions": [corpus.init(), corpus.deposit(corpus.OWNER_A, 5_000 * corpus.E8, 1)],
}


@pytest.fixture(scope="module")
def cli_bin():
    try:
        return diff._ensure_cli()
    except diff.DifferentialError as exc:  # pragma: no cover - env-dependent
        pytest.skip(f"perps-np guest CLI unavailable: {exc}")


def _real_guest(cli_bin):
    g = diff.run_guest(_CASE["actions"], binp=cli_bin)
    assert g["accepted"], "teeth base case must accept (else the teeth prove nothing)"
    return g


def test_teeth_baseline_unmutated_case_is_equivalent(cli_bin):
    # Control: without any mutation the case is observationally equivalent, so the
    # failures below are caused by the injected defect, not a broken base.
    assert diff.run_case(_CASE, binp=cli_bin)["ok"]


def test_teeth_mutated_numeric_post_state_field_fails(cli_bin, monkeypatch):
    real = _real_guest(cli_bin)

    def corrupt(*_a, **_k):
        g = copy.deepcopy(real)
        g["post_snapshot"]["accounts"][0]["collateral_e8"] += 1  # off-by-one
        return g

    monkeypatch.setattr(diff, "run_guest", corrupt)
    res = diff.run_case(_CASE, binp=cli_bin)
    assert res["ok"] is False and "post_snapshot diverged" in res["reason"], res


def test_teeth_mutated_journal_hash_field_fails(cli_bin, monkeypatch):
    real = _real_guest(cli_bin)

    def corrupt(*_a, **_k):
        g = copy.deepcopy(real)
        # Snapshot left correct; only the committed hash is flipped -> the SEPARATE
        # encoder assertion (not the transition diff) must catch it.
        g["meta"]["post_app_hash"] = "00" * 32
        return g

    monkeypatch.setattr(diff, "run_guest", corrupt)
    res = diff.run_case(_CASE, binp=cli_bin)
    assert res["ok"] is False and "encoder divergence" in res["reason"], res


def test_teeth_broken_adapter_mapping_fails(cli_bin):
    # Guest unchanged + correct; a deliberately wrong authority->snapshot adapter
    # (collateral off-by-one) must surface as a divergence -- proves the
    # trusted-path adapter is not silently rubber-stamping.
    def broken_adapter(state, *, market_id, collateral_asset="zUSD"):
        snap = diff.state_to_snapshot(state, market_id=market_id, collateral_asset=collateral_asset)
        if snap["accounts"]:
            snap["accounts"][0]["collateral_e8"] += 1
        return snap

    res = diff.run_case(_CASE, binp=cli_bin, state_to_snapshot_fn=broken_adapter)
    assert res["ok"] is False and "post_snapshot diverged" in res["reason"], res
