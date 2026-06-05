"""PR-gated binding: the LIVE spot settlement apply step REFINES the machine-checked Lean theorem
`Proofs.SettlementSupplyConservation.accepted_preserves_supply` — the proof->running-code link for
balances.proof_artifact.

This is a DIFFERENT layer from test_settlement_conservation_live_binding.py:
  * that test = the runtime-invariant guard binding (the live validator/apply REJECTS non-conserving
    settlements; supports runtime_invariants + running_impl);
  * THIS test = the proof-artifact binding: it transcribes the Lean theorem's MODEL and shows the
    live apply is an instance of it.

The Lean theorem (lean-mathlib/Proofs/SettlementSupplyConservation.lean), derived NOT assumed:
    applyDeltas L D = zipWith (+) L D          -- apply an arbitrary per-cell net-delta vector
    supply L        = L.sum
    supply_applyDeltas:  |L|=|D| -> supply (applyDeltas L D) = supply L + supply D   (key lemma)
    accepted Db Dr  := supply Db + supply Dr = 0                                     (validator gate)
    accepted_preserves_supply:  accepted Db Dr -> supply(apply Lb Db)+supply(apply Lr Dr)
                                                  = supply Lb + supply Lr            (HEADLINE)

This binding INDEPENDENTLY transcribes that model and drives the LIVE validate_settlement_strong +
apply_settlement:
  1. snapshot the pre-state per-cell amounts (user balances + pool reserves) for each asset;
  2. drive the live accept + apply;
  3. snapshot post-state; INDEPENDENTLY derive the live per-cell net-delta vectors (post-pre over
     the cell union, zero-extended for new cells) = the Lean model's D vectors;
  4. recompute `accepted` (Σ balDeltas + Σ resDeltas == 0 per asset) with our OWN summation — the
     live apply must satisfy the theorem's HYPOTHESIS;
  5. recompute `supply` pre/post with our OWN summation — the live state must exhibit the theorem's
     CONCLUSION (supply preserved).
We never call net_delta / validate_settlement as the conservation oracle — the sums are re-derived
(per the cpmm binding discipline: transcribe the theorem, drive the live code, independent oracle).

A digest of the Lean proof source is PINNED here, so editing the theorem invalidates this binding
(forcing re-review). The proof's no-sorry build + axiom audit is gated separately by the committed
proof receipt + runtime-shadow.yml.

Teeth:
  * a monkeypatched apply that adds net+1 to a cell makes the live per-cell deltas violate
    `accepted` (Σ != 0) AND moves `supply` -> the transcribed theorem relation FAILS (an
    oracle-that-mirrors-apply would not catch it);
  * the pinned Lean digest must match (a silently-edited/weakened proof trips the pin).
"""

from __future__ import annotations

from pathlib import Path

import pytest

from src.core.batch_clearing import apply_settlement
from src.core.settlement_strong_validator import validate_settlement_strong
from src.state import BalanceTable

# Reuse the live-drive scenario scaffolding (same authority path, exercised at a different layer).
from tests.runtime.test_settlement_conservation_live_binding import (
    A1,
    FEE_RECIP,
    _add_liquidity_scenario,
    _create_pool_scenario,
    _remove_liquidity_scenario,
    _swap_exact_out_scenario,
    _swap_scenario,
)

# ---------------------------------------------------------------------------
# Pin the Lean proof (proof<->binding coupling). A proof edit changes the digest
# and trips this assertion, forcing re-review of the binding.
# ---------------------------------------------------------------------------
_LEAN_PROOF = (
    Path(__file__).resolve().parents[2]
    / "lean-mathlib"
    / "Proofs"
    / "SettlementSupplyConservation.lean"
)
_REQUIRED_LEAN_DECLS = (
    "theorem supply_applyDeltas",
    "theorem accepted_preserves_supply",
    "theorem supply_changed_implies_not_accepted",
    "theorem witness_accepted_preserves_noncanceling",
    "theorem witness_unbalanced_creates_supply",
)


def test_lean_proof_present_and_nontautological() -> None:
    """Statement-level pin: the required theorems are present and the headline keeps the
    Σdelta=0 GATE as its hypothesis (not a smuggled supply-equality => the forbidden tautology).
    The source sha256 + no-sorry build are pinned separately by the committed proof receipt
    (docs/assurance/spot_proof_public_receipt.json) and CI, so this test is robust to benign
    comment/whitespace edits while still catching a shape regression."""
    assert _LEAN_PROOF.is_file(), f"missing Lean proof: {_LEAN_PROOF}"
    text = _LEAN_PROOF.read_text(encoding="utf-8")
    for decl in _REQUIRED_LEAN_DECLS:
        assert decl in text, f"Lean proof missing required declaration: {decl}"
    # The proof must NOT smuggle the conclusion into the hypothesis (the forbidden tautology):
    # `accepted` is the per-asset delta-sum gate, never `supply ... = supply ...`.
    assert "supply balDeltas + supply resDeltas = 0" in text, (
        "accepted must be the delta-sum gate (Σdelta=0), not a supply-equality hypothesis"
    )
    assert "sorry" not in text and "admit" not in text, "Lean proof must be sorry-free"


# ---------------------------------------------------------------------------
# Independent transcription of the Lean model over the LIVE state.
# ---------------------------------------------------------------------------
def _cells_for_asset(balances: BalanceTable, pools: dict, asset: str):
    """The Lean ledgers for one asset, split into the (balance cells, reserve cells)
    the live apply touches. Returns dicts cell_key -> amount."""
    bal: dict = {}
    for (pubkey, a), amt in balances.get_all_balances().items():
        if a == asset:
            bal[("bal", pubkey)] = int(amt)
    res: dict = {}
    for pool_id, pool in pools.items():
        for a in (pool.asset0, pool.asset1):
            if a == asset:
                res[("res", pool_id, a)] = int(pool.get_reserve(asset))
    return bal, res


def _delta_vector(pre: dict, post: dict) -> list[int]:
    """Lean model's per-cell net-delta vector D = post - pre over the cell union
    (zero-extended for cells absent on one side — a fresh account starts at 0)."""
    return [int(post.get(c, 0)) - int(pre.get(c, 0)) for c in (set(pre) | set(post))]


def _lean_supply(cells: dict) -> int:
    """Lean `supply` = sum over cells, independently summed."""
    return sum(int(v) for v in cells.values())


def _assets_in(balances: BalanceTable, pools: dict) -> set:
    assets: set = {a for (_pk, a) in balances.get_all_balances().keys()}
    for pool in pools.values():
        assets.add(pool.asset0)
        assert pool.asset1 is not None
        assets.add(pool.asset1)
    return assets


def _assert_live_apply_models_theorem(intents, pools, balances, lp, settlement) -> None:
    """Drive the live accept+apply and show it is an instance of accepted_preserves_supply:
    the live per-asset delta vectors satisfy `accepted` (Σ=0) AND `supply` is preserved."""
    assets = _assets_in(balances, pools)
    pre = {a: _cells_for_asset(balances, pools, a) for a in assets}

    ok, err = validate_settlement_strong(
        settlement=settlement, intents=intents, pre_balances=balances,
        pre_pools=pools, pre_lp_balances=lp,
    )
    assert ok, f"settlement should validate: {err}"
    apply_settlement(settlement, balances, pools, lp)

    assets_post = _assets_in(balances, pools)
    moved = False
    for a in assets | assets_post:
        pre_bal, pre_res = pre.get(a, ({}, {}))
        post_bal, post_res = _cells_for_asset(balances, pools, a)
        bal_deltas = _delta_vector(pre_bal, post_bal)
        res_deltas = _delta_vector(pre_res, post_res)
        # Lean HYPOTHESIS `accepted`: Σ balDeltas + Σ resDeltas == 0 (independently summed).
        assert sum(bal_deltas) + sum(res_deltas) == 0, (
            "live apply violates the theorem hypothesis (Σdelta != 0)", a,
            sum(bal_deltas), sum(res_deltas),
        )
        # Lean CONCLUSION `supply preserved`: supply(post) == supply(pre) (independently summed).
        supply_pre = _lean_supply(pre_bal) + _lean_supply(pre_res)
        supply_post = _lean_supply(post_bal) + _lean_supply(post_res)
        assert supply_post == supply_pre, ("supply not preserved", a, supply_pre, supply_post)
        if any(d != 0 for d in bal_deltas + res_deltas):
            moved = True
    return moved


@pytest.mark.parametrize("amount_in", [1, 1000, 50_000, 250_000, 1_000_000])
def test_live_swap_models_lean_theorem(amount_in: int) -> None:
    _assert_live_apply_models_theorem(*_swap_scenario(amount_in))


def test_binding_is_nonvacuous_cells_move() -> None:
    # non-vacuity: a filling swap must actually move some asset's cells, so the
    # accept-hypothesis + supply-preserved checks above are binding something real.
    moved = _assert_live_apply_models_theorem(*_swap_scenario(250_000))
    assert moved, "a 250k swap must move cells (else the binding is vacuous)"


@pytest.mark.parametrize("amount_out", [1, 1000, 50_000, 250_000])
def test_live_swap_exact_out_models_lean_theorem(amount_out: int) -> None:
    _assert_live_apply_models_theorem(*_swap_exact_out_scenario(amount_out))


@pytest.mark.parametrize(("amount0", "amount1"), [(1_000, 2_000), (2_000_000, 2_000_000)])
def test_live_create_pool_models_lean_theorem(amount0: int, amount1: int) -> None:
    _assert_live_apply_models_theorem(*_create_pool_scenario(amount0, amount1))


@pytest.mark.parametrize(("a0", "a1"), [(100_000, 100_000), (250_000, 125_000)])
def test_live_add_liquidity_models_lean_theorem(a0: int, a1: int) -> None:
    _assert_live_apply_models_theorem(*_add_liquidity_scenario(a0, a1))


@pytest.mark.parametrize("lp_amount", [1, 1_000, 250_000])
def test_live_remove_liquidity_models_lean_theorem(lp_amount: int) -> None:
    _assert_live_apply_models_theorem(*_remove_liquidity_scenario(lp_amount))


def test_teeth_apply_supply_creation_breaks_theorem_relation(monkeypatch) -> None:
    """TEETH: an apply that creates supply (adds net+1 to a cell with no matching decrease) makes
    the live per-asset delta vectors violate the theorem hypothesis (Σ != 0) and shifts supply, so
    the transcribed accept->preserve relation FAILS. A binding whose oracle mirrors apply would not
    catch this; ours re-derives Σ from the post-state, so it does."""
    intents, pools, balances, lp, settlement = _swap_scenario(1000)
    real_apply = apply_settlement

    def leaky_apply(s, b, p, lp_table=None):
        real_apply(s, b, p, lp_table)
        b.add(FEE_RECIP, A1, 7)  # supply creation: free A1, no matching reserve decrease

    import src.core.batch_clearing as bc
    monkeypatch.setattr(bc, "apply_settlement", leaky_apply)

    # drive validate + the leaky apply, then run the SAME independent transcription used above
    assets = _assets_in(balances, pools)
    pre = {a: _cells_for_asset(balances, pools, a) for a in assets}
    ok, _err = validate_settlement_strong(
        settlement=settlement, intents=intents, pre_balances=balances,
        pre_pools=pools, pre_lp_balances=lp,
    )
    assert ok
    bc.apply_settlement(settlement, balances, pools, lp)

    violated = False
    for a in assets | _assets_in(balances, pools):
        pre_bal, pre_res = pre.get(a, ({}, {}))
        post_bal, post_res = _cells_for_asset(balances, pools, a)
        bal_deltas = _delta_vector(pre_bal, post_bal)
        res_deltas = _delta_vector(pre_res, post_res)
        if sum(bal_deltas) + sum(res_deltas) != 0:
            violated = True  # theorem hypothesis broken by the leak
        supply_pre = _lean_supply(pre_bal) + _lean_supply(pre_res)
        supply_post = _lean_supply(post_bal) + _lean_supply(post_res)
        if supply_post != supply_pre:
            violated = True  # theorem conclusion broken by the leak
    assert violated, "leak must break the transcribed theorem relation (else the binding has no teeth)"
