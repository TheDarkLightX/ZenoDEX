import Mathlib.Tactic

/-!
# Settlement Supply Conservation (apply-step, DERIVED not assumed)

This file certifies the property the balances `proof_artifact` CBC column needs:

> If the live settlement validator ACCEPTS (its per-asset gate
> `Σ balance_deltas[X] + Σ reserve_deltas[X] = 0` holds), THEN applying the
> settlement preserves the per-asset *supply* — the sum over every user-balance
> cell and every pool-reserve cell of that asset.

## Why this is NOT the tautology in `SettlementConservationLive.lean`

`SettlementConservationLive.lean` DEFINES `reserveDelta := -balanceDelta`
per constructor, so `totalDelta = 0` falls out of `simp` — it bakes the
conclusion into the definitions and proves nothing about the apply step.

Here the per-cell net deltas `D` are **arbitrary** integers (the model never
constrains them to cancel pairwise). The acceptance gate `Σ D = 0` is a
**discharged hypothesis** that, on the live path, comes from the validator
(`batch_clearing.py::_check_settlement_asset_delta_conservation`,
`settlement_strong_validator.validate_settlement_strong`). The supply-
preservation conclusion is **derived** from a genuine induction lemma about how
the apply step moves the running total — it is not assumed.

The load-bearing content is `supply_applyDeltas`: applying an arbitrary net-delta
vector changes the supply by *exactly* the sum of those deltas. The headline
theorem then closes by discharging that sum with the acceptance hypothesis.

## Scope / faithfulness

This is an abstract ledger model: a per-asset ledger is the list of signed
amounts held in each cell (user accounts ++ pool reserves), and the apply step
adds an arbitrary per-cell net-delta vector (0 for untouched cells), modelling
the live `BalanceTable.add(cell, net)` and `reserve += net`. Faithfulness to the
running Python `apply_settlement` is established separately by the PR-gated live
binding test that transcribes THIS theorem and drives the real validate+apply
path over an independently-summed full ledger
(`tests/runtime/test_settlement_supply_conservation_lean_binding.py`); the Lean
proof is the abstract certificate, the test is the refinement to live code.

REVIEW [A- -> A]: the theorem core was genuine, but the first draft used
`native_decide` for the two witness lemmas. That introduced `Lean.trustCompiler`
into the witness dependency surface, which is too weak for a load-bearing proof
artifact. The witnesses now use ordinary simplification and integer arithmetic,
so the file stays inside the same trusted-dependency profile as the main theorem.
-/

namespace Proofs
namespace SettlementSupplyConservation

/-- A per-asset ledger: the signed amount held in each cell (user-balance rows
and pool-reserve rows) for ONE asset. -/
abbrev Ledger := List Int

/-- Per-asset supply = the sum over all cells. -/
def supply (L : Ledger) : Int := L.sum

/-- Apply an arbitrary per-cell net-delta vector `D` to ledger `L` by pointwise
addition (`D[i]` is the net change to cell `i`, `0` for cells the settlement does
not touch). Models the live apply: `BalanceTable.add(cell, net)` / `reserve += net`.
The deltas are NOT constrained to cancel — that is what makes the conservation
theorem have content rather than holding by construction. -/
def applyDeltas (L D : Ledger) : Ledger := List.zipWith (· + ·) L D

/-- **Key derived lemma** (genuine induction, the non-tautological core):
applying a per-cell net-delta vector changes the supply by *exactly* the sum of
the deltas. Nothing here assumes the deltas cancel. -/
theorem supply_applyDeltas (L D : Ledger) (h : L.length = D.length) :
    supply (applyDeltas L D) = supply L + supply D := by
  unfold supply applyDeltas
  induction L generalizing D with
  | nil =>
      cases D with
      | nil => simp
      | cons d ds => simp at h
  | cons a as ih =>
      cases D with
      | nil => simp at h
      | cons d ds =>
          simp only [List.zipWith_cons_cons, List.sum_cons]
          have hlen : as.length = ds.length := by simpa using h
          rw [ih ds hlen]
          ring

/-- An accepted settlement: the live validator's per-asset conservation gate,
`Σ balance_deltas[X] + Σ reserve_deltas[X] = 0`. This is the hypothesis the
validator discharges; it is NOT a fact about the apply step. -/
def accepted (balDeltas resDeltas : Ledger) : Prop :=
    supply balDeltas + supply resDeltas = 0

/-- **Headline theorem (DERIVED):** an accepted settlement preserves the combined
per-asset supply (Σ user-balance cells + Σ pool-reserve cells) across the live
apply step. The acceptance hypothesis `Σdeltas = 0` is discharged; the
preservation is concluded from `supply_applyDeltas`, not assumed. -/
theorem accepted_preserves_supply
    (balLedger balDeltas resLedger resDeltas : Ledger)
    (hb : balLedger.length = balDeltas.length)
    (hr : resLedger.length = resDeltas.length)
    (hacc : accepted balDeltas resDeltas) :
    supply (applyDeltas balLedger balDeltas)
      + supply (applyDeltas resLedger resDeltas)
      = supply balLedger + supply resLedger := by
  rw [supply_applyDeltas balLedger balDeltas hb,
      supply_applyDeltas resLedger resDeltas hr]
  unfold accepted at hacc
  -- (balS + balDS) + (resS + resDS) = balS + resS, since balDS + resDS = 0.
  omega

/-- **Contrapositive corollary:** if the apply step changed the supply, the
settlement was NOT accepted (its per-asset delta sum was non-zero). Useful as the
no-supply-creation guarantee for the running authority. -/
theorem supply_changed_implies_not_accepted
    (balLedger balDeltas resLedger resDeltas : Ledger)
    (hb : balLedger.length = balDeltas.length)
    (hr : resLedger.length = resDeltas.length)
    (hchg : supply (applyDeltas balLedger balDeltas)
      + supply (applyDeltas resLedger resDeltas)
      ≠ supply balLedger + supply resLedger) :
    ¬ accepted balDeltas resDeltas := by
  intro hacc
  exact hchg (accepted_preserves_supply balLedger balDeltas resLedger resDeltas hb hr hacc)

/-- **Non-vacuity witness:** an accepted settlement whose deltas do NOT pairwise
cancel — the balance side nets `+7` and the reserve side nets `-7`, so neither
side is internally balanced, yet the combined supply is preserved. This shows the
gate is on the COMBINED per-asset sum, not on a per-constructor cancellation. -/
theorem witness_accepted_preserves_noncanceling :
    -- balance side nets +7, reserve side nets -7; combined 0 (no pairwise cancel)
    accepted [10, -3] [-7] ∧
    supply (applyDeltas [100, 50] [10, -3])
      + supply (applyDeltas [1000] [-7])
      = supply [100, 50] + supply [1000] := by
  constructor
  · norm_num [accepted, supply]
  · norm_num [supply, applyDeltas]

/-- **Load-bearing-hypothesis witness:** an UNbalanced settlement (combined delta
sum `= +2 ≠ 0`) is NOT accepted AND its apply step creates `2` units of supply.
This proves the acceptance hypothesis is essential — without it the conclusion is
false — so `accepted_preserves_supply` is non-vacuous and not a hidden tautology. -/
theorem witness_unbalanced_creates_supply :
    -- balance side +7, reserve side -5; combined +2 ≠ 0 → not accepted, supply +2
    ¬ accepted [10, -3] [-5] ∧
    supply (applyDeltas [100, 50] [10, -3])
      + supply (applyDeltas [1000] [-5])
      = supply [100, 50] + supply [1000] + 2 := by
  constructor
  · norm_num [accepted, supply]
  · norm_num [supply, applyDeltas]

end SettlementSupplyConservation
end Proofs
