import Mathlib.Tactic

/-!
# Live Settlement Conservation

This file captures the linear conservation obligation shared by the live spot
settlement action classes:

```text
balance_delta(asset) + reserve_delta(asset) = 0
```

The model intentionally ignores CPMM output arithmetic, LP mint/burn arithmetic,
and non-negativity. Those obligations are proved or tested elsewhere. This file
proves the smaller balance-surface fact used by the live settlement authority
path: exact-in/out swaps, pool creation, add-liquidity, and remove-liquidity
move each asset between user balances and pool reserves without creating or
destroying that asset.

REVIEW [new -> A-]: this is a clean linear proof for the right action classes,
but it is still an abstract model. The balances proof_artifact row should stay
false until a receipt binds these constructors to the Python settlement deltas.
-/

namespace Proofs
namespace SettlementConservationLive

/-- One per-asset live settlement move.

Each constructor models one asset side of the live settlement replay:

* `swapInput amount protocolFee`: the trader spends `amount`; the protocol-fee
  recipient, if any, is an ordinary balance-row recipient for `protocolFee`; the
  pool reserve receives `amount - protocolFee`.
* `swapOutput amountOut`: the trader receives `amountOut`; the pool reserve
  releases the same asset amount.
* `createPool amount`, `addLiquidity amount`, and `removeLiquidity amount`
  model the corresponding reserve/user transfer for one asset.
-/
inductive AssetMove where
  | swapInput (amount protocolFee : Int)
  | swapOutput (amountOut : Int)
  | createPool (amount : Int)
  | addLiquidity (amountUsed : Int)
  | removeLiquidity (amountOut : Int)
  deriving Repr, DecidableEq

/-- Net change in all user balance rows for this asset. -/
def balanceDelta : AssetMove → Int
  | .swapInput amount protocolFee => -amount + protocolFee
  | .swapOutput amountOut => amountOut
  | .createPool amount => -amount
  | .addLiquidity amountUsed => -amountUsed
  | .removeLiquidity amountOut => amountOut

/-- Net change in all pool reserve rows for this asset. -/
def reserveDelta : AssetMove → Int
  | .swapInput amount protocolFee => amount - protocolFee
  | .swapOutput amountOut => -amountOut
  | .createPool amount => amount
  | .addLiquidity amountUsed => amountUsed
  | .removeLiquidity amountOut => -amountOut

/-- The authority-path conservation measure for one asset. -/
def totalDelta (move : AssetMove) : Int :=
  balanceDelta move + reserveDelta move

/-- Every modeled live settlement move conserves the asset exactly. -/
theorem assetMove_totalDelta_zero (move : AssetMove) :
    totalDelta move = 0 := by
  cases move <;> simp [totalDelta, balanceDelta, reserveDelta]

/-- Applying one move preserves the combined `{balances + reserves}` total. -/
def applyMove (state : Int × Int) (move : AssetMove) : Int × Int :=
  (state.1 + balanceDelta move, state.2 + reserveDelta move)

theorem applyMove_preserves_total (state : Int × Int) (move : AssetMove) :
    (applyMove state move).1 + (applyMove state move).2 = state.1 + state.2 := by
  cases move <;> simp [applyMove, balanceDelta, reserveDelta] <;> omega

/-- Sequential application of per-asset moves. -/
def applyMoves (state : Int × Int) (moves : List AssetMove) : Int × Int :=
  moves.foldl applyMove state

/-- A whole live settlement batch preserves the combined per-asset total. -/
theorem applyMoves_preserves_total (moves : List AssetMove) (state : Int × Int) :
    (applyMoves state moves).1 + (applyMoves state moves).2 = state.1 + state.2 := by
  induction moves generalizing state with
  | nil =>
      simp [applyMoves]
  | cons move rest ih =>
      simp [applyMoves, List.foldl_cons]
      calc
        (applyMoves (applyMove state move) rest).1 +
            (applyMoves (applyMove state move) rest).2
            = (applyMove state move).1 + (applyMove state move).2 := ih (applyMove state move)
        _ = state.1 + state.2 := applyMove_preserves_total state move

/-- Equivalent list-sum statement used by receipt checkers and smoke imports. -/
theorem list_totalDelta_sum_zero (moves : List AssetMove) :
    (moves.map totalDelta).sum = 0 := by
  induction moves with
  | nil =>
      simp
  | cons move rest ih =>
      simp [assetMove_totalDelta_zero move, ih]

/-- Concrete non-vacuity witness: a mixed live batch has zero net asset creation. -/
theorem witness_mixed_live_batch :
    ([
      AssetMove.createPool 2_000_000,
      AssetMove.swapInput 1_000 3,
      AssetMove.swapOutput 996,
      AssetMove.addLiquidity 100_000,
      AssetMove.removeLiquidity 1_000
    ].map totalDelta).sum = 0 := by
  decide

end SettlementConservationLive
end Proofs
