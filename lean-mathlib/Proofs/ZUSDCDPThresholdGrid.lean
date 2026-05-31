/-!
# zUSD CDP Threshold Grid

This file is a small, self-contained Lean mirror of the runtime zUSD CDP
threshold grid. It pins the arithmetic shape Kani does not handle directly:

```text
MCR_OK(c,d,p,m) := d = 0 or c * p * 10000 >= d * m * 1e8
```

The checked statements are finite boundary witnesses, not a full live-domain
proof of the running zUSD transition.
-/

namespace Proofs
namespace ZUSDCDPThresholdGrid

def e8 : Nat := 100000000
def bps : Nat := 10000

def mcrOk (collateral debt price mcrBps : Nat) : Bool :=
  if debt == 0 then
    true
  else
    decide (collateral * price * bps >= debt * mcrBps * e8)

def mintAdmitsByMcr (collateral debt price mcrBps amount : Nat) : Bool :=
  mcrOk collateral (debt + amount) price mcrBps

def withdrawAdmitsByMcr (collateral debt price mcrBps amount : Nat) : Bool :=
  if amount <= collateral then
    mcrOk (collateral - amount) debt price mcrBps
  else
    false

def liquidateAdmitsByMcr (collateral debt price mcrBps : Nat) : Bool :=
  !mcrOk collateral debt price mcrBps

def redemptionGrossCollateral (amount price : Nat) : Nat :=
  amount * e8 / price

def redeemAdmitsByMcr
    (collateral debt price mcrBps amount : Nat) : Bool :=
  if debt < amount then
    false
  else
    let gross := redemptionGrossCollateral amount price
    if gross == 0 then
      false
    else if collateral < gross then
      false
    else
      mcrOk (collateral - gross) (debt - amount) price mcrBps

def cdpBoundaryGridOk : Bool :=
  mcrOk (110 * e8) (100 * e8) e8 11000 &&
  !mcrOk (110 * e8) (100 * e8 + 1) e8 11000 &&
  !mintAdmitsByMcr (110 * e8) (100 * e8) e8 11000 1 &&
  mintAdmitsByMcr (110 * e8) (100 * e8 - 1) e8 11000 1 &&
  !withdrawAdmitsByMcr (110 * e8) (100 * e8) e8 11000 1 &&
  withdrawAdmitsByMcr (110 * e8 + 1) (100 * e8) e8 11000 1 &&
  liquidateAdmitsByMcr (110 * e8) (100 * e8 + 1) e8 11000 &&
  !liquidateAdmitsByMcr (110 * e8) (100 * e8) e8 11000 &&
  !redeemAdmitsByMcr (200 * e8) (100 * e8) (2 * e8) 11000 1 &&
  redeemAdmitsByMcr (200 * e8) (100 * e8) (2 * e8) 11000 (50 * e8)

/--
Finite Lean check for the zUSD CDP boundary cases mirrored by
`tests/runtime/test_zusd_cdp_threshold_grid.py`.
-/
theorem cdpBoundaryGridOk_true : cdpBoundaryGridOk = true := by
  native_decide

theorem cdpBoundaryWitnesses :
    mcrOk (110 * e8) (100 * e8) e8 11000 = true ∧
      mcrOk (110 * e8) (100 * e8 + 1) e8 11000 = false ∧
      redemptionGrossCollateral 1 (2 * e8) = 0 := by
  native_decide

end ZUSDCDPThresholdGrid
end Proofs
