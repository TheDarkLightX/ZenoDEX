/-!
# CPMM Exact-Swap Arithmetic, Bounded Runtime Slice

This file pins the finite arithmetic slice used by the runtime CPMM exact-out
grid. The running exact-out code computes:

```text
gross_in = ceil(net_in_required * 10000 / (10000 - fee_bps))
fee_paid = ceil(gross_in * fee_bps / 10000)
net_in_actual = gross_in - fee_paid
```

For the bounded fee-inversion slice below, `net_in_actual = net_in_required`.
The file also mirrors the exact-in and exact-out small-domain arithmetic grids
used by the runtime tests and checks accepted-case safety properties.
-/

namespace Proofs
namespace CPMMExactOutFeeInverse

def bpsDenom : Nat := 10000

def ceilDiv (num den : Nat) : Nat :=
  (num + den - 1) / den

def exactOutFeeInverseCase (netIn feeBps : Nat) : Bool :=
  let feeDen := bpsDenom - feeBps
  let grossIn := ceilDiv (netIn * bpsDenom) feeDen
  let feePaid := ceilDiv (grossIn * feeBps) bpsDenom
  grossIn - feePaid == netIn

def exactOutFeeInverseBounded (maxNetIn : Nat) : Bool :=
  (List.range maxNetIn).all fun offset =>
    let netIn := offset + 1
    (List.range bpsDenom).all fun feeBps =>
      exactOutFeeInverseCase netIn feeBps

def feeTierGrid : List Nat :=
  [0, 1, 30, 5000, 9999, bpsDenom]

def exactInAcceptedSafetyCase
    (reserveIn reserveOut amountIn feeBps : Nat) : Bool :=
  let feePaid := ceilDiv (amountIn * feeBps) bpsDenom
  if feePaid < amountIn then
    let netIn := amountIn - feePaid
    let amountOut := (reserveOut * netIn) / (reserveIn + netIn)
    if 0 < amountOut then
      let newIn := reserveIn + amountIn
      let newOut := reserveOut - amountOut
      decide (reserveIn * reserveOut ≤ newIn * newOut) &&
        decide (newIn = reserveIn + amountIn) &&
        decide (newOut = reserveOut - amountOut) &&
        decide (amountOut ≤ reserveOut)
    else
      true
  else
    true

def exactOutAcceptedSafetyCase
    (reserveIn reserveOut amountOut feeBps maxGapBps : Nat) : Bool :=
  if reserveOut ≤ amountOut then
    true
  else if feeBps == bpsDenom then
    true
  else
    let reserveDelta := reserveOut - amountOut
    let feeDen := bpsDenom - feeBps
    let netInRequired := ceilDiv (reserveIn * amountOut) reserveDelta
    let grossIn := ceilDiv (netInRequired * bpsDenom) feeDen
    let feePaid := ceilDiv (grossIn * feeBps) bpsDenom
    let netInActual := grossIn - feePaid
    let amountOutQuote := (reserveOut * netInActual) / (reserveIn + netInActual)
    let overdeliveryGap := amountOutQuote - amountOut
    let gapBps := ceilDiv (overdeliveryGap * bpsDenom) amountOut
    if maxGapBps < gapBps then
      true
    else
      let newIn := reserveIn + grossIn
      let newOut := reserveOut - amountOut
      decide (amountOut ≤ amountOutQuote) &&
        decide (reserveIn * reserveOut ≤ newIn * newOut) &&
        decide (newIn = reserveIn + grossIn) &&
        decide (newOut = reserveOut - amountOut) &&
        decide (newOut < reserveOut)

def exactInSmallDomainSafetyGrid : Bool :=
  (List.range 12).all fun reserveInOffset =>
    let reserveIn := reserveInOffset + 1
    (List.range 12).all fun reserveOutOffset =>
      let reserveOut := reserveOutOffset + 1
      (List.range 12).all fun amountInOffset =>
        let amountIn := amountInOffset + 1
        feeTierGrid.all fun feeBps =>
          exactInAcceptedSafetyCase reserveIn reserveOut amountIn feeBps

def exactOutSmallDomainSafetyGrid : Bool :=
  (List.range 12).all fun reserveInOffset =>
    let reserveIn := reserveInOffset + 1
    (List.range 11).all fun reserveOutOffset =>
      let reserveOut := reserveOutOffset + 2
      (List.range (reserveOut - 1)).all fun amountOutOffset =>
        let amountOut := amountOutOffset + 1
        feeTierGrid.all fun feeBps =>
          exactOutAcceptedSafetyCase reserveIn reserveOut amountOut feeBps bpsDenom

/--
Bounded Lean mirror of the runtime/Z3 exact-out fee-inversion check:
for every `1 <= net_in <= 200` and every `0 <= fee_bps < 10000`, the gross
input computed by the exact-out formula leaves exactly the required net input
after applying the runtime's ceil-rounded fee.
-/
theorem exactOutFeeInverseBounded_200 :
    exactOutFeeInverseBounded 200 = true := by
  native_decide

theorem exactOutFeeInverseWitness :
    exactOutFeeInverseCase 1 9999 = true ∧
      exactOutFeeInverseCase 200 30 = true := by
  native_decide

/--
Finite Lean mirror of the exact-in runtime grid. For reserves and gross inputs
in `1..12`, and the fee tiers `{0,1,30,5000,9999,10000}`, every formula-accepted
case preserves `k`, has the expected post-reserve shape, and never overdraws the
output reserve.
-/
theorem exactInSmallDomainSafetyGrid_true :
    exactInSmallDomainSafetyGrid = true := by
  native_decide

/--
Finite Lean mirror of the exact-out runtime grid. For `reserve_in in 1..12`,
`reserve_out in 2..12`, `amount_out in 1..reserve_out-1`, the same fee tiers,
and a permissive overdelivery cap of `10000` bps, every formula-accepted case
quotes at least the requested output, preserves `k`, and has the expected
post-reserve shape.
-/
theorem exactOutSmallDomainSafetyGrid_true :
    exactOutSmallDomainSafetyGrid = true := by
  native_decide

theorem exactSwapSafetyWitnesses :
    exactInAcceptedSafetyCase 1 2 1 0 = true ∧
      exactInAcceptedSafetyCase 12 12 12 bpsDenom = true ∧
      exactOutAcceptedSafetyCase 1 2 1 0 bpsDenom = true ∧
      exactOutAcceptedSafetyCase 12 12 11 bpsDenom bpsDenom = true := by
  native_decide

end CPMMExactOutFeeInverse
end Proofs
