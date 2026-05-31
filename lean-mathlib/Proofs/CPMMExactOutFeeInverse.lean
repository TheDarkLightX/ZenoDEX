/-!
# CPMM Exact-Out Fee Inversion, Bounded Runtime Slice

This file pins the finite arithmetic slice used by the runtime CPMM exact-out
grid. The running exact-out code computes:

```text
gross_in = ceil(net_in_required * 10000 / (10000 - fee_bps))
fee_paid = ceil(gross_in * fee_bps / 10000)
net_in_actual = gross_in - fee_paid
```

For the bounded slice below, `net_in_actual = net_in_required`.
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

end CPMMExactOutFeeInverse
end Proofs
