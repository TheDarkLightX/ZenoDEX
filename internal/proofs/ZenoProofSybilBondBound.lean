import Mathlib

/-!
# ZenoProof Sybil Bond Bound (Internal Exploration)

INTERNAL ONLY. This file lives under `internal/proofs/` and is NOT part of the
main `lean-mathlib/Proofs/` library. It addresses hypothesis card `H-MD-007`
(split/merge neutrality / Sybil resistance) by quantifying the identity bond
required to make a 2-atom split strictly unprofitable under equal-split reward
allocation.

## Motivation

Standard Shapley value is *not* split-proof. Equal-split allocation is also
not split-proof: if a player splits into 2 identities while the total pool of
identities grows from `n` to `n + 1`, the combined payment after split is
`2V / (n + 1)` while the pre-split payment was `V / n`. The gross gain is
`V · (n - 1) / (n · (n + 1))`. For `n ≥ 2` this is strictly positive, so
splitting is gross-profitable.

The protocol fix is a non-refundable identity bond `B` charged per registered
identity. To register a Sybil split, the attacker must pay one additional bond.
Splitting is net-unprofitable iff the gross gain is dominated by the bond.

## Main Result

Equal-split reward `V` among `n + 1` identities (one of whom is a 2-atom Sybil
from an original cohort of `n`) is **net Sybil-unprofitable** iff:

```text
V · (n - 1) ≤ B · n · (n + 1)
```

Plain reading: the bond `B`, multiplied by the post-split denominator, must
dominate the gross Sybil gain numerator.

Cross-multiplied form avoids `Real` and integer floor.

## Scope

Two-atom split only. The k-atom generalization is sketched at the bottom of
this file. ESSO refinement (runtime enforcement of bond at identity registration)
is out of scope here.
-/

namespace Internal
namespace ZenoProofSybilBondBound

/-- Pre-split equal-split payment to the original player (out of `n` total
identities, total pool `V`). Returned scaled by `n` to avoid division. -/
def preSplitPaymentScaled (V _n : Nat) : Nat := V

/-- Post-split combined payment to the 2-atom Sybil (out of `n + 1` total
identities, total pool `V`). Returned scaled by `(n + 1)` to avoid division;
the actual combined payment is `2V / (n + 1)`. -/
def postSplitPaymentScaled (V : Nat) (_n : Nat) : Nat := 2 * V

/-- Cross-multiplied net Sybil profit (scaled by `n · (n + 1)`):

```text
net = postSplitScaled · n - preSplitScaled · (n + 1) - B · n · (n + 1)
    = 2V · n - V · (n + 1) - B · n · (n + 1)
```

In Nat arithmetic we keep a `≤` form to avoid negative numbers. -/
def sybilUnprofitable (V B n : Nat) : Prop :=
  2 * V * n ≤ V * (n + 1) + B * n * (n + 1)

/-- **Bond Bound Theorem.**

Equivalent forms of Sybil-unprofitability under equal-split allocation.

The right-hand form is the *protocol design rule*: choose bond `B` so that
`V · (n - 1) ≤ B · n · (n + 1)` for the smallest expected cohort `n`. -/
theorem sybil_unprofitable_iff_bond_dominates
    (V B n : Nat) (hn : 1 ≤ n) :
    sybilUnprofitable V B n ↔ V * (n - 1) ≤ B * n * (n + 1) := by
  unfold sybilUnprofitable
  have hnSucc : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  constructor
  · intro h
    -- 2Vn ≤ V(n+1) + Bn(n+1)
    -- ⇒ 2Vn - V(n+1) ≤ Bn(n+1)
    -- ⇒ V(2n - n - 1) ≤ Bn(n+1)
    -- ⇒ V(n - 1) ≤ Bn(n+1)
    have hExpand : V * (n + 1) = V * n + V := by ring
    have hMul2 : 2 * V * n = V * n + V * n := by ring
    have hMain : V * n + V * n ≤ V * n + V + B * n * (n + 1) := by
      have := h
      rw [hMul2, hExpand] at this
      exact this
    have hCancel : V * n ≤ V + B * n * (n + 1) := by omega
    -- Now V × n ≤ V + B × n × (n+1).
    -- Rewrite V × n = V × (n - 1) + V (using hnSucc):
    have hRewriteVn : V * n = V * (n - 1) + V := by
      conv_lhs => rw [hnSucc]
      ring
    rw [hRewriteVn] at hCancel
    omega
  · intro h
    -- V(n - 1) ≤ Bn(n+1)
    -- ⇒ V × (n + 1) + Bn(n+1) ≥ V × (n + 1) + V × (n - 1)
    --                       = V × ((n + 1) + (n - 1))
    --                       = V × (2n)
    --                       = 2Vn
    have hRewrite : V * (n + 1) + V * (n - 1) = 2 * V * n := by
      have : V * (n + 1) + V * (n - 1) = V * ((n + 1) + (n - 1)) := by ring
      rw [this]
      have hsum : (n + 1) + (n - 1) = 2 * n := by omega
      rw [hsum]
      ring
    omega

/-! ## Non-Vacuity Witnesses -/

/-- Witness: with `V = 100`, `n = 4` (so `n - 1 = 3` and `n · (n + 1) = 20`),
the minimal Sybil-blocking bond satisfies `B ≥ 3 · 100 / 20 = 15`. Take `B = 15`. -/
theorem witness_bond_blocks_sybil :
    sybilUnprofitable 100 15 4 := by
  unfold sybilUnprofitable
  decide

/-- Witness: a deficient bond `B = 10` (below the threshold of 15) leaves
Sybil profitable. The protocol must reject this configuration. -/
theorem witness_deficient_bond_admits_sybil :
    ¬ sybilUnprofitable 100 10 4 := by
  unfold sybilUnprofitable
  decide

/-- Witness: at the boundary `B = 15` the Sybil profit reaches zero exactly.
Larger bonds are strictly Sybil-unprofitable. -/
theorem witness_bond_above_threshold_is_strict :
    2 * 100 * 4 < 100 * (4 + 1) + 16 * 4 * (4 + 1) := by
  decide

/-! ## k-Atom Generalization (Sketch)

For a k-atom Sybil split, the bond cost is `(k - 1) · B` and the post-split
combined payment is `k · V / (n + k - 1)`. The unprofitability condition
generalizes to:

```text
V · ((k - 1) · n - (k - 1)) ≤ (k - 1) · B · n · (n + k - 1)
↔ V · (n - 1) ≤ B · n · (n + k - 1)
```

Plain reading: the bound is independent of `k - 1` (which cancels), but the
denominator grows in `k`. Larger splits are *less* profitable per unit of bond
because the post-split denominator grows. So the bond `B` sized for `k = 2`
covers all larger splits too. This is a strong protocol property: one threshold
covers all Sybil cardinalities under equal-split allocation.

A formal Lean proof of this generalization is left as a follow-up theorem.
The two-atom result above is the binding case.
-/

end ZenoProofSybilBondBound
end Internal
