import Proofs.CPMMInvariants
import Mathlib.Tactic

/-!
Fee ceil-division decomposition lemma.

This is the algebra behind the overflow-safer fee computation:

  ceil(gross * fee / 10000)
    = (gross / 10000) * fee + ceil((gross % 10000) * fee / 10000)

It is useful when translating kernels to fixed-width arithmetic environments
because it reduces the size of intermediate products.
-/

namespace CPMMInvariants

theorem computeFee_decomposed (gross fee_bps : ℕ) :
    computeFee gross fee_bps =
      (gross / 10000) * fee_bps + computeFee (gross % 10000) fee_bps := by
  -- Unfold the definition: computeFee amount fee_bps = ceilDiv (amount*fee_bps) 10000.
  simp [computeFee, ceilDiv]

  have hpos : 0 < (10000 : ℕ) := by decide
  have hdiv : (10000 : ℕ) * (gross / 10000) + gross % 10000 = gross := Nat.div_add_mod gross 10000

  -- Rewrite the LHS using Euclidean division of `gross` and then split the divisible part.
  calc
    (gross * fee_bps + (10000 - 1)) / 10000
        = (((((10000 : ℕ) * (gross / 10000) + gross % 10000) * fee_bps)) + (10000 - 1)) / 10000 := by
              -- Only rewrite the LHS occurrence of `gross` to avoid blowing up the RHS
              -- (`gross` also appears inside `gross / 10000` and `gross % 10000` there).
              conv_lhs => rw [hdiv.symm]
    _ = ((((10000 : ℕ) * ((gross / 10000) * fee_bps)) + ((gross % 10000) * fee_bps)) + (10000 - 1)) / 10000 := by
              -- Expand (a+b)*c and reassociate.
              simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
    _ = ((((gross % 10000) * fee_bps + (10000 - 1)) + (10000 : ℕ) * ((gross / 10000) * fee_bps)) / 10000) := by
              -- Commute/associate to match `x + 10000*y`.
              ac_rfl
    _ = ((gross % 10000) * fee_bps + (10000 - 1)) / 10000 + (gross / 10000) * fee_bps := by
              -- (x + n*y)/n = x/n + y
              simpa using
                (Nat.add_mul_div_left ((gross % 10000) * fee_bps + (10000 - 1)) ((gross / 10000) * fee_bps) hpos)
    _ = (gross / 10000) * fee_bps + (((gross % 10000) * fee_bps + (10000 - 1)) / 10000) := by
              ac_rfl

end CPMMInvariants
