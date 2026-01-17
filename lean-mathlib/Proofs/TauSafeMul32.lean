import Mathlib.Data.Nat.Basic

/-!
Tau safe-range multiplication lemma (Mathlib).

Tau bitvector arithmetic is modular. For a bv[32] product check like:

  (rin2 * rout2) ≥ (rin * rout)

to be sound, we need a sufficient condition ensuring no overflow occurs in either product.

The TauSwap v4 swap specs enforce the conservative safe-range:
  x ≤ 65535 (0xFFFF)

Then `x*y < 2^32`, so `(x*y) mod 2^32 = x*y` and modular multiplication agrees with ℕ multiplication.

This file proves the core arithmetic bound used by that argument.
-/

namespace TauSwap
namespace TauSafe

def MAX_SAFE16 : Nat := 65535

def MOD32 : Nat := 2 ^ 32

theorem mul_lt_2pow32_of_le_ffff {a b : Nat} (ha : a ≤ MAX_SAFE16) (hb : b ≤ MAX_SAFE16) :
    a * b < MOD32 := by
  -- Monotone bound: a*b ≤ MAX_SAFE16*MAX_SAFE16, then close the goal with a constant inequality.
  have hab_le : a * b ≤ MAX_SAFE16 * MAX_SAFE16 := Nat.mul_le_mul ha hb
  have hconst : MAX_SAFE16 * MAX_SAFE16 < MOD32 := by
    -- This is a pure numeral inequality: (65535^2) < 2^32.
    dsimp [MAX_SAFE16, MOD32]
    decide
  exact lt_of_le_of_lt hab_le hconst

theorem mod32_eq_of_lt {n : Nat} (hn : n < MOD32) : n % MOD32 = n := by
  exact Nat.mod_eq_of_lt hn

theorem safe_mul_mod32_eq {a b : Nat} (ha : a ≤ MAX_SAFE16) (hb : b ≤ MAX_SAFE16) :
    (a * b) % MOD32 = a * b := by
  exact mod32_eq_of_lt (mul_lt_2pow32_of_le_ffff ha hb)

end TauSafe
end TauSwap

