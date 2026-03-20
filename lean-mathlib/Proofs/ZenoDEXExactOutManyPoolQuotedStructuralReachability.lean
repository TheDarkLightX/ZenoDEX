import Proofs.ZenoDEXExactOutManyPoolStructuralRecursionReachability

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolQuotedStructuralReachability

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolStructuralRecursionReachability

/-!
# Exact-Out Many-Pool Quoted Structural Reachability

This file isolates the concrete `quote_in` side condition from the already
proved structural recursion theorem.

The theorem proved here is intentionally conditional:

- if the leg quote oracle succeeds with a positive `amount_in` for every
  positive bounded `amount_out`,
- then every structurally reachable support split lifts to a quoted recursive
  path carrying concrete per-leg inputs.

This is the strongest honest local bridge before proving that the shipped
runtime's exact-out quote function is total on the audited bounded domain.
-/

structure QuotedLeg (n : ℕ) where
  poolIdx : Fin n
  amountOut : ℕ
  amountIn : ℕ
deriving DecidableEq, Repr

def supportOfQuotedLegs {n : ℕ} (legs : List (QuotedLeg n)) : List (Fin n × ℕ) :=
  legs.map fun leg => (leg.poolIdx, leg.amountOut)

def QuoteTotalOnPositiveBounded {n : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ) : Prop :=
  ∀ i amountOut, 0 < amountOut → amountOut ≤ cap i →
    ∃ amountIn, 0 < amountIn ∧ quoteIn i amountOut = some amountIn

inductive QuotedStructurallyReachable
    {n : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ) : ℕ → List (QuotedLeg n) → Prop where
  | nil :
      QuotedStructurallyReachable quoteIn cap 0 []
  | cons
      {Q : ℕ}
      {head : QuotedLeg n}
      {tail : List (QuotedLeg n)}
      (hLower :
        max 1 (Q - ExactOutManyPoolRemainingCapacityTopSum.remainingCapacityTopSum cap head.poolIdx tail.length) ≤
          head.amountOut)
      (hUpper : head.amountOut ≤ min (cap head.poolIdx) Q)
      (hQuote : quoteIn head.poolIdx head.amountOut = some head.amountIn)
      (hTail : QuotedStructurallyReachable quoteIn cap (Q - head.amountOut) tail) :
      QuotedStructurallyReachable quoteIn cap Q (head :: tail)

theorem supportOfQuotedLegs_nil {n : ℕ} :
    supportOfQuotedLegs ([] : List (QuotedLeg n)) = [] := by
  rfl

theorem supportOfQuotedLegs_cons {n : ℕ}
    (head : QuotedLeg n)
    (tail : List (QuotedLeg n)) :
    supportOfQuotedLegs (head :: tail) =
      (head.poolIdx, head.amountOut) :: supportOfQuotedLegs tail := by
  rfl

theorem structurallyReachable_of_quoted
    {n : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {Q : ℕ}
    {legs : List (QuotedLeg n)}
    (hQuoted : QuotedStructurallyReachable quoteIn cap Q legs) :
    StructurallyReachable cap Q (supportOfQuotedLegs legs) := by
  induction hQuoted with
  | nil =>
      simpa [supportOfQuotedLegs_nil] using (StructurallyReachable.nil (cap := cap))
  | @cons Q head tail hLower hUpper _hQuote hTail ih =>
      have hLower' :
          max 1
              (Q -
                ExactOutManyPoolRemainingCapacityTopSum.remainingCapacityTopSum cap
                  (head.poolIdx, head.amountOut).1
                  (supportOfQuotedLegs tail).length) ≤
            (head.poolIdx, head.amountOut).2 := by
        simpa [supportOfQuotedLegs, List.length_map] using hLower
      have hUpper' :
          (head.poolIdx, head.amountOut).2 ≤
            min (cap (head.poolIdx, head.amountOut).1) Q := by
        simpa using hUpper
      exact StructurallyReachable.cons hLower' hUpper' ih

theorem quoted_of_structurallyReachable
    {n : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap) :
    ∀ {Q : ℕ} {legs : List (Fin n × ℕ)},
      StructurallyReachable cap Q legs →
      ∃ quotedLegs,
        supportOfQuotedLegs quotedLegs = legs ∧
        QuotedStructurallyReachable quoteIn cap Q quotedLegs
  | _, _, StructurallyReachable.nil => by
      exact ⟨[], rfl, QuotedStructurallyReachable.nil⟩
  | Q, head :: tail, StructurallyReachable.cons hLower hUpper hTail => by
      have hPos : 0 < head.2 := by
        exact lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_left _ _) hLower)
      have hCap : head.2 ≤ cap head.1 := by
        exact le_trans hUpper (min_le_left _ _)
      rcases hQuoteTotal head.1 head.2 hPos hCap with ⟨amountIn, _hInPos, hQuote⟩
      rcases quoted_of_structurallyReachable
          (quoteIn := quoteIn) (cap := cap) hQuoteTotal hTail with
        ⟨quotedTail, hTailSupport, hTailQuoted⟩
      have hTailLen : quotedTail.length = tail.length := by
        simpa [supportOfQuotedLegs] using congrArg List.length hTailSupport
      let quotedHead : QuotedLeg n := {
        poolIdx := head.1
        amountOut := head.2
        amountIn := amountIn
      }
      have hLowerQuoted :
          max 1
              (Q -
                ExactOutManyPoolRemainingCapacityTopSum.remainingCapacityTopSum cap
                  quotedHead.poolIdx quotedTail.length) ≤
            quotedHead.amountOut := by
        simpa [quotedHead, hTailLen] using hLower
      have hUpperQuoted :
          quotedHead.amountOut ≤ min (cap quotedHead.poolIdx) Q := by
        simpa [quotedHead] using hUpper
      exact ⟨
        quotedHead :: quotedTail,
        by
          simpa [supportOfQuotedLegs, quotedHead] using
            congrArg (List.cons (head.1, head.2)) hTailSupport,
        QuotedStructurallyReachable.cons hLowerQuoted hUpperQuoted hQuote hTailQuoted
      ⟩

theorem quoted_of_feasible_supportLegs
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ} {maxLegs : ℕ}
    {alloc : Alloc n Q}
    (hQuoteTotal : QuoteTotalOnPositiveBounded quoteIn cap)
    (hFeas : Feasible cap maxLegs alloc) :
    ∃ quotedLegs,
      supportOfQuotedLegs quotedLegs = supportLegs alloc ∧
      QuotedStructurallyReachable quoteIn cap Q quotedLegs := by
  exact quoted_of_structurallyReachable hQuoteTotal
    (feasible_supportLegs_structurallyReachable hFeas)

end ExactOutManyPoolQuotedStructuralReachability
end ZenoDEX
end TauSwap
