import Proofs.ZenoDEXExactOutManyPoolStructuralRecursionReachability

open scoped Classical BigOperators

/-!
# Exact-Out Many-Pool Selected-Domain Emission Bridge

This file proves the next honest selected-domain generator bridge after
structural reachability.

It does not claim global pool-prefilter completeness. It also does not prove
that `quote_in` succeeds for every leg. Instead, it proves:

```text
Feasible(cap,maxLegs,alloc) ∧ QuoteSuccessFor(quoteIn, supportLegs alloc)
  -> EmittedByGenerator(quoteIn, cap, Q, supportLegs alloc)
```

Plain reading: any feasible bounded selected-domain allocation whose positive
support legs all quote successfully is emitted by the modeled recursive
selected-domain generator.
-/

namespace TauSwap
namespace ZenoDEX
namespace ExactOutManyPoolSelectedDomainEmissionBridge

open ExactOutManyPoolSelectedDomainCompleteness
open ExactOutManyPoolSupportPresentation
open ExactOutManyPoolStructuralRecursionReachability

/-- Every leg in a support presentation has a successful quote under the
abstract quote oracle. `quoteIn pool amount = some amountIn` models the runtime
`quote_in(pool_id, amount_out)` side condition in
`build_exact_out_many_pool_selected_domain`. -/
def QuoteSuccessFor {n : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (legs : List (Fin n × ℕ)) : Prop :=
  ∀ leg, leg ∈ legs → ∃ amountIn, quoteIn leg.1 leg.2 = some amountIn

/-- Recursive generator emission relation for a quoted support path. It mirrors
the proof-relevant part of the Python recursion:

- `[]` emits exactly target `0`;
- `head :: tail` emits target `Q` when the head amount is in the concrete branch
  interval, the head quote succeeds, and the tail emits the residual target.
-/
inductive EmittedByGenerator {n : ℕ}
    (quoteIn : Fin n → ℕ → Option ℕ)
    (cap : Fin n → ℕ) : ℕ → List (Fin n × ℕ) → Prop where
  | nil :
      EmittedByGenerator quoteIn cap 0 []
  | cons
      {Q : ℕ}
      {head : Fin n × ℕ}
      {tail : List (Fin n × ℕ)}
      {amountIn : ℕ}
      (hLower : max 1 (Q - ExactOutManyPoolRemainingCapacityTopSum.remainingCapacityTopSum cap head.1 tail.length) ≤ head.2)
      (hUpper : head.2 ≤ min (cap head.1) Q)
      (hQuote : quoteIn head.1 head.2 = some amountIn)
      (hTail : EmittedByGenerator quoteIn cap (Q - head.2) tail) :
      EmittedByGenerator quoteIn cap Q (head :: tail)

/-- Structural reachability plus per-leg quote success gives generator emission.
This is the direct bridge from range-only reachability to quoted emission. -/
theorem emittedByGenerator_of_structurallyReachable_of_quoteSuccess
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {legs : List (Fin n × ℕ)}
    (hReach : StructurallyReachable cap Q legs)
    (hQuoteSuccess : QuoteSuccessFor quoteIn legs) :
    EmittedByGenerator quoteIn cap Q legs := by
  induction hReach with
  | nil =>
      exact EmittedByGenerator.nil
  | cons hLower hUpper _hTail ih =>
      rcases hQuoteSuccess _ (List.Mem.head _) with ⟨_amountIn, hQuote⟩
      exact EmittedByGenerator.cons hLower hUpper hQuote
        (ih (fun leg hMem => hQuoteSuccess leg (List.Mem.tail _ hMem)))

/-- Feasible bounded allocations are emitted by the modeled selected-domain
recursive generator, provided the quote oracle succeeds on every positive
support leg. -/
theorem feasible_support_emittedByGenerator_of_quoteSuccess
    {n Q : ℕ}
    {quoteIn : Fin n → ℕ → Option ℕ}
    {cap : Fin n → ℕ}
    {maxLegs : ℕ}
    {alloc : Alloc n Q}
    (hFeas : Feasible cap maxLegs alloc)
    (hQuoteSuccess : QuoteSuccessFor quoteIn (supportLegs alloc)) :
    EmittedByGenerator quoteIn cap Q (supportLegs alloc) := by
  exact emittedByGenerator_of_structurallyReachable_of_quoteSuccess
    (hReach := feasible_supportLegs_structurallyReachable (cap := cap) hFeas)
    hQuoteSuccess

end ExactOutManyPoolSelectedDomainEmissionBridge
end ZenoDEX
end TauSwap
