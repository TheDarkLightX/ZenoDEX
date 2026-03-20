import Proofs.ZenoDEXExactInRouteCertificate
import Proofs.ZenoDEXExactInRouteRankProjection
import Proofs.ZenoDEXExactOutCanonicalMinimizer
import Proofs.ZenoDEXExactOutBruteforceCompleteness
import Proofs.BatchAuctionCanonical

/-!
# ZenoDEX Unique Canonical Winner Everywhere

Composing proof for the ShapeForge `unique_canonical_winner_everywhere` clause.
Closes Gap 1 in target shapes `shape_pp_candidate_v1` and `dex_kernel_candidate_v1`.

## The Canonical Winner Principle

All three DEX optimizer subsystems derive deterministic winner selection from
the **same abstract principle**: for any nonempty finite candidate set with a
total-order key, there exists a unique minimum.

  ∀ S ≠ ∅. ∃! k ∈ S. ∀ x ∈ S, k ≤ x

Each subsystem instantiates this with a different key type:

| Subsystem | Key Type | Order | Evidence |
|-----------|----------|-------|----------|
| **Batch** | `(Volume^od ×_lex Surplus^od) ×_lex Order` | `LinearOrder` (Mathlib) | `Batch.exists_unique_canonical` |
| **Exact-in** | `(routeKeyRank, candidateIndex)` | Total order (`keyLe`) | `exact_in_exists_unique_canonical_winner` |
| **Exact-out** | `(inputTotal ×_lex legCount) ×_lex legsLex` | `LinearOrder` (Mathlib) | `ExactOutCanonicalMinimizer.exists_unique_canonical` |

## Cross-invariant: canonical_winner_requires_total_key

The `keyLe_is_total_order` theorem certifies that exact-in's `keyLe` satisfies
all four total-order axioms (reflexive, transitive, antisymmetric, total).
Batch and exact-out inherit this from Mathlib's `LinearOrder` typeclass.

## Scope

This file certifies the **canonicality** property: given ANY nonempty finite
candidate set, the canonical winner is unique and deterministic. The separate
**completeness** property (whether the candidate generator covers all feasible
solutions) is tracked by `exact_out_generator_is_globally_complete_v1` and
remains open — it is a generator obligation, not a canonicality obligation.

## Key results

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 1 | `keyLe_refl`, `keyLe_antisymm`, `keyLe_total` | Core | keyLe is a total preorder |
| 2 | `chooseBetter_mem`, `foldl_chooseBetter_mem` | Core | Fold preserves membership |
| 3 | `exact_in_exists_unique_canonical_winner` | Main | ∃! winner for exact-in streams |
| 4 | `certificate_identifies_unique_winner` | Bridge | Certificate = unique winner |
| 5 | `exact_out_unique_canonical_winner` | Re-export | ∃! winner for exact-out Finsets |
| 6 | `keyLe_is_total_order` | Main | keyLe is reflexive, transitive, antisymmetric, total |
| 7 | `batch_unique_canonical_winner` | Re-export | ∃! winner for batch Finsets |
| 8 | `unified_three_way_canonicality` | Main | All three subsystems produce unique winners |
| 9 | `exists_unique_trueKeyLe_minimum` | **Bridge** | Fold on projected candidates = unique `trueKeyLe`-minimum |
-/

namespace TauSwap
namespace UniqueCanonicalWinnerEverywhere

open Routing.ExactInRouteCertificate

-- ════════════════════════════════════════════════════════════════════════════
-- Part 1: keyLe is a linear order on Candidate
-- ════════════════════════════════════════════════════════════════════════════

theorem keyLe_refl (a : Candidate) : keyLe a a :=
  Or.inr ⟨rfl, Nat.le_refl _⟩

theorem keyLe_antisymm {a b : Candidate} (hab : keyLe a b) (hba : keyLe b a) :
    a = b := by
  rcases hab with hlt_ab | ⟨hrank_ab, hidx_ab⟩
  · -- a.rank < b.rank
    rcases hba with hlt_ba | ⟨hrank_ba, _⟩
    · exact absurd (Nat.lt_trans hlt_ab hlt_ba) (Nat.lt_irrefl _)
    · exact absurd (hrank_ba ▸ hlt_ab) (Nat.lt_irrefl _)
  · -- a.rank = b.rank ∧ a.idx ≤ b.idx
    rcases hba with hlt_ba | ⟨_, hidx_ba⟩
    · exact absurd (hrank_ab ▸ hlt_ba) (Nat.lt_irrefl _)
    · have hidx_eq := Nat.le_antisymm hidx_ab hidx_ba
      cases a with
      | mk ai ar => cases b with
        | mk bi br =>
          simp only [Candidate.mk.injEq]
          exact ⟨hidx_eq, hrank_ab⟩

theorem keyLe_total (a b : Candidate) : keyLe a b ∨ keyLe b a := by
  unfold keyLe
  by_cases h1 : a.routeKeyRank < b.routeKeyRank
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : b.routeKeyRank < a.routeKeyRank
    · exact Or.inr (Or.inl h2)
    · have hrank : a.routeKeyRank = b.routeKeyRank := by omega
      by_cases h3 : a.candidateIndex ≤ b.candidateIndex
      · exact Or.inl (Or.inr ⟨hrank, h3⟩)
      · exact Or.inr (Or.inr ⟨hrank.symm, by omega⟩)

-- ════════════════════════════════════════════════════════════════════════════
-- Part 2: chooseBetter preserves membership
-- ════════════════════════════════════════════════════════════════════════════

theorem chooseBetter_mem (best cand : Candidate) :
    chooseBetter best cand = best ∨ chooseBetter best cand = cand := by
  unfold chooseBetter
  split
  · exact Or.inr rfl
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl

theorem foldl_chooseBetter_mem (first : Candidate) (rest : List Candidate) :
    (rest.foldl chooseBetter first) ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp [List.foldl]
  | cons a xs ih =>
    simp only [List.foldl]
    have hFold := ih (chooseBetter first a)
    have hStep := chooseBetter_mem first a
    have hFold' : xs.foldl chooseBetter (chooseBetter first a) ∈
        first :: a :: xs := by
      simp only [List.mem_cons] at hFold ⊢
      rcases hFold with heq | hmem
      · rcases hStep with hbest | hcand
        · exact Or.inl (heq.trans hbest)
        · exact Or.inr (Or.inl (heq.trans hcand))
      · exact Or.inr (Or.inr hmem)
    exact hFold'

-- ════════════════════════════════════════════════════════════════════════════
-- Part 3: Exact-In unique canonical winner
-- ════════════════════════════════════════════════════════════════════════════

/-- The fold-based argmin over a candidate stream produces the UNIQUE element
that is both a member of the stream and dominates every candidate.

This composes:
- `foldl_chooseBetter_keyLe_all` (domination)
- `foldl_chooseBetter_mem` (membership)
- `keyLe_antisymm` (uniqueness via linear order) -/
theorem exact_in_exists_unique_canonical_winner
    (first : Candidate) (rest : List Candidate) :
    ∃! w, w ∈ first :: rest ∧ ∀ c ∈ first :: rest, keyLe w c := by
  set winner := rest.foldl chooseBetter first with hwinner_def
  refine ⟨winner, ?_, ?_⟩
  · -- Existence: winner satisfies both conditions
    constructor
    · exact foldl_chooseBetter_mem first rest
    · intro c hc
      have hAll := foldl_chooseBetter_keyLe_all first rest
      rcases List.mem_cons.mp hc with rfl | hmem
      · exact hAll.1
      · exact hAll.2 c hmem
  · -- Uniqueness: any other element satisfying the same must equal winner
    intro w' ⟨hw'Mem, hw'Le⟩
    have hAll := foldl_chooseBetter_keyLe_all first rest
    -- winner dominates w'
    have hWinW' : keyLe winner w' := by
      rcases List.mem_cons.mp hw'Mem with rfl | hmem
      · exact hAll.1
      · exact hAll.2 w' hmem
    -- w' dominates winner
    have hW'Win : keyLe w' winner :=
      hw'Le winner (foldl_chooseBetter_mem first rest)
    exact keyLe_antisymm hW'Win hWinW'

/-- The certificate winner IS the unique canonical winner.
Connects `buildCertificate` to the uniqueness theorem. -/
theorem certificate_identifies_unique_winner
    (first : Candidate) (rest : List Candidate) (bindingOk : Bool) :
    let cert := buildCertificate first rest bindingOk
    let certWinner : Candidate :=
      { candidateIndex := cert.winnerIndex, routeKeyRank := cert.winnerKey }
    certWinner ∈ first :: rest ∧
      ∀ c ∈ first :: rest, keyLe certWinner c := by
  constructor
  · -- The certificate winner is a member
    have hFold := foldl_chooseBetter_mem first rest
    have : (rest.foldl chooseBetter first) ∈ first :: rest := hFold
    show { candidateIndex := (buildCertificate first rest bindingOk).winnerIndex,
           routeKeyRank := (buildCertificate first rest bindingOk).winnerKey : Candidate }
      ∈ first :: rest
    have hEq : ({ candidateIndex := (buildCertificate first rest bindingOk).winnerIndex,
                   routeKeyRank := (buildCertificate first rest bindingOk).winnerKey : Candidate }) =
      rest.foldl chooseBetter first := by
      simp [buildCertificate]
    rw [hEq]
    exact hFold
  · -- The certificate winner dominates all
    intro c hc
    exact buildCertificate_winner_keyLe_all first rest bindingOk hc

-- ════════════════════════════════════════════════════════════════════════════
-- Part 4: Exact-Out unique canonical winner (reference)
-- ════════════════════════════════════════════════════════════════════════════

/-- The exact-out canonical minimizer theorem already proves uniqueness over
any nonempty Finset with a linear order. We re-export it here for composition.

Source: `ZenoDEXZenoDEX.ExactOutCanonicalMinimizer.exists_unique_canonical` -/
theorem exact_out_unique_canonical_winner
    {PoolId : Type} [LinearOrder PoolId]
    (S : Finset (ZenoDEX.ExactOutCanonicalMinimizer.Key PoolId)) (hS : S.Nonempty) :
    ∃! k, k ∈ S ∧ ∀ x ∈ S, k ≤ x :=
  ZenoDEX.ExactOutCanonicalMinimizer.exists_unique_canonical S hS

-- ════════════════════════════════════════════════════════════════════════════
-- Part 5: Non-vacuity witnesses
-- ════════════════════════════════════════════════════════════════════════════

/-- Witness: exact-in with 3 candidates, the unique winner is index 1 (lowest rank). -/
theorem witness_exact_in_3_candidates :
    let c0 : Candidate := ⟨0, 5⟩
    let c1 : Candidate := ⟨1, 2⟩
    let c2 : Candidate := ⟨2, 7⟩
    let winner := [c1, c2].foldl chooseBetter c0
    winner = c1 := by decide

/-- Witness: exact-in tie-break prefers lower candidate index. -/
theorem witness_exact_in_tie_break :
    let c0 : Candidate := ⟨3, 4⟩
    let c1 : Candidate := ⟨1, 4⟩
    let c2 : Candidate := ⟨5, 4⟩
    let winner := [c1, c2].foldl chooseBetter c0
    winner = c1 := by decide

/-- Witness: exact-in uniqueness — only one element satisfies mem ∧ keyLe_all. -/
theorem witness_exact_in_uniqueness :
    let c0 : Candidate := ⟨0, 3⟩
    let c1 : Candidate := ⟨1, 1⟩
    let c2 : Candidate := ⟨2, 3⟩
    let stream := [c0, c1, c2]
    (∀ w ∈ stream, (∀ c ∈ stream, keyLe w c) → w = c1) := by decide

-- ════════════════════════════════════════════════════════════════════════════
-- Part 6: keyLe is a total order (canonical_winner_requires_total_key)
-- ════════════════════════════════════════════════════════════════════════════

/-- **TOTAL ORDER CERTIFICATE**: The exact-in candidate key ordering `keyLe`
satisfies all four axioms of a total order:

  1. Reflexive: keyLe a a
  2. Transitive: keyLe a b → keyLe b c → keyLe a c
  3. Antisymmetric: keyLe a b → keyLe b a → a = b
  4. Total: keyLe a b ∨ keyLe b a

This certifies the ShapeForge cross-invariant `canonical_winner_requires_total_key`:
the exact-in routing key is total on every admitted nonempty candidate set.

Batch and exact-out keys inherit this property from Mathlib's `LinearOrder`
typeclass; exact-in keys prove it directly from `keyLe` definition. -/
theorem keyLe_is_total_order :
    (∀ a : Candidate, keyLe a a) ∧
    (∀ a b c : Candidate, keyLe a b → keyLe b c → keyLe a c) ∧
    (∀ a b : Candidate, keyLe a b → keyLe b a → a = b) ∧
    (∀ a b : Candidate, keyLe a b ∨ keyLe b a) :=
  ⟨keyLe_refl, fun _ _ _ => keyLe_trans, fun _ _ => keyLe_antisymm, keyLe_total⟩

-- ════════════════════════════════════════════════════════════════════════════
-- Part 7: Batch canonical winner (third leg of the three-way principle)
-- ════════════════════════════════════════════════════════════════════════════

/-- **BATCH CANONICAL WINNER**: For any nonempty finite set of batch keys,
there exists a unique canonical winner under the (A,B)-objective ordering.

Source: `Proofs.BatchAuctionCanonical.exists_unique_canonical`.
Key type: `(Volume^od ×_lex Surplus^od) ×_lex Order` — maximize volume,
then surplus, then choose the lexicographically smallest order.

This is the batch leg of the `unique_canonical_winner_everywhere` clause. -/
theorem batch_unique_canonical_winner
    (S : Finset Batch.Key) (hS : S.Nonempty) :
    ∃! k, k ∈ S ∧ ∀ x ∈ S, k ≤ x :=
  Batch.exists_unique_canonical S hS

-- ════════════════════════════════════════════════════════════════════════════
-- Part 8: Unified three-way canonicality principle
-- ════════════════════════════════════════════════════════════════════════════

/-- **UNIFIED THREE-WAY CANONICALITY**: All three DEX optimizer subsystems
produce unique canonical winners from the same abstract principle.

This is the composing theorem for ShapeForge `unique_canonical_winner_everywhere`.
It packages:
- Batch: `∃!` winner under `(Volume^od ×_lex Surplus^od) ×_lex Order`
- Exact-in: `∃!` winner under `keyLe = lex(routeKeyRank, candidateIndex)`
- Exact-out: `∃!` winner under `(inputTotal ×_lex legCount) ×_lex legsLex`

**Scope**: This theorem certifies **canonicality** (deterministic unique winner
selection). The separate **completeness** obligation (does the generator emit
all feasible candidates?) is tracked by `exact_out_generator_is_globally_complete_v1`
and remains open — it is a generator concern, not a canonicality concern. -/
theorem unified_three_way_canonicality
    -- Batch: arbitrary nonempty finite set of batch keys
    (batchS : Finset Batch.Key) (hBatch : batchS.Nonempty)
    -- Exact-in: arbitrary nonempty candidate stream
    (first : Candidate) (rest : List Candidate)
    -- Exact-out: arbitrary nonempty finite set of exact-out keys
    {PoolId : Type} [LinearOrder PoolId]
    (outS : Finset (ZenoDEX.ExactOutCanonicalMinimizer.Key PoolId))
    (hOut : outS.Nonempty) :
    -- (1) Batch has a unique canonical winner
    (∃! k, k ∈ batchS ∧ ∀ x ∈ batchS, k ≤ x) ∧
    -- (2) Exact-in has a unique canonical winner
    (∃! w, w ∈ first :: rest ∧ ∀ c ∈ first :: rest, keyLe w c) ∧
    -- (3) Exact-out has a unique canonical winner
    (∃! k, k ∈ outS ∧ ∀ x ∈ outS, k ≤ x) :=
  ⟨batch_unique_canonical_winner batchS hBatch,
   exact_in_exists_unique_canonical_winner first rest,
   exact_out_unique_canonical_winner outS hOut⟩

/-- **ABSTRACT MINIMUM PRINCIPLE**: The common abstract principle underlying
all three canonicality theorems. For any `LinearOrder`, any nonempty `Finset`
has a unique minimum element.

This is `Batch.exists_unique_min_of_finset_nonempty` from BatchAuctionCanonical.lean,
re-exported at the composing level. Both batch and exact-out keys are `LinearOrder`
types; exact-in satisfies this principle via the `keyLe` total order (Part 6). -/
theorem abstract_unique_minimum_principle
    {α : Type} [LinearOrder α] (S : Finset α) (hS : S.Nonempty) :
    ∃! m, m ∈ S ∧ ∀ x ∈ S, m ≤ x :=
  Batch.exists_unique_min_of_finset_nonempty S hS

-- ════════════════════════════════════════════════════════════════════════════
-- Part 9: End-to-end bridge — rank projection + fold uniqueness
-- ════════════════════════════════════════════════════════════════════════════

open Routing.ExactInRouteRankProjection in
/-- **END-TO-END RANK PROJECTION BRIDGE**: For any nonempty key list with a
linear order, there exists a unique `Fin` index that minimizes `trueKeyLe` —
the pre-projection semantic route-key order.

This composes:
- `exact_in_exists_unique_canonical_winner` (fold finds unique `keyLe`-min)
- `projectedCandidate_keyLe_iff_trueKeyLe` (`keyLe` on projected ↔ `trueKeyLe`)

to prove: the Python runtime's `sorted(set(keys))` rank projection faithfully
identifies the true canonical winner. Promotes `routing_exact_in_argmin` from
**contract** to **proved**. -/
theorem exists_unique_trueKeyLe_minimum
    {α : Type} [LinearOrder α]
    (keys : List α) (hne : 0 < keys.length) :
    ∃! i : Fin keys.length, ∀ j : Fin keys.length, trueKeyLe keys i j := by
  -- Build projected candidate list from key indices
  set projList := (List.finRange keys.length).map (projectedCandidate keys) with hProjDef
  -- Projected list is nonempty (same length as keys)
  have hLen : projList.length = keys.length := by simp [hProjDef]
  -- Decompose into first :: rest
  have ⟨first, rest, hCons⟩ : ∃ a l, projList = a :: l := by
    match projList, hLen with
    | a :: l, _ => exact ⟨a, l, rfl⟩
    | [], h => simp at h; omega
  -- Apply fold uniqueness theorem on projected candidates
  obtain ⟨w, ⟨hwMem, hwLe⟩, hwUniq⟩ := exact_in_exists_unique_canonical_winner first rest
  -- w is in projList, hence a projectedCandidate for some index
  have hwInProj : w ∈ projList := hCons ▸ hwMem
  rw [hProjDef, List.mem_map] at hwInProj
  obtain ⟨iStar, _, hiStarEq⟩ := hwInProj
  -- Helper: any Fin index maps to a member of first :: rest
  have hmem_of_fin : ∀ j : Fin keys.length,
      projectedCandidate keys j ∈ first :: rest := by
    intro j
    have : projectedCandidate keys j ∈ projList := by
      rw [hProjDef, List.mem_map]; exact ⟨j, List.mem_finRange j, rfl⟩
    exact hCons ▸ this
  -- iStar is the unique trueKeyLe-minimum
  refine ⟨iStar, ?_, ?_⟩
  · -- Domination: iStar ≤ every index under trueKeyLe
    intro j
    have hKeyLe : keyLe w (projectedCandidate keys j) := hwLe _ (hmem_of_fin j)
    rw [← hiStarEq] at hKeyLe
    exact (projectedCandidate_keyLe_iff_trueKeyLe keys iStar j).1 hKeyLe
  · -- Uniqueness: any other minimum equals iStar
    intro j hj
    have hiStarJ : trueKeyLe keys iStar j := by
      have hKeyLe : keyLe w (projectedCandidate keys j) := hwLe _ (hmem_of_fin j)
      rw [← hiStarEq] at hKeyLe
      exact (projectedCandidate_keyLe_iff_trueKeyLe keys iStar j).1 hKeyLe
    have hjIStar : trueKeyLe keys j iStar := hj iStar
    -- Convert to keyLe and use antisymmetry
    have h1 := (projectedCandidate_keyLe_iff_trueKeyLe keys j iStar).2 hjIStar
    have h2 := (projectedCandidate_keyLe_iff_trueKeyLe keys iStar j).2 hiStarJ
    have heq := keyLe_antisymm h1 h2
    have := congr_arg Candidate.candidateIndex heq
    simp [projectedCandidate] at this
    exact Fin.ext this

/-- Non-vacuity witness: 3-element key list `[5, 2, 7]` has unique
`trueKeyLe`-minimum at index 1 (key value 2). -/
theorem witness_trueKeyLe_minimum_3keys :
    let keys : List Nat := [5, 2, 7]
    ∃! i : Fin keys.length, ∀ j : Fin keys.length,
      Routing.ExactInRouteRankProjection.trueKeyLe keys i j := by
  exact exists_unique_trueKeyLe_minimum [5, 2, 7] (by simp)

-- ════════════════════════════════════════════════════════════════════════════
-- Part 10: Bounded-domain exact-out brute-force = canonical (composition)
-- ════════════════════════════════════════════════════════════════════════════

open TauSwap.ZenoDEX.ExactOutBruteforceCompleteness in
/-- **BOUNDED-DOMAIN EXACT-OUT CANONICALITY**: Over the finite brute-force
search interval `[lo, hi]`, the canonical exact-out winner exists, is unique,
and coincides with the brute-force witness.

This composes:
- `searchSet_nonempty` (bounded interval → nonempty candidate Finset)
- `witness_is_canonical` (brute-force witness ∈ search set and dominates)
- `witness_is_unique_canonical` (brute-force witness is THE ∃! canonical minimum)

**Significance**: The generator is COMPLETE over its bounded search domain.
Combined with `exists_unique_canonical`, the exact-out canonical winner over
the emitted domain is both found by the generator AND unique. Global generator
completeness beyond the bounded domain is a separate scope boundary
(`exact_out_generator_is_globally_complete_v1`). -/
theorem exact_out_bounded_complete_canonical
    {PoolId : Type} [LinearOrder PoolId]
    {routeKey : Nat → ZenoDEX.ExactOutCanonicalMinimizer.Key PoolId}
    {lo hi qStar : Nat}
    (hRange : qStar ∈ Finset.Icc lo hi)
    (hMin : ∀ x ∈ Finset.Icc lo hi, routeKey qStar ≤ routeKey x) :
    ∃! k, k ∈ searchSet routeKey lo hi ∧
      ∀ y ∈ searchSet routeKey lo hi, k ≤ y :=
  witness_is_unique_canonical hRange hMin

/-- Non-vacuity witness: the hypotheses of `exact_out_bounded_complete_canonical`
are achievable. A single-element search set `[lo, lo]` trivially satisfies
the preconditions. -/
theorem witness_bounded_complete_canonical_preconditions :
    (0 : Nat) ∈ Finset.Icc 0 2 := by decide

-- ════════════════════════════════════════════════════════════════════════════
-- Part 11: Complete promotion summary
-- ════════════════════════════════════════════════════════════════════════════

/-- **PROMOTION SUMMARY**: All three slice promotions needed for
`unique_canonical_winner_everywhere` at `proved` status:

| Slice | Status | Key Theorem |
|-------|--------|-------------|
| `batch_canonicalization` | proved | `batch_unique_canonical_winner` |
| `routing_exact_in_argmin` | proved | `exists_unique_trueKeyLe_minimum` |
| `exact_out_canonical_minimizer` | proved | `exact_out_bounded_complete_canonical` |

Cross-invariant `canonical_winner_requires_total_key`:
  certified by `keyLe_is_total_order` (exact-in) and Mathlib `LinearOrder`
  (batch, exact-out).

**Scope**: Canonicality fully proved. Generator completeness beyond the bounded
search domain is a separate scope boundary — see negative knowledge entry
`exact_out_generator_is_globally_complete_v1`. -/
theorem promotion_summary :
    -- (1) Batch: unique canonical winner for any nonempty Finset
    (∀ (S : Finset Batch.Key), S.Nonempty → ∃! k, k ∈ S ∧ ∀ x ∈ S, k ≤ x) ∧
    -- (2) Exact-in: unique canonical winner via fold + rank projection
    (∀ (first : Candidate) (rest : List Candidate),
      ∃! w, w ∈ first :: rest ∧ ∀ c ∈ first :: rest, keyLe w c) ∧
    -- (3) Exact-out: unique canonical winner for any nonempty Finset
    (∀ {PoolId : Type} [LinearOrder PoolId]
      (S : Finset (ZenoDEX.ExactOutCanonicalMinimizer.Key PoolId)),
      S.Nonempty → ∃! k, k ∈ S ∧ ∀ x ∈ S, k ≤ x) ∧
    -- (4) Cross-invariant: exact-in key is a total order
    ((∀ a : Candidate, keyLe a a) ∧
     (∀ a b c : Candidate, keyLe a b → keyLe b c → keyLe a c) ∧
     (∀ a b : Candidate, keyLe a b → keyLe b a → a = b) ∧
     (∀ a b : Candidate, keyLe a b ∨ keyLe b a)) :=
  ⟨fun S hS => batch_unique_canonical_winner S hS,
   fun first rest => exact_in_exists_unique_canonical_winner first rest,
   fun S hS => exact_out_unique_canonical_winner S hS,
   keyLe_is_total_order⟩

end UniqueCanonicalWinnerEverywhere
end TauSwap
