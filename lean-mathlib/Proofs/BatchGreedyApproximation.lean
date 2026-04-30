import Proofs.BatchGreedyOptimality
import Mathlib.Tactic

/-!
# Batch Greedy Approximation: k-Intent A-Optimality and B-Gap Bounds

Extends `BatchGreedyOptimality.lean` (2-intent equal-input case) to k-intent
batches. The extension has two dimensions:

1. **A-optimality (volume)**: for k equal-input intents processed with greedy
   skip-on-fail scheduling, any adjacent transposition that violates the
   greedy (descending minOut) order cannot increase total executed volume.
   The key structural lemma (`depletion_gap_bounded`) shows that processing
   one extra equal-input intent before a sequence of equal-input intents
   costs at most d in tail volume.

2. **B-gap (surplus)**: for 2 equal-input intents that both execute, the total
   output is order-invariant (`equal_input_output_sum_invariant`), so the
   surplus difference is zero.

## Mathematical model

- Intents are `(input, minOut)` pairs, all with the same input `d`.
- Scheduling uses **skip-on-fail**: try each intent left-to-right; if
  satisfiable, execute and update the pool; otherwise skip (pool unchanged).
- Volume = sum of `input` for executed intents.
- Surplus = sum of `(output - minOut)` for executed intents.

## Key results

| # | Name | Kind | Statement |
|---|------|------|-----------|
| 1 | `scheduleVol` | Def | Volume of a skip-on-fail schedule |
| 2 | `tail_pool_both_exec` | Structural | Equal inputs: pool after both execute is order-invariant |
| 3 | `depletion_gap_bounded` | Structural | Extra depletion costs at most d in tail volume |
| 4 | `k_intent_greedy_volume_optimal` | Main | k-intent greedy A-optimality (equal-input) |
| 5 | `two_intent_B_gap_zero` | Main | B-gap = 0 for 2 equal-input intents |
| 6 | `outputAtN_antitone_trans` | Structural | Position output anti-monotone for arbitrary offsets |
| 7 | `satisfiable_set_nesting` | Structural | Satisfiable set at n+1 is subset of set at n |

## Proof dependencies
- `BatchGreedyOptimality.lean`: greedy_volume_ge_reverse_equal_input,
  exchange_at_any_position, equal_input_output_sum_invariant, equal_input_same_pool
- `CPMMOutputMonotonicity.lean`: swapOut_diminishing_returns
- `AntiFragmentation.lean`: swapOut definition
- This file: k-intent extension (formal, 0 sorry)
-/

namespace BatchGreedyApproximation

open BatchGreedyOptimality (Intent intentOut satisfiable poolAfter poolAfterN outputAtN
  exchange_at_any_position outputAtN_antitone equal_input_output_sum_invariant
  greedy_volume_ge_reverse_equal_input equal_input_sat_transfer
  satisfiable_on_original_if_on_depleted not_sat_on_depleted_if_not_on_original
  equal_input_same_pool greedyVol reverseVol price_impact_reduces_output)
open AntiFragmentation (swapOut)

/-! ## Part 1: k-Intent Scheduling Definitions -/

/-- Volume (total executed input) of a schedule processed left-to-right
    with greedy skip-on-fail semantics. An intent executes if satisfiable
    on the current pool state; otherwise it is skipped and the pool is
    unchanged for the next intent. -/
def scheduleVol (x y : ℕ) : List Intent → ℕ
  | [] => 0
  | i :: rest =>
    if satisfiable x y i then
      i.input + scheduleVol (poolAfter x y i).1 (poolAfter x y i).2 rest
    else
      scheduleVol x y rest

/-- Total output of a schedule (sum of outputs for executed intents). -/
def scheduleOut (x y : ℕ) : List Intent → ℕ
  | [] => 0
  | i :: rest =>
    if satisfiable x y i then
      intentOut x y i + scheduleOut (poolAfter x y i).1 (poolAfter x y i).2 rest
    else
      scheduleOut x y rest

/-- Non-vacuity: scheduleVol for concrete example.
    Pool (1000, 1000), a = (100, 80), b = (100, 70).
    Greedy [a,b]: a satisfies (90>=80), b satisfies on depleted (75>=70). Vol = 200.
    Reverse [b,a]: b satisfies (90>=70), a fails on depleted (75<80). Vol = 100. -/
theorem witness_scheduleVol :
    let x := 1000; let y := 1000
    let a : Intent := ⟨100, 80⟩; let b : Intent := ⟨100, 70⟩
    scheduleVol x y [a, b] = 200 ∧
    scheduleVol x y [b, a] = 100 ∧
    scheduleOut x y [a, b] = 165 ∧
    scheduleOut x y [b, a] = 90 := by
  native_decide

/-! ## Part 2: Pool State Invariance After Two Equal-Input Executions -/

/-- TAIL POOL INVARIANCE: when two equal-input intents both execute,
    the pool state after both is order-invariant.

    Proof: equal_input_same_pool gives poolAfter(x,y,a) = poolAfter(x,y,b).
    Applying it again at the intermediate pool gives the result. -/
theorem tail_pool_both_exec (x y d : ℕ) (a b : Intent)
    (ha : a.input = d) (hb : b.input = d) :
    poolAfter (poolAfter x y a).1 (poolAfter x y a).2 b =
    poolAfter (poolAfter x y b).1 (poolAfter x y b).2 a := by
  have h1 := equal_input_same_pool x y d a b ha hb
  rw [h1]
  exact equal_input_same_pool (poolAfter x y b).1 (poolAfter x y b).2 d b a hb ha

/-- Non-vacuity: tail pool invariance with concrete values.
    Pool (1000, 1000), both intents input = 100.
    After both execute: pool = (1200, 835) regardless of order. -/
theorem witness_tail_pool :
    let x := 1000; let y := 1000
    let a : Intent := ⟨100, 80⟩; let b : Intent := ⟨100, 70⟩
    poolAfter (poolAfter x y a).1 (poolAfter x y a).2 b = (1200, 835) ∧
    poolAfter (poolAfter x y b).1 (poolAfter x y b).2 a = (1200, 835) := by
  native_decide

/-! ## Part 3: Depletion Gap Lemma

The key structural result for k-intent optimality: processing one extra
equal-input intent before a sequence of equal-input intents costs at most
d in tail volume.

Formally: `scheduleVol(x, y, rest) ≤ d + scheduleVol(P.1, P.2, rest)`
where `P = poolAfter(x, y, b)` for any b with `b.input = d` and all intents
in rest have input d.

Proof by induction on rest:
- **Base** (rest = []): 0 ≤ d + 0.
- **Case 1** (c fails on (x,y)): c also fails on P (more depleted pool), skip.
  Gap for rest' ≤ d by IH.
- **Case 2** (c succeeds on both): both pools deplete by one d-input trade.
  poolAfter(x,y,c) = poolAfter(x,y,b) = P (equal inputs). And
  poolAfter(P,c) is one more depletion of P. By IH on rest', gap ≤ d.
- **Case 3** (c succeeds on (x,y) but fails on P): the single execution on
  the less-depleted pool yields d. poolAfter(x,y,c) = P. Both sides now
  process rest' from the SAME pool P. Gap = d − 0 + (tail_P − tail_P) = d. -/
theorem depletion_gap_bounded (x y d : ℕ) (b : Intent) (rest : List Intent)
    (hb : b.input = d) (hall : ∀ c ∈ rest, c.input = d) :
    scheduleVol x y rest ≤ d + scheduleVol (poolAfter x y b).1 (poolAfter x y b).2 rest := by
  induction rest generalizing x y b with
  | nil => simp [scheduleVol]
  | cons c rest' ih =>
    have hc : c.input = d := hall c (List.mem_cons_self ..)
    have hrest' : ∀ e ∈ rest', e.input = d := fun e he => hall e (List.mem_cons_of_mem _ he)
    simp only [scheduleVol]
    by_cases hc_orig : satisfiable x y c
    · rw [if_pos hc_orig]
      -- c satisfiable on original pool (x, y)
      by_cases hc_depl : satisfiable (poolAfter x y b).1 (poolAfter x y b).2 c
      · -- Case 2: c satisfiable on both pools
        rw [if_pos hc_depl]
        -- poolAfter(x,y,c) = poolAfter(x,y,b) since c.input = d = b.input
        have hpc := equal_input_same_pool x y d c b hc hb
        -- poolAfter(P,c) where P = poolAfter(x,y,b)
        -- IH: scheduleVol(poolAfter(x,y,c), rest') ≤ d + scheduleVol(poolAfter(poolAfter(x,y,c),c), rest')
        -- But we need it with the right pools. After rewriting:
        -- LHS: c.input + scheduleVol(poolAfter(x,y,c), rest')
        -- RHS: d + (c.input + scheduleVol(poolAfter(P,c), rest'))
        -- poolAfter(x,y,c) = P by hpc. So LHS = d + scheduleVol(P, rest').
        -- RHS = d + d + scheduleVol(poolAfter(P,c), rest').
        -- Need: d + scheduleVol(P, rest') ≤ d + d + scheduleVol(poolAfter(P,c), rest').
        -- i.e. scheduleVol(P, rest') ≤ d + scheduleVol(poolAfter(P,c), rest').
        -- This is exactly the IH applied at pool P with prior trade c.
        rw [hc, hpc]
        have ih_step := ih (poolAfter x y b).1 (poolAfter x y b).2 c hc hrest'
        omega
      · -- Case 3: c satisfiable on (x,y) but NOT on depleted pool P
        rw [if_neg hc_depl]
        -- LHS: c.input + scheduleVol(poolAfter(x,y,c), rest')
        -- RHS: d + scheduleVol(P, rest')
        -- poolAfter(x,y,c) = poolAfter(x,y,b) = P (equal inputs)
        have hpc := equal_input_same_pool x y d c b hc hb
        rw [hc, hpc]
    · -- Case 1: c NOT satisfiable on original pool (x, y)
      rw [if_neg hc_orig]
      -- c also not satisfiable on depleted pool P (more depleted => less output)
      have hc_depl : ¬satisfiable (poolAfter x y b).1 (poolAfter x y b).2 c :=
        not_sat_on_depleted_if_not_on_original x y b c hc_orig
      rw [if_neg hc_depl]
      -- Both skip c. Gap for rest' ≤ d by IH.
      exact ih x y b hb hrest'

/-- Non-vacuity: depletion gap is exactly d in the critical case.
    Pool (1000, 1000), d = 100, prior trade b = (100, 70).
    P = poolAfter(1000, 1000, b) = (1100, 910).
    rest = [(100, 65)]: succeeds on (1000,1000) with output 90, fails on P with output 75... wait.
    Actually 75 >= 65, so it succeeds on P too. Let me find a crossing case.
    rest = [(100, 76)]: output on original = 90 >= 76 (yes), output on P = 75 < 76 (no).
    scheduleVol(1000, 1000, [(100,76)]) = 100.
    scheduleVol(1100, 910, [(100,76)]) = 0.
    100 <= 100 + 0 = 100. Gap = d exactly. -/
theorem witness_depletion_gap :
    let x := 1000; let y := 1000
    let b : Intent := ⟨100, 70⟩
    let rest := [Intent.mk 100 76]
    scheduleVol x y rest = 100 ∧
    scheduleVol (poolAfter x y b).1 (poolAfter x y b).2 rest = 0 ∧
    scheduleVol x y rest ≤ 100 + scheduleVol (poolAfter x y b).1 (poolAfter x y b).2 rest := by
  native_decide

/-! ## Part 4: k-Intent Greedy Volume Optimality

Using the depletion gap lemma, we prove that for k equal-input intents,
greedy scheduling (descending minOut) maximizes total executed volume
over any adjacent transposition. -/

/-- K-INTENT GREEDY VOLUME OPTIMAL: for equal-input intents a, b with
    a.minOut >= b.minOut, and a tail `rest` where all intents have the
    same input d, scheduling a before b gives at least as much total
    volume as b before a.

    When both intents a and b are satisfiable on the original pool:
    the exchange property and depletion gap lemma give the result.
    When only one is satisfiable: satisfiability transfer handles it.
    When neither is satisfiable: both are skipped, tail is identical. -/
theorem k_intent_greedy_volume_optimal (x y d : ℕ) (a b : Intent) (rest : List Intent)
    (ha_in : a.input = d) (hb_in : b.input = d)
    (hmin : a.minOut ≥ b.minOut)
    (hall : ∀ c ∈ rest, c.input = d) :
    scheduleVol x y (a :: b :: rest) ≥ scheduleVol x y (b :: a :: rest) := by
  simp only [scheduleVol]
  by_cases ha_sat : satisfiable x y a
  · rw [if_pos ha_sat]
    by_cases hab : satisfiable (poolAfter x y a).1 (poolAfter x y a).2 b
    · rw [if_pos hab]
      have hb_sat : satisfiable x y b :=
        satisfiable_on_original_if_on_depleted x y a b hab
      rw [if_pos hb_sat]
      by_cases hba : satisfiable (poolAfter x y b).1 (poolAfter x y b).2 a
      · -- Both survive in second position. Tail sees same pool.
        rw [if_pos hba]
        have htail := tail_pool_both_exec x y d a b ha_in hb_in
        rw [htail, ha_in, hb_in]
      · -- b survives after a, a does NOT survive after b.
        rw [if_neg hba]
        -- Greedy: 2d + scheduleVol(poolAfter(poolAfter(x,y,a),b), rest).
        -- Reverse: d + scheduleVol(poolAfter(x,y,b), rest).
        -- poolAfter(x,y,a) = poolAfter(x,y,b) =: P1 by equal_input_same_pool.
        -- poolAfter(P1, b) =: P2.
        -- Need: 2d + scheduleVol(P2, rest) >= d + scheduleVol(P1, rest).
        -- i.e. d + scheduleVol(P2, rest) >= scheduleVol(P1, rest).
        -- This is exactly the depletion gap lemma.
        have hpool := equal_input_same_pool x y d a b ha_in hb_in
        rw [ha_in, hb_in]
        -- After rw, we need:
        -- d + (d + scheduleVol(poolAfter(poolAfter(x,y,a), b), rest))
        --   >= d + scheduleVol(poolAfter(x,y,b), rest)
        -- The poolAfter(x,y,a) is P1 = poolAfter(x,y,b) by hpool.
        -- So poolAfter(poolAfter(x,y,a), b) = poolAfter(P1, b) = P2.
        -- And RHS has scheduleVol(P1, rest).
        -- Rewrite using hpool to make the pools match.
        rw [hpool]
        -- Now: d + (d + scheduleVol(poolAfter(poolAfter(x,y,b), b), rest))
        --   >= d + scheduleVol(poolAfter(x,y,b), rest)
        -- Apply depletion_gap_bounded at P1 = poolAfter(x,y,b) with prior b.
        have hgap := depletion_gap_bounded (poolAfter x y b).1 (poolAfter x y b).2 d b rest hb_in hall
        omega
    · rw [if_neg hab]
      by_cases hb_sat : satisfiable x y b
      · rw [if_pos hb_sat]
        by_cases hba : satisfiable (poolAfter x y b).1 (poolAfter x y b).2 a
        · -- a sat on original, b NOT sat after a. But a sat after b.
          -- By exchange: a (harder) sat after b => b (easier) sat after a.
          -- Contradicts hab.
          exact absurd (equal_input_sat_transfer x y d a b ha_in hb_in hmin hba) hab
        · rw [if_neg hba]
          -- Greedy: a executes, b fails. Vol = d + tail(poolAfter(x,y,a)).
          -- Reverse: b executes, a fails. Vol = d + tail(poolAfter(x,y,b)).
          -- poolAfter(x,y,a) = poolAfter(x,y,b) by equal inputs.
          have hpool := equal_input_same_pool x y d a b ha_in hb_in
          rw [ha_in, hb_in, hpool]
      · -- b NOT sat on original. Reverse: skip b, try a. Greedy: a exec.
        rw [if_neg hb_sat, if_pos ha_sat]
  · rw [if_neg ha_sat]
    by_cases hb_sat : satisfiable x y b
    · -- a NOT sat on original. b sat.
      rw [if_pos hb_sat]
      have hba : ¬satisfiable (poolAfter x y b).1 (poolAfter x y b).2 a :=
        not_sat_on_depleted_if_not_on_original x y b a ha_sat
      rw [if_neg hba, if_pos hb_sat]
    · rw [if_neg hb_sat, if_neg ha_sat, if_neg hb_sat]

/-- Non-vacuity: k-intent greedy is strictly better in 3-intent case.
    Pool (1000, 1000), d = 100.
    Greedy [a,b,c] where a=(100,80), b=(100,70), c=(100,60): all 3 execute. Vol = 300.
    Swapped [b,a,c]: b succeeds, a fails (75<80), c on less-depleted pool succeeds. Vol = 200. -/
theorem witness_k_intent_greedy :
    let x := 1000; let y := 1000
    let a : Intent := ⟨100, 80⟩; let b : Intent := ⟨100, 70⟩
    let c : Intent := ⟨100, 60⟩
    scheduleVol x y [a, b, c] = 300 ∧
    scheduleVol x y [b, a, c] = 200 ∧
    scheduleVol x y [a, b, c] > scheduleVol x y [b, a, c] := by
  native_decide

/-- Non-vacuity: 4-intent case showing greedy advantage propagates.
    Pool (10000, 10000), d = 100.
    Greedy [99, 97, 95, 90]: outputs 99, 97, 95, 93. All satisfy. Vol = 400.
    Swapped [97, 99, 95, 90]: 97 at pos 0 (99>=97 yes), 99 at pos 1 (97<99 no),
    95 at pos 1 (97>=95 yes), 90 at pos 2 (95>=90 yes). Vol = 300. -/
theorem witness_k_intent_4 :
    let x := 10000; let y := 10000
    let i1 : Intent := ⟨100, 99⟩
    let i2 : Intent := ⟨100, 97⟩
    let i3 : Intent := ⟨100, 95⟩
    let i4 : Intent := ⟨100, 90⟩
    scheduleVol x y [i1, i2, i3, i4] = 400 ∧
    scheduleVol x y [i2, i1, i3, i4] = 300 ∧
    scheduleVol x y [i1, i2, i3, i4] > scheduleVol x y [i2, i1, i3, i4] := by
  native_decide

/-! ## Part 5: B-Gap Analysis (Equal-Input B-Gap = 0) -/

/-- TWO-INTENT B-GAP IS ZERO: when both intents have equal input d,
    the total output from executing both is identical regardless of order.

    The B metric (total surplus = total_output - total_minOut) therefore
    has the same value for both orderings when both execute, giving B-gap = 0.

    Proof: direct application of `equal_input_output_sum_invariant`. -/
theorem two_intent_B_gap_zero (x y d : ℕ) (a b : Intent)
    (ha : a.input = d) (hb : b.input = d) :
    intentOut x y a + intentOut (poolAfter x y a).1 (poolAfter x y a).2 b =
    intentOut x y b + intentOut (poolAfter x y b).1 (poolAfter x y b).2 a :=
  equal_input_output_sum_invariant x y d a b ha hb

/-- B-GAP BOUNDED: for two equal-input intents, the surplus difference
    between any two orderings is bounded by 0 when both intents execute. -/
theorem greedy_B_gap_bounded (x y d : ℕ) (a b : Intent)
    (ha : a.input = d) (hb : b.input = d) :
    intentOut x y a + intentOut (poolAfter x y a).1 (poolAfter x y a).2 b =
    intentOut x y b + intentOut (poolAfter x y b).1 (poolAfter x y b).2 a :=
  two_intent_B_gap_zero x y d a b ha hb

/-- Non-vacuity: B-gap = 0 with concrete values.
    Pool (1000, 1000), intents with input 100.
    Total output = 90 + 75 = 165 regardless of order. -/
theorem witness_B_gap_zero :
    let x := 1000; let y := 1000
    let a : Intent := ⟨100, 80⟩; let b : Intent := ⟨100, 50⟩
    intentOut x y a + intentOut (poolAfter x y a).1 (poolAfter x y a).2 b = 165 ∧
    intentOut x y b + intentOut (poolAfter x y b).1 (poolAfter x y b).2 a = 165 ∧
    intentOut x y a + intentOut (poolAfter x y a).1 (poolAfter x y a).2 b =
      intentOut x y b + intentOut (poolAfter x y b).1 (poolAfter x y b).2 a := by
  native_decide

/-! ## Part 6: Position Output Monotonicity -/

/-- OUTPUT ANTITONE TRANSITIVE: output at position n+k is no greater than
    at position n, for any k. Extends `outputAtN_antitone` (k=1) to
    arbitrary offsets by induction.

    The structural reason that earlier positions are more valuable. -/
theorem outputAtN_antitone_trans (x y d n k : ℕ) :
    outputAtN x y d (n + k) ≤ outputAtN x y d n := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc outputAtN x y d (n + (k + 1))
        = outputAtN x y d ((n + k) + 1) := by ring_nf
      _ ≤ outputAtN x y d (n + k) := outputAtN_antitone x y d (n + k)
      _ ≤ outputAtN x y d n := ih

/-- Non-vacuity: antitone transitive with concrete values.
    Position 0: 90, Position 3: 55. 55 <= 90. -/
theorem witness_antitone_trans :
    outputAtN 1000 1000 100 0 = 90 ∧
    outputAtN 1000 1000 100 3 = 55 ∧
    outputAtN 1000 1000 100 3 ≤ outputAtN 1000 1000 100 0 := by
  native_decide

/-- POSITION THRESHOLD: if an intent is satisfiable at a later position n+1,
    it is satisfiable at the earlier position n. -/
theorem satisfiable_at_earlier_position (x y d n m : ℕ)
    (h : outputAtN x y d (n + 1) ≥ m) :
    outputAtN x y d n ≥ m := by
  have := outputAtN_antitone x y d n
  omega

/-- Non-vacuity: position threshold is strict. -/
theorem witness_position_threshold :
    outputAtN 1000 1000 100 0 = 90 ∧
    outputAtN 1000 1000 100 1 = 75 ∧
    outputAtN 1000 1000 100 2 = 64 ∧
    outputAtN 1000 1000 100 0 ≥ 80 ∧
    ¬(outputAtN 1000 1000 100 1 ≥ 80) := by
  native_decide

/-! ## Part 7: Exchange Property Consequences -/

/-- EXCHANGE AT ANY POSITION: for equal-input intents at any position n,
    if the harder intent (higher minOut) is satisfiable, the easier is too.

    The matroid-like exchange axiom underlying greedy optimality. -/
theorem exchange_property (x y d : ℕ) (a b : Intent) (n : ℕ)
    (ha : a.input = d) (hb : b.input = d) (hmin : a.minOut ≥ b.minOut)
    (ha_sat : satisfiable (poolAfterN x y d n).1 (poolAfterN x y d n).2 a) :
    satisfiable (poolAfterN x y d n).1 (poolAfterN x y d n).2 b :=
  exchange_at_any_position x y d a b n ha hb hmin ha_sat

/-- SATISFIABLE SET NESTING: the set of intents satisfiable at position n+1
    is a subset of those satisfiable at position n. -/
theorem satisfiable_set_nesting (x y d : ℕ) (i : Intent) (n : ℕ)
    (hi : i.input = d)
    (h : satisfiable (poolAfterN x y d (n + 1)).1 (poolAfterN x y d (n + 1)).2 i) :
    satisfiable (poolAfterN x y d n).1 (poolAfterN x y d n).2 i := by
  simp only [satisfiable, intentOut, AntiFragmentation.swapOut] at *
  rw [hi] at *
  have hanti := outputAtN_antitone x y d n
  simp only [outputAtN, AntiFragmentation.swapOut] at hanti
  omega

/-- Non-vacuity: satisfiable set nesting. -/
theorem witness_sat_nesting :
    let x := 1000; let y := 1000; let d := 100
    let easy : Intent := ⟨100, 70⟩
    let hard : Intent := ⟨100, 80⟩
    satisfiable (poolAfterN x y d 0).1 (poolAfterN x y d 0).2 easy ∧
    satisfiable (poolAfterN x y d 1).1 (poolAfterN x y d 1).2 easy ∧
    ¬satisfiable (poolAfterN x y d 2).1 (poolAfterN x y d 2).2 easy ∧
    satisfiable (poolAfterN x y d 0).1 (poolAfterN x y d 0).2 hard ∧
    ¬satisfiable (poolAfterN x y d 1).1 (poolAfterN x y d 1).2 hard := by
  native_decide

/-! ## Part 8: Schedule Volume Bounds -/

/-- VOLUME UPPER BOUND: schedule volume is bounded by sum of inputs. -/
theorem scheduleVol_le_sum_input (x y : ℕ) (intents : List Intent) :
    scheduleVol x y intents ≤ (intents.map Intent.input).sum := by
  induction intents generalizing x y with
  | nil => simp [scheduleVol]
  | cons i rest ih =>
    simp only [scheduleVol, List.map_cons, List.sum_cons]
    split
    · have := ih (poolAfter x y i).1 (poolAfter x y i).2; omega
    · have := ih x y; omega

/-- Non-vacuity: volume bound is tight when all intents execute. -/
theorem witness_vol_bound :
    let x := 10000; let y := 10000
    let intents : List Intent := [⟨100, 10⟩, ⟨200, 10⟩, ⟨50, 10⟩]
    scheduleVol x y intents = 350 ∧
    (intents.map Intent.input).sum = 350 := by
  native_decide

end BatchGreedyApproximation
