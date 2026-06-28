# ZenoDEX AB Subset-DP Dominance Frontier - 2026-06-28

## Executive Result

The next high-value AB-ordering target is Pareto dominance pruning inside the
full-state subset DP. A bounded refutation checker found no counterexample to
the proposed dominance relation on exact-in same-direction AB batches.

This is a candidate frontier item. It is not yet a core implementation change
and it is not a machine-checked proof.

## Hypothesis Card

- `hypothesis_id`: `ab_subset_dp_pareto_dominance_pruning_v1`
- `mechanism_change`: prune dominated states inside each processed-set bucket of
  the AB full-state subset DP.
- `representation_shift_used`: `quotient`
- `expected_metric_delta`: lower state count and lower runtime for bounded
  exact AB ordering; no intended change to selected order.
- `null_hypothesis`: the proposed dominance relation is unsound; a dominated
  state can still produce a better final AB key for some remaining suffix.
- `falsification_recipe`: generate reachable states with the same processed
  mask, identify dominance pairs, then replay every remaining-order suffix
  within the declared bound.
- `support_recipe`: compare pruned DP against the existing full-state DP and
  brute force on small batches; measure state reduction and runtime.
- `formal_obligations`: prove CPMM exact-in monotonicity over the dominance
  order, prove no-op preservation for rejected swaps, and prove suffix
  simulation from a dominating state weakly improves the AB key.
- `risk_modes`: exact-out swaps, mixed direction, tie handling, and grouped
  sender balances can invalidate an overbroad dominance claim.
- `status`: `supported-candidate`

## Candidate Dominance Rule

For same-pool, same-direction, exact-in AB states with the same processed mask,
state `s1` may dominate state `s2` when:

```text
s1.amount_a >= s2.amount_a
s1.surplus_b >= s2.surplus_b
s1.r_in <= s2.r_in
s1.r_out >= s2.r_out
s1.remaining_balances >= s2.remaining_balances  (componentwise)
if objective totals tie, s1.order_ids <= s2.order_ids
```

The rule says `s1` has at least as good an accumulated objective, at least as
good future CPMM price conditions for exact-in swaps, at least as much remaining
sender capacity, and no worse deterministic tie prefix.

## Replay Receipt

```bash
python3 tools/check_ab_subset_dp_dominance_candidate.py
```

Result:

```json
{
  "ok": true,
  "case_count": 18,
  "dominance_pairs_seen": 760384,
  "dominance_pairs_checked": 3959,
  "suffix_permutations_checked": 12707,
  "max_states_for_mask": 720,
  "first_counterexample": null
}
```

The checker uses an explicit budget: `n in {4,5,6}`, 6 variants per size, at
most 4 remaining suffix items, and at most 12 checked dominance pairs per mask.
For each selected pair, suffix replay is exhaustive within the suffix bound.

## Why It Matters

The existing AB subset DP carries full reserves and per-sender balances in each
subset bucket. That is correct, but the number of states can grow quickly.
Dominance pruning gives a proof-shaped path to reduce states without changing
the exact objective, provided the dominance relation is kept within the exact-in
same-direction domain or separately extended with new proofs.

## Non-Claims

- This does not prove dominance for exact-out intents.
- This does not prove dominance for mixed-direction batches.
- This does not modify the production ordering path.
- Passing this bounded checker is not a Lean theorem.
- No settlement authority is derived from this research note.

## Next Implementation Step

Add an opt-in research version of AB subset DP with this dominance filter and
compare it against the existing full-state DP plus brute force. Promotion should
require zero selected-order mismatches, deterministic state-reduction receipts,
and a targeted proof note before touching the default core path.
