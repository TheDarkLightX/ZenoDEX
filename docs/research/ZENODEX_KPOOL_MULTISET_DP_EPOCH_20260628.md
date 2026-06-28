# ZenoDEX k-Pool Multiset DP Search Epoch - 2026-06-28

## Scope

This note records a Research Kernel search epoch for the cross-pool batch
clearing oracle. It is a research result, not a settlement rule and not a
production security claim.

The target surface is same-direction exact-in batch routing across `k` CPMM
pools with integer fee-ceil and output-floor arithmetic. The existing subset
DP removes the factorial ordering barrier by exploring the subset lattice. The
remaining hypothesis here is whether duplicate exact-in amounts can be
quotiented for `k > 2`, as already done for the two-pool oracle.

## Hypothesis Card

- `hypothesis_id`: `H-kpool-multiset-dp-20260628`
- `mechanism_change`: replace the k-pool subset bitmask with per-amount usage
  counts when exact-in amounts repeat.
- `representation_shift_used`: `quotient`
- `expected_metric_delta`: lower state count, lower transition count, lower
  runtime on duplicate-heavy batches; unchanged optimum in the modeled domain.
- `null_hypothesis`: identity still matters in k-pool reserve trajectories, so
  grouping duplicate amounts changes the optimum.
- `falsification_recipe`: compare k-pool multiset DP against k-pool subset DP
  and brute force on adversarial duplicate-heavy small domains.
- `support_recipe`: measure state, transition, ordering, and runtime reductions
  on duplicate-heavy fixtures.
- `formal_obligations`: prove that equal exact-in amounts are behaviorally
  interchangeable because the transition depends on amount and reserve state,
  not intent identity.
- `risk_modes`: hidden per-intent fields, heterogeneous constraints, per-user
  balances, exact-out intents, and settlement-authority misuse.
- `status`: `supported-bounded`

## Bounded Evidence

Self-contained experiment, seed `2026062802`:

| Check | Cases | Result |
|-------|-------|--------|
| k-pool subset DP vs k-pool multiset DP | 36 | 0 mismatches |
| k-pool multiset DP vs brute force | 14 | 0 mismatches |

The subset-vs-multiset corpus included `k=3,4`, `n=3..5`, duplicate-heavy
amount alphabets, reserves in `{1,2,3,5,10,50,100}`, and fees in
`{0,1,30,100,500,5000,9999}`.

Maximum observed reduction in the parity corpus:

| Metric | Reduction |
|--------|-----------|
| States visited | `4.86x` |
| Transitions evaluated | `14.86x` |

Duplicate-heavy benchmark fixtures:

| Intents | Output preserved | State ratio | Transition ratio | Ordering ratio | Runtime ratio |
|---------|------------------|-------------|------------------|----------------|---------------|
| `[4,4,4,4,4,4]` | `True` | `3.10x` | `12.80x` | `720.00x` | `26.07x` |
| `[3,3,3,5,5]` | `True` | `1.69x` | `3.40x` | `12.00x` | `7.58x` |

## Candidate Algorithm

```text
state = (used_count_by_amount, input_0..input_{k-2}, y_0..y_{k-2})
hidden_pool = derived by conservation from processed input and banked output

for each reachable count vector:
  for each amount class with remaining count:
    for each k-way allocation of that amount:
      update reserves and banked output
      keep the highest output for the next compressed state
```

The ordering upper bound changes from:

```text
n!
```

to:

```text
n! / product_d count_d!
```

where `count_d` is the multiplicity of exact-in amount `d`.

The DP remains exponential in the number of distinct amount classes and
pseudo-polynomial in the split domain. It reduces the identity factor for
duplicate-heavy batches; it does not remove the general subset lower bound for
all-distinct inputs.

## Non-Claims

- No production settlement authority is claimed.
- No exact-out, heterogeneous-constraint, per-user-balance, or slippage-limit
  support is claimed.
- No polynomial-time algorithm for arbitrary all-distinct k-pool batch clearing
  is claimed.
- The experiment is bounded evidence. A core implementation should still add
  focused tests, a benchmark tool, and a formal quotient proof obligation.

## Next Promotion Gate

1. Add `solve_k_pool_cpmm_multiset_dp` beside the existing k-pool subset oracle.
2. Run parity against k-pool subset DP and brute force on a larger adversarial
   corpus.
3. Add duplicate-heavy benchmark output to the existing cross-pool benchmark.
4. Add a Lean or lightweight proof note for the amount-identity quotient:

```text
same amount and same reserve state -> same transition set
```

The interpretation is simple: in this modeled oracle, duplicate exact-in
intents have no behaviorally relevant identity, so count vectors are sufficient.
