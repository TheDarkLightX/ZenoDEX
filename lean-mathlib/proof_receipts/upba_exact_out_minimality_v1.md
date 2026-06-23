# UPBA Exact-Out Minimality V1 Receipt

Date: 2026-05-15

## Accepted Artifact

`lean-mathlib/Proofs/UniformBatchExactOutMinimality.lean`

## Main Theorem

```text
UniformBatchExactOutMinimality.minimalGrossForOut_satisfies_and_minimal
```

For a positive uniform price ratio and `fee_bps < 10000`, the UPBA v3 exact-out
gross-input formula is sufficient and minimal at that fixed price. The proof
combines:

- price-side required net input:
  `requiredNetForOut = ceil(amount_out * price_den / price_num)`;
- fee-side gross-up:
  `minimalGrossForNet = ceil(required_net * 10000 / (10000 - fee_bps))`;
- deterministic post-fee net identity inherited from
  `Proofs.CpmmSwapV8ExactOutMinimality`.

## Replay

```bash
cd lean-mathlib
lake build Proofs.UniformBatchExactOutMinimality Proofs.UniformBatchOptimality
```

Result: passed locally on 2026-05-15.

The aggregate check:

```bash
cd lean-mathlib
lake build Proofs
```

Result: passed locally on 2026-05-15 after repairing unrelated proof hygiene
issues in the aggregate import set.

## Boundaries

This proof does not claim:

- price-grid economic sufficiency;
- fair inclusion;
- CPMM reserve feasibility;
- partial exact-out fills;
- multi-hop routing;
- unbounded rational-price optimality.

Two Aristotle proof-search packets were submitted as independent checks:

- `04980b35-4ee8-4f73-86d4-736f7a469c48`: fee gross-up minimality.
- `d5931f45-a542-49bb-a9cd-1148fec8a252`: price-side required-net minimality.

Both later returned with Aristotle platform status `COMPLETE_WITH_ERRORS`, but
the downloaded proof packets contain complete Lean proofs for the target theorem
surfaces. Local replay passed:

```bash
cd internal/aristotle/results/04980b35/unpacked/upba_exact_out_minimal_input_v1_aristotle
lake build
rg -n '\b(sorry|admit|axiom|unsafe|sorryAx)\b' AristotleTask.lean

cd internal/aristotle/results/d5931f45/unpacked/upba_exact_out_price_required_net_v1_aristotle
lake build
rg -n '\b(sorry|admit|axiom|unsafe|sorryAx)\b' AristotleTask.lean
```

Result: both packets build locally and the trust scans on `AristotleTask.lean`
have no matches.

Integration decision: accept both Aristotle packets as corroborating evidence.
Keep `lean-mathlib/Proofs/UniformBatchExactOutMinimality.lean` as the canonical
artifact because it is already integrated with the repo's CPMM exact-out fee
lemmas and proves the combined fixed-price gross-input theorem:

```text
UniformBatchExactOutMinimality.minimalGrossForOut_satisfies_and_minimal
```
