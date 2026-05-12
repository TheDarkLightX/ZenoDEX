# ZenoDEX Proof Refinement Frontier

This document records the ZenoDEX-wide 1000-atom proof refinement campaign.
The replay tool is:

```bash
python3 tools/zenodex_proof_refinement_frontier.py --format text
```

To emit the full ranked 1000-atom JSON record:

```bash
python3 tools/zenodex_proof_refinement_frontier.py \
  --include-candidates \
  --output internal/runs/zenodex_proof_refinement_frontier_1000_20260512.json
```

The campaign was also run through Atom of Thoughts as ten 100-atom container
passes:

```text
ZDX-PRF-BATCH-0001-0100   CPMM kernel integer math
ZDX-PRF-BATCH-0101-0200   exact-out routing and candidate completeness
ZDX-PRF-BATCH-0201-0300   batch clearing and UPBA settlement
ZDX-PRF-BATCH-0301-0400   settlement certificate verification
ZDX-PRF-BATCH-0401-0500   oracle consumer runtime binding
ZDX-PRF-BATCH-0501-0600   perps margin, funding, and liquidation
ZDX-PRF-BATCH-0601-0700   zUSD redemption and MCR accounting
ZDX-PRF-BATCH-0701-0800   LP and vault share accounting
ZDX-PRF-BATCH-0801-0900   ZenoProof mechanism economics
ZDX-PRF-BATCH-0901-1000   evidence registry and replay discipline
```

Each individual atom is a hypothesis with a candidate ID, dependency list,
confidence, falsifier, evidence command, and promotion gate. A candidate becomes
verified only after the named evidence command and promotion gate pass.

## Receipt

```text
status = accepted
atom_iteration_count = 1000
candidate_count = 1000
dimensions = 10 lanes * 10 gap classes * 5 methods * 2 binding modes
```

## Top Promotion Targets

The frontier ranks all 1000 atoms, then selects a diverse top-ten queue so the
first cycle covers every major lane and every major gap class.

1. `PRF-0522`: Perps margin, funding, and liquidation candidate-generator
   completeness via Lean theorem, runtime-bound closure.
2. `PRF-0302`: Settlement certificate verifier runtime theorem binding via
   Lean theorem, runtime-bound closure.
3. `PRF-0112`: Exact-out routing integer rounding bridge via Lean theorem,
   runtime-bound closure.
4. `PRF-0244`: Batch clearing and UPBA settlement certificate totality via
   ESSO/SMT invariant, runtime-bound closure.
5. `PRF-0474`: Oracle consumer runtime resource-bound complexity via ESSO/SMT
   invariant, runtime-bound closure.
6. `PRF-0666`: zUSD redemption and MCR conservation/accounting identity via
   Python exact replay, runtime-bound closure.
7. `PRF-0054`: CPMM kernel generic canonical theorem refactor via ESSO/SMT
   invariant, runtime-bound closure.
8. `PRF-0734`: LP and vault share accounting compositional trace induction via
   ESSO/SMT invariant, runtime-bound closure.
9. `PRF-0986`: Evidence registry and replay snapshot/migration replay via
   Python exact replay, runtime-bound closure.
10. `PRF-0896`: ZenoProof mechanism economics negative-knowledge claim scope via
   Python exact replay, runtime-bound closure.

## Why These Are First

The top targets were selected because they combine high value movement, known
proof-to-runtime adapter debt, and direct evidence paths. The first promotion
cycle should prioritize:

```text
runtime binding -> integer bridge -> certificate totality -> trace induction
```

This sequence attacks the common failure mode where a proof is correct over its
model, while the runtime path consumes a different state, candidate set, witness,
or timestamp.

## Non-Claims

This frontier does not claim:

- the 1000 hypotheses are verified theorems;
- exhaustive ZenoDEX safety;
- global routing optimality;
- UPBA is deployed;
- ignored internal proofs are public assurance.

## Next Work Queue

The best immediate PR is `PRF-0302`, because settlement certificate verification
is the narrowest high-value runtime boundary. It should add a malformed/valid
certificate corpus, stable reject-order checks, and a theorem or proof note
tying `validate_operations` to the strong validator replay contract.

`PRF-0112` and `PRF-0522` should follow. They cover the two places where local
validity can diverge from global behavior: generated route candidates and
composed perps transitions.
