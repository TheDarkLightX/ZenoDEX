# ZenoDEX Aristotle Math Completion Job v1

Status: submitted to Aristotle on 2026-05-06.

## Job

- Aristotle job id: `0570bfa8-e9e4-4951-91ef-9e02e7b715ea`
- Submission mode: `aristotle formalize`
- Local prompt packet:
  `experiments/aristotle_tasks/zenodex_math_completion_big_v1/zenodex_math_completion_problem_set_v1.md`

## Scope

The packet asks Aristotle for one broad Lean theorem ladder covering:

- verifier backend policy and ZenoProof admission;
- O5 independence and claim-DAG closure;
- ProofMining reward safety and claimability;
- ZenoOracle median, sync-window, and O3/O4/O5 receipt binding;
- settlement execution and live-economics budget bounds;
- CPMM/AMM swap arithmetic and exact-out candidate certificates;
- batch settlement, fee-split, LP accounting, and value conservation;
- perps margin, liquidation, and insurance-pool safety anchors;
- zUSD collateral/debt conservation and MCR anchors;
- FIRE/CAL certificate fail-closed acceptance;
- disaster-state axis coverage and cross-module assume/guarantee composition;
- backend-agnostic VM / zkVM / Wasm admission equivalence.

## Boundaries

The packet explicitly avoids claiming live market truth, external cryptographic
soundness, compiler correctness, or production network liveness. Those remain
external assumptions. The requested Lean work should model them as assumptions
and prove only the in-repo math surfaces and composition laws.

## Related Job

- Aristotle job id: `fb6f30df-0453-4b26-9d84-d7a8893b65d2`
- Scope: smaller exact Lean packet for ZenoProof / ProofMining verifier context
  and reward-gate arithmetic.

