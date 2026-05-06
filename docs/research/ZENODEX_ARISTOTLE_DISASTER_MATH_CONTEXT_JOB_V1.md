# ZenoDEX Aristotle Disaster Math Context Job v1

Status: submitted to Aristotle on 2026-05-06.

## Job

- Aristotle job id: `d7939dbc-5a1f-4815-b721-fc649be415b1`
- Submission mode: `aristotle formalize`
- Local prompt packet:
  `experiments/aristotle_tasks/zenodex_disaster_math_context_v1/zenodex_disaster_math_context_v1.md`

## Intent

This job gives Aristotle additional mathematical context for reducing disaster
states across ZenoDEX, ZenoProof, and ZenoOracle. It asks Aristotle to choose
the formal objects and theorem shapes itself, rather than using a prescribed
encoding.

The packet emphasizes:

- unverified proof acceptance;
- binding drift across commitments, roots, receipts, and rewards;
- verifier policy, code identity, sandbox identity, and determinism drift;
- O5 independence spoofing;
- ZenoOracle median, freshness, diversity, and consumption binding failures;
- settlement conservation drift;
- CPMM/AMM overdelivery and rounding drift;
- exact-out route-selection failures;
- LP mint/burn accounting drift;
- perps margin, liquidation, funding, and insurance failures;
- zUSD collateral/debt failures;
- ProofMining duplicate reward and wrong-winner failures;
- FIRE/CAL certificate acceptance gaps;
- cross-module composition failures;
- disaster coverage gaps and minimal bad-state bases;
- backend-neutral VM / zkVM / Wasm verifier admission.

## Boundaries

The job asks Aristotle to keep cryptographic soundness, market truth, compiler
correctness, OS sandbox correctness, zkVM correctness, Wasm runtime correctness,
and production network liveness as explicit external assumptions.

## Related Aristotle Jobs

- `0570bfa8-e9e4-4951-91ef-9e02e7b715ea`: large ZenoDEX math completion theorem
  ladder.
- `fb6f30df-0453-4b26-9d84-d7a8893b65d2`: exact ZenoProof / ProofMining reward
  gate packet. Last observed status: complete.

