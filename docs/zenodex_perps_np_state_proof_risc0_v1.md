# ZenoDEX Perps NP RISC0 Transition Proof v1

This document records the scoped RISC0 proof surface for the dynamic N-party
perps clearinghouse.

## Surface

- Proof type: `risc0.zenodex_perps_np_transition.v1`
- Guest source: `zk/state_proof_risc0/methods/guest`
- Shared transition semantics: `zk/state_proof_risc0/shared/src/lib.rs`
- Host CLI: `zk/state_proof_risc0/cli` (`tau-state-proof-risc0-cli`)
- Strict live-wrapper verifier: `tools/proof_verifiers/risc0_perps_np_live_wrapper_v1.py`
- Smoke tool: `tools/zeno_ledger_perp_np_risc0_real_proof_smoke.py`

## Transition Semantics (v1 Scope)

The guest proves one perps NP epoch transition over dynamic participants:

1. Canonicalize accounts and require at least four participants.
2. Bind `chain_id`, `market_id`, `pre_app_hash`, `post_app_hash`,
   `operation_hash`, oracle binding hash, participant-set hash, pre/post state
   roots, and state-delta hash.
3. Validate net-zero positions, two-ledger conservation, and insurance ledger
   identity before settlement.
4. Settle the old book before matching new intents.
5. Match intents inside the guest with deterministic largest-remainder
   rationing. Host-supplied fills are not accepted.
6. Apply deterministic zero-funding liquidation, insurance draws,
   realized-profit haircut, and ADL rebalancing when settlement creates bad
   debt.
7. Reject duplicate intent nonces, expired intents, wrong participant set,
   wrong state roots, wrong state-delta hash, insolvent ADL, and nonzero
   funding.
8. Validate post-transition net-zero positions, conservation, insurance ledger,
   and maintenance margin.

Funding is intentionally fail-closed to `0` in this v1 surface. The Python
runtime currently disables nonzero operator-set funding for the same reason:
nonzero funding needs a separately bound funding source.

`pre_app_hash` and `post_app_hash` are scoped perps app hashes recomputed from
the proven perps state roots. They are not whole-runtime Python app hashes or
Merkle inclusion proofs for unrelated application state.

## Journal

The committed journal is `PerpsNpTransitionJournalV1`. It includes:

- proof type and journal version;
- chain and market identifiers;
- pre/post app hashes and pre/post perps state roots;
- operation hash, state-delta hash, oracle binding hash, participant-set hash,
  and receipts root;
- fee-pool, insurance, and claims-paid ledger values before and after the
  transition;
- participant, intent, and filled-intent counts;
- epoch before/after, clearing price, settle price, and funding rate;
- `net_zero_ok`, `conservation_ok`, and `insurance_ok`.

The CLI verifier rejects a receipt unless the journal proof type matches this
surface and the receipt verifies against the embedded nonzero RISC0 image ID.
Optional `expected` fields are fail-closed binding checks for chain, market,
roots, operation, oracle, participant set, counts, prices, ledger values, and
image ID.

## Evidence

Local real-proof smoke command:

```bash
python3 tools/zeno_ledger_perp_np_risc0_real_proof_smoke.py \
  --case all \
  --timeout 1800 \
  --out-dir internal/release_artifacts/risc0_perps_np_smoke \
  --target-dir zk/state_proof_risc0/target
```

Observed on 2026-06-02:

- 4 positive real proofs: four-wallet epoch, five-wallet epoch,
  settlement-driven liquidation/ADL epoch, and a reject-path/oracle-clamp epoch
  with `REJ_MARGIN`, `REJ_POS_BOUND`, `REJ_PRICE`, `REJ_SUPERSEDED`, and one
  zero-delta min-fill revocation.
- 7 negative proof-generation failures: participant floor, duplicate nonce,
  expired intent, wrong post-state root, nonzero funding, negative ledger
  field, and epoch overflow.
- Strict verifier tamper rejection for wrong proof type, chain, image ID,
  pre/post app hashes, pre/post roots, operation hash, oracle binding hash,
  participant-set hash, state-delta hash, and fee/insurance/claims ledger
  fields.
- RISC0 image ID:
  `59b2fbf4ea477dac19bdeb3ac1f81437c37387a4048360818c8b7c82b03e85d0`.

The smoke report is written to:
`internal/release_artifacts/risc0_perps_np_smoke/perps_np_risc0_real_proof_smoke_report.json`.

## Current Non-Claims

This proof does not prove real external oracle truth, custody, production
finality, every perps wallet action, or the full Python runtime. It proves the
scoped NP epoch transition described above.

`production_security_claim` for this proof surface remains `false` until oracle
authority, production custody, artifact binding, and runtime release gates pass.
