# ZenoDEX zUSD RISC0 Transition Proof v1

This document records the scoped RISC0 proof surface for the zUSD
collateral-deposit plus mint transition.

## Surface

- Proof type: `risc0.zenodex_zusd_transition.v1`
- Runtime stream surface: `zusd_stream11`
- Guest source: `zk/state_proof_risc0/methods/guest`
- Shared transition semantics: `zk/state_proof_risc0/shared/src/lib.rs`
- Host CLI: `zk/state_proof_risc0/cli` (`tau-state-proof-risc0-cli`)
- Strict live-wrapper verifier: `tools/proof_verifiers/risc0_zusd_live_wrapper_v1.py`
- Smoke tool: `tools/zeno_ledger_zusd_risc0_real_proof_smoke.py`

## Transition Semantics (v1 Scope)

The guest proves one zUSD single-vault transition:

1. Bind `chain_id`, `vault_id`, `owner_pubkey`, `pre_app_hash`,
   `post_app_hash`, `operation_hash`, oracle binding hash, pre/post zUSD state
   roots, and state-delta hash.
2. Validate the pre-state oracle shape, active/pending price relationship,
   debt conservation, debt floor, caps, fee bounds, and system solvency.
3. Apply one positive collateral deposit.
4. Apply one positive `mint_zusd` operation when the oracle is initialized,
   fresh, and has no pending-price mismatch.
5. Reject recovery-mode minting, stale/no oracle, pending-price mismatch,
   below-floor mint, debt cap breach, supply cap breach, MCR breach, broken
   debt conservation, wrong state roots, wrong app hashes, and wrong
   state-delta hash.
6. Bind the minted zUSD wallet balance, vault debt, free debt, protocol
   revenue, and borrow fee in the journal.

`pre_app_hash` and `post_app_hash` are scoped zUSD app hashes recomputed from
the proven zUSD state roots. They are not whole-runtime Python app hashes or
Merkle inclusion proofs for unrelated application state.

The oracle binding is carried as `oracle_binding_hash`; this proof does not
verify external oracle truth or source independence. Caller authorization is an
external precondition enforced by the runtime before proof submission.

## Journal

The committed journal is `ZusdTransitionJournalV1`. It includes:

- proof type and journal version;
- chain, vault, and owner identifiers;
- pre/post app hashes and pre/post zUSD state roots;
- operation hash, state-delta hash, and oracle binding hash;
- oracle epoch and active price;
- MCR/CCR parameters;
- deposit, principal mint, mint fee, and debt delta;
- collateral, debt, free debt, wallet zUSD balance, and protocol revenue
  values before/after;
- `mcr_ok`, `conservation_ok`, and `mint_balance_ok`.

The CLI verifier rejects a receipt unless the journal proof type matches this
surface and the receipt verifies against the embedded nonzero RISC0 image ID.
Optional `expected` fields are fail-closed binding checks for chain, vault,
owner, roots, operation, oracle, amount values, MCR fields, and image ID.

## Evidence

Local real-proof smoke command:

```bash
python3 tools/zeno_ledger_zusd_risc0_real_proof_smoke.py \
  --case all \
  --timeout 1800 \
  --out-dir internal/release_artifacts/risc0_zusd_smoke \
  --target-dir zk/state_proof_risc0/target
```

Observed on 2026-06-02:

- 1 positive real proof: 2000 zUSD-value collateral deposited,
  1000 zUSD minted, MCR satisfied, post-state root verified.
- 5 negative proof-generation failures: MCR breach, stale oracle, nonce
  replay, total debt mismatch, and wrong post-app hash.
- Strict verifier tamper rejection for wrong proof type, chain, image ID,
  post-state root, operation hash, and oracle binding hash.
- RISC0 image ID:
  `59b2fbf4ea477dac19bdeb3ac1f81437c37387a4048360818c8b7c82b03e85d0`.

The smoke report is written to:
`internal/release_artifacts/risc0_zusd_smoke/zusd_risc0_real_proof_smoke_report.json`.

## Current Non-Claims

This proof does not prove every zUSD command, multi-vault zUSD, redemptions,
repayments, liquidation, real external oracle truth, custody, production
finality, or the full Python runtime. It proves the scoped deposit-plus-mint
transition described above.

`production_security_claim` for this proof surface remains `false` until oracle
authority, production custody, artifact binding, runtime release wiring, and full
release gates pass.
