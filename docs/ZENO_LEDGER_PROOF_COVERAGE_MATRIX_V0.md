# ZenoLedger Proof Coverage Matrix V0

The proof coverage matrix records which ZenoLedger proof surfaces are currently
supported by public replay claims and which surfaces remain explicit gaps.

Run the matrix gate with:

```bash
python3 tools/check_zeno_ledger_proof_coverage_matrix.py --pretty
```

The checker loads [ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json](ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json),
checks every supported surface against `docs/claims_registry.yaml`, requires
the known proof gaps to remain listed, and rejects gap rows that carry a
`claim_id`.

Current supported surfaces cover:

- ZK/TEE metadata composition modeling;
- Risc0 spot-transition proof metadata adaptation;
- Rust/Python fixture equivalence for the current spot v1 transition scope,
  including create-pool, swap-exact-in, add-liquidity, and remove-liquidity;
- opt-in real Risc0 proof smoke for empty transition, faucet mint, create-pool,
  swap-exact-in, add-liquidity, remove-liquidity, and one multi-transaction
  spot liquidity-cycle block, with guest nonce sequencing, accepted-receipt
  roots, and emitted ZenoLedger body/header/proof-metadata bindings checked by
  the archive checker for `real_proof_smoke_report.json`;
- strict replay-bound range verification from one canonical anchor snapshot,
  with governed configuration binding, linked carried state, one deterministic
  execution per supported transaction body, and exact post-state-root and
  rejection-receipt checks. V0 rejects nonempty body-level
  `settlement_envelopes` because that effect surface has no governed replay
  executor;
- proof-required metadata gating as a structural diagnostic. The range verifier
  records a typed pending authority obligation and does not accept metadata or
  report booleans as cryptographic proof authority;
- proof-verification report replay;
- local light-client checkpoint quorum binding over a structural
  header/body/checkpoint diagnostic, signer-registry signature-set root, and BLS
  checkpoint quorum. This surface does not claim deterministic state replay.

Current explicit gaps cover consensus-bound proof-required authority, UPBA
v2/v3 proof execution, Oracle critical-action proof execution, zUSD proof
execution, perps proof execution, proof-market reward proof execution,
light-client state-transition replay, production light-client finality, and real
recursive epoch proof aggregation. The light-client gap is now specifically
production validator rotation, fork-choice, slashing, peer discovery, and
adversarial network finality.

This matrix is a scope-control artifact. It does not add zkVM execution support
for the listed gaps.
