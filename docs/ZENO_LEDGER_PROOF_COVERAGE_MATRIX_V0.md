# ZenoLedger Proof Coverage Matrix V0

The proof coverage matrix records which ZenoLedger proof surfaces are currently
supported by public replay claims and which surfaces remain explicit gaps.

Run the matrix gate with:

```bash
python3 tools/check_zeno_ledger_proof_coverage_matrix.py --pretty
```

Run the stricter full-zk readiness gate with:

```bash
python3 tools/check_zeno_ledger_proof_coverage_matrix.py --require-full-zk --pretty
```

That stricter gate is expected to fail today. It returns nonzero until every
listed value-moving surface is `covered` with no `gap_surface_ids` and no
required non-claims.

The checker loads [ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json](ZENO_LEDGER_PROOF_COVERAGE_MATRIX_V0.json),
checks every supported surface against `docs/claims_registry.yaml`, requires
the known proof gaps to remain listed, and rejects gap rows that carry a
`claim_id`. It also checks `full_zk_value_moving_surfaces` so each value-moving
surface has explicit proof-surface or gap-surface references.

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
- proof-required range replay;
- proof-verification report replay;
- local light-client checkpoint quorum replay that binds verified
  header/body/checkpoint replay to a signer-registry signature-set root and BLS
  checkpoint quorum;
- recursive lifecycle asset-delta row coverage for the current spot, zUSD
  DepositMint, and perps NP recursive leaf surfaces, with CLI row-root metadata
  binding and a Tau-compatible lifecycle admission gate;
- deterministic recursive lifecycle admission packet checking that recomputes
  row roots, checks aggregate conservation, authority roots, header roots,
  transcript binding, supported profile flags, and emits the same
  Tau-compatible admission booleans.

Current explicit gaps cover complete spot-block proof execution, UPBA v2/v3
proof execution, Oracle critical-action proof execution, zUSD proof execution,
perps proof execution, proof-market reward proof execution, production
light-client finality, and real recursive epoch proof aggregation. The
light-client gap is now specifically production validator rotation, fork-choice,
slashing, peer discovery, and adversarial network finality. The recursive
scaling gaps are specifically oracle recursive leaf coverage, complete
non-deposit-mint zUSD lifecycle row extraction, and production runtime admission
over real root proofs, header binding, data availability, and source-finality
certificates.

The full-zk value-moving matrix currently has eight entries:

| Surface | Status | Blocking gap ids |
| --- | --- | --- |
| Spot v1 complete block execution | `covered_scoped` | `spot_complete_block_real_proof` |
| UPBA execution | `open` | `uniform_batch_upba_v2_v3_real_proof` |
| Oracle critical-action execution | `open` | `oracle_critical_action_real_proof`, `recursive_oracle_leaf_real_proof` |
| zUSD lifecycle execution | `covered_scoped` | `zusd_lifecycle_real_proof`, `zusd_non_deposit_mint_lifecycle_rows` |
| Perps settlement execution | `covered_scoped` | `perps_settlement_real_proof` |
| Proof-market reward execution | `open` | `proof_market_reward_real_proof` |
| Recursive epoch and production admission | `covered_scoped` | `recursive_epoch_real_proof`, `recursive_production_admission` |
| Production light-client finality for value-moving admission | `covered_scoped` | `light_client_production_finality` |

This matrix is a scope-control artifact. It does not add zkVM execution support
for the listed gaps.
