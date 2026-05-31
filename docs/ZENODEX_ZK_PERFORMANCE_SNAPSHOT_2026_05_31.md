# ZenoDEX ZK Performance Snapshot, 2026-05-31

This is a local smoke measurement for the current Risc0 spot v1 proof path. It
is not a production prover benchmark.

Host: private local developer workstation. Specific hardware details are not
part of the public artifact.

Measured release-binary commands:

```bash
RISC0_FORCE_BUILD=1 CARGO_TARGET_DIR=/tmp/zenodex_risc0_release_target cargo build --manifest-path zk/state_proof_risc0/Cargo.toml --release -q -p tau-state-proof-risc0-cli
python3 tools/zeno_ledger_risc0_real_proof_smoke.py --case empty --timeout 240 --out-dir /tmp/zenodex_risc0_release_empty --target-dir /tmp/zenodex_risc0_release_target --cli-bin /tmp/zenodex_risc0_release_target/release/tau-state-proof-risc0-cli
python3 tools/zeno_ledger_risc0_real_proof_smoke.py --case swap_exact_in --timeout 240 --out-dir /tmp/zenodex_risc0_release_swap_exact_in --target-dir /tmp/zenodex_risc0_release_target --cli-bin /tmp/zenodex_risc0_release_target/release/tau-state-proof-risc0-cli
```

Results:

| Case | Runner | Generate | Verify | Total | Proof base64 chars |
| --- | --- | ---: | ---: | ---: | ---: |
| `empty` | release CLI | 46.101s | 0.066s | 46.167s | 358,612 |
| `swap_exact_in` | release CLI | 76.913s | 0.032s | 76.945s | 376,276 |

The first debug smoke was slower for verification because it used `cargo run`
without `--release`. The Docker/local-testnet path builds and runs the release
CLI, which explains why prior Docker tests could be much faster.

Coverage from `tools/measure_zenodex_zk_transition_coverage.py`:

- Proof operation coverage: 7 of 11 listed spot-v1 operation families, 63.64%.
- Current real Risc0 scope: `empty_transition`, `faucet_mint`, `create_pool`,
  `swap_exact_in`, `add_liquidity`, `remove_liquidity`,
  `liquidity_cycle_block`.
- Not covered by that proof scope: `swap_exact_out`, `multi_hop`,
  `rejected_receipt_execution`, `native_asset_sync`.
- Proof matrix scope: 7 supported surfaces and 7 explicit gap surfaces, 50%.

Conclusion: the current proof path is promising for async receipts, batch proof
publication, audit proofs, and light-client compression. Mandatory proof
generation on the user-facing admission path still needs warm p95/p99
benchmarks on target prover hardware. Release-mode verification is cheap in
these samples, so proof-backed validation can reduce host trust once each
critical transition has real proof coverage.
