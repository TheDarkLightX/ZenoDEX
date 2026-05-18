# Spot Risc0 Proof Smoke, 2026-05-18

This receipt records the expanded ZenoDEX spot v1 Risc0 proof smoke after
adding add-liquidity and remove-liquidity to the guest transition scope, and
after binding each real proof smoke case to a ZenoLedger body, header, and proof
metadata artifact. The latest run also binds ordered ingress facts, pre/post
nonce roots, and accepted-receipt roots into the Risc0 journal and ZenoLedger
proof metadata.

Run context:

- Date: 2026-05-18
- Git HEAD at run: `263cb670eff12beefa31c735949a012775bd79a0`
- Working tree status: dirty. This is local checkout evidence, not a clean
  release tag claim.
- Real-proof report:
  `/tmp/zenodex_risc0_real_proof_smoke_all_nonce_receipt/real_proof_smoke_report.json`
- Risc0 image id:
  `a8c9d649329faae9107b4f6c5ad02866c90a157896f2fa7f6eb128b8c5d55245`

## Scope

The smoke generated and host-verified non-empty Risc0 receipts for seven cases:

- `empty`
- `faucet_mint`
- `create_pool`
- `swap_exact_in`
- `add_liquidity`
- `remove_liquidity`
- `spot_block_liquidity_cycle`

The combined `spot_block_liquidity_cycle` case proves one multi-transaction
block with create-pool, add-liquidity, swap-exact-in, and remove-liquidity. It
binds state hash, transaction commitment, pre-app hash, post-app hash, and block
timestamp through the CLI verifier.

The non-empty cases carry transaction nonces. The guest checks per-sender nonce
sequencing from an empty starting nonce map in these fixtures. The combined
liquidity-cycle block uses sender nonces `0, 1, 2, 3`.

Each case also emits:

- `{case}_zeno_ledger_body.json`
- `{case}_zeno_ledger_header.json`
- `{case}_risc0_proof_metadata.json`

The archived smoke report records `ledger_binding.ok = true`,
`header_bound = true`, `body_checked = true`, `post_state_root_checked = true`,
and `pre_state_root_checked = true` for all seven cases. The archive checker
now loads the emitted proof/body/header/metadata files and rejects tampering
that breaks header/body roots, proof-metadata/header binding, proof envelope to
metadata rebuild, or report-to-artifact field equality. The metadata rebuild
also binds `ingress_commitment`, `pre_nonce_root`, `post_nonce_root`, and
`accepted_receipts_root`.

## Commands

```bash
CARGO_TARGET_DIR=/tmp/zenodex_risc0_target \
  cargo test --manifest-path zk/state_proof_risc0/Cargo.toml \
  -p tau-state-proof-risc0-shared

CARGO_TARGET_DIR=/tmp/zenodex_risc0_target \
  cargo check --manifest-path zk/state_proof_risc0/Cargo.toml \
  -p tau-state-proof-risc0-cli

RISC0_FORCE_BUILD=1 CARGO_TARGET_DIR=/tmp/zenodex_risc0_force_target \
  cargo check --manifest-path zk/state_proof_risc0/Cargo.toml \
  -p tau-state-proof-risc0-cli

python3 tools/zeno_ledger_risc0_real_proof_smoke.py \
  --case all \
  --timeout 180 \
  --out-dir /tmp/zenodex_risc0_real_proof_smoke_all_nonce_receipt \
  --target-dir /tmp/zenodex_risc0_force_target

python3 tools/check_zeno_ledger_risc0_real_proof_smoke_report.py \
  /tmp/zenodex_risc0_real_proof_smoke_all_nonce_receipt/real_proof_smoke_report.json \
  --require-proof-files \
  --pretty

pytest -q \
  tests/integration/test_zeno_ledger_risc0_proof_metadata.py \
  tests/test_check_zeno_ledger_risc0_real_proof_smoke_report.py

pytest -q \
  tests/integration/test_risc0_shared_fixture_equivalence.py \
  tests/test_check_zeno_ledger_risc0_real_proof_smoke_report.py

python3 tools/check_zeno_ledger_proof_coverage_matrix.py --pretty
```

## Observed Results

- Rust shared crate: `11 passed`
- CLI placeholder build: passed
- CLI real-method build with `RISC0_FORCE_BUILD=1`: passed
- Real-proof smoke: `ok: true`, `case_count: 7`
- Smoke report checker: `ok: true`, `status: accepted`, all seven
  `ledger_binding_ok = true`
- Metadata/report checker tests: `21 passed`
- Python fixture/metadata/report focused tests: `28 passed`
- Proof coverage matrix: `ok: true`, `status: accepted`

Case post-app hashes:

- `empty`: `97e32b9e75aa599a226b74b32f9606d2eb60f4172266b181a26bc8d6c4a6d257`
- `faucet_mint`: `d709945d069b56e81108dd4352275c69cd8a85317eb113ef81b9191aad0426b5`
- `create_pool`: `cdedb50a4a2388af0f479062e0ea6d5288b7c460b55237c419b46fc5dd7b6f75`
- `swap_exact_in`: `168c616c3e9cbc832f9accf6022fcf5153f4611de71115e36a6e540a1230101b`
- `add_liquidity`: `671803d43d456dc0f418cf97700be3d13219c31ff98fa8253545deb6fb04ae4a`
- `remove_liquidity`: `15ba48c3948611ea40af205be1f3186b17f34b77dcf8f88c3d8649dbf7f121ba`
- `spot_block_liquidity_cycle`: `b158b93aae996b95f760edc8ac5003c79a6b93eeb821255248059360bb9410c6`

## Residual Limits

This closes the current supported spot v1 proof smoke over create-pool,
swap-exact-in, add-liquidity, remove-liquidity, faucet mint, and one combined
block fixture. It also closes the local archive binding from each proof envelope
to a ZenoLedger body/header/proof-metadata triplet, and closes successful-lane
nonce sequencing plus accepted-receipt root emission for the supported spot v1
transactions. It still does not claim exact-out, multi-hop routing, UPBA batch
clearing, rejected receipt execution, full production ingress semantics, full
Python-runtime equivalence, recursive aggregation, or production network
readiness.
