# Production Traceability Matrix

This matrix maps key production-closure invariants to the runtime guards, tests,
and replay or formal evidence that currently support them. The machine-readable
source is `docs/production_traceability_matrix.json`.

Run:

```bash
python3 tools/check_production_traceability_matrix.py
```

Current entries:

| ID | Status | Runtime Guard | Evidence |
| --- | --- | --- | --- |
| `dex_nonce_replay_protection` | `supported` | Core nonce policy, deployment profile guard, and `apply_ops` nonce admission | `tests/integration/test_dex_engine_helpers.py`, `tests/integration/test_deployment_profiles.py`, `tests/core/test_dex_step.py` |
| `dex_strong_settlement_replay` | `supported` | Strong settlement replay validator | `tests/core/test_settlement_strong_validator.py`, `tests/integration/test_settlement_strong_certificate.py` |
| `dex_intent_normal_form_boundary` | `supported` | Parsed-intent normal-form gate with validated marker and unknown-field rejection | `tests/core/test_intent_normal_form.py`, operations parser/fuzz suites, `tests/integration/test_dex_engine_helpers.py` |
| `dex_deployment_profile_postures` | `supported` | Named local/public-testnet/production-strict deployment profiles | `tests/integration/test_deployment_profiles.py`, `tools/check_dex_deployment_profiles.py` |
| `upba_fixed_admission_price_grid` | `supported_scoped` | UPBA certificate and bounded price-grid evidence verifier | UPBA core and integration test suites |
| `zenoledger_public_testnet_rehearsal` | `supported_replay` | Public-testnet candidate gate, anti-equivocation check, bundle, dual-operator rehearsal, live-intake smoke | `tools/run_public_testnet_candidate_gate.sh`, `tools/check_zeno_ledger_anti_equivocation.py` |
| `zk_risc0_metadata_binding` | `supported_scoped` | RISC0 proof metadata root checks and verifier registry admission | `tests/integration/test_zeno_ledger_risc0_proof_metadata.py`, `tests/integration/test_zeno_ledger_verifier_registry_v0.py` |
| `tee_metadata_binding` | `supported_scoped` | TEE quote/policy metadata root checks and verifier registry admission | `tests/integration/test_zeno_ledger_tee_proof_metadata.py`, `tests/integration/test_zeno_ledger_verifier_registry_v0.py` |
| `oracle_critical_authorization` | `supported` | ZenoOracle routing and settlement authorization gates | `tests/integration/test_oracle_authorization_semantic_binding.py` |
| `proof_mining_claimability` | `supported` | Proof-mining claimability manager/runtime gates | Proof-mining core and integration suites |
| `api_surface_profiles` | `supported` | API bootstrap profile refuses unsafe demo/value-moving exposure | `tests/integration/test_api_surface_profiles.py` |

Residual limits remain part of the JSON entry for each invariant. A matrix entry
is an evidence map, not a mainnet-readiness claim by itself.
