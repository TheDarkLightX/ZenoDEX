# RISC0 Release Binary Artifacts - 2026-06-02

This checkout built the scoped RISC0 verifier CLI for the perps NP, zUSD, and
legacy spot proof surfaces.

```text
binary: zk/state_proof_risc0/target/release/tau-state-proof-risc0-cli
sha256: 722196857f485ae88a6e2f4375b62db588964d0dcf85ad04a8b863f5c6628f22
risc0_image_id: 59b2fbf4ea477dac19bdeb3ac1f81437c37387a4048360818c8b7c82b03e85d0
production_security_claim: false
```

Rebuild command:

```bash
cd zk/state_proof_risc0
RISC0_FORCE_BUILD=1 cargo build --release -q -p tau-state-proof-risc0-cli
sha256sum target/release/tau-state-proof-risc0-cli
```

Release evidence:

```text
perps_np_risc0_smoke: internal/release_artifacts/risc0_perps_np_smoke/perps_np_risc0_real_proof_smoke_report.json
zusd_risc0_smoke: internal/release_artifacts/risc0_zusd_smoke/zusd_risc0_real_proof_smoke_report.json
perps_np_runtime_smoke: /tmp/zenodex_perp_np_release_smoke_current2/perp_np_release_smoke_report.json
spot_risc0_smoke: /tmp/zenodex_spot_risc0_smoke_current/empty_tau_state_proof.json
```

The compiled binary lives under `target/`, which is ignored by the repository.
This manifest records the release binary identity so the artifact can be
rebuilt and checked before packaging or publishing.
