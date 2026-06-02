# RISC0 Release Binary Artifacts - 2026-06-02

This checkout built the scoped RISC0 verifier CLI for the perps NP, zUSD, and
legacy spot proof surfaces.

```text
binary: zk/state_proof_risc0/target/release/tau-state-proof-risc0-cli
sha256: 221f9aa7e3067cdd73265f905e6b08630613fbe5e8897ff19b87a04d14019bf8
risc0_image_id: e3264d6a144237769bdc1af099c28200361a49346f49cdbddd9630828d9aa885
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
perps_np_risc0_smoke: /tmp/zenodex_perp_np_risc0_smoke_all_current3/perps_np_risc0_real_proof_smoke_report.json
zusd_risc0_smoke: /tmp/zenodex_zusd_risc0_smoke_all_current/zusd_risc0_real_proof_smoke_report.json
perps_np_runtime_smoke: /tmp/zenodex_perp_np_release_smoke_current2/perp_np_release_smoke_report.json
spot_risc0_smoke: /tmp/zenodex_spot_risc0_smoke_current/empty_tau_state_proof.json
```

The compiled binary lives under `target/`, which is ignored by the repository.
This manifest records the release binary identity so the artifact can be
rebuilt and checked before packaging or publishing.
