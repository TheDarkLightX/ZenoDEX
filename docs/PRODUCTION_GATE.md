---
title: PRODUCTION_GATE
type: note
permalink: autonomous-tau-dex-review/docs/production-gate
---

## Production readiness gate (local)

This repo includes a single “production gate” script that runs the same checks we treat as launch-blocking:

- Kernel spec assurance (manifest-backed)
- Container hardening artifact checks
- Python unit tests
- UI dependency audit (`npm audit`)
- Build the production container image
- Scan the built artifact with Trivy (HIGH/CRITICAL with fixes)

### Run

From repo root:

```bash
bash tools/prod_gate.sh
```

For the ZenoLedger public-testnet rehearsal lane, run:

```bash
bash tools/run_public_testnet_candidate_gate.sh
```

That gate stores the local two-node smoke report under its temporary artifact
directory and validates the expected state-machine sequence before reporting
success.

For the value-moving production-boundary closure checklist, see
`docs/PRODUCTION_BOUNDARY_CLOSURE_AUDIT.md`. The replay command is:

```bash
python3 tools/check_production_boundary.py
```

For the local reproducibility audit, see `docs/REPRODUCIBILITY_AUDIT.md`. The
Python dependency replay command is:

```bash
python3 tools/check_python_hash_locks.py --json
```

Optional flags:

```bash
bash tools/prod_gate.sh --skip-docker
bash tools/prod_gate.sh --skip-ui
bash tools/prod_gate.sh --private-esso
bash tools/prod_gate.sh --public-kernel-receipt
bash tools/prod_gate.sh --kernel-receipt docs/assurance/kernel_assurance_public_receipt.json
```

### Private ESSO Boundary

ESSO is a private proof/toolchain dependency. It should not be vendored into
the public ZenoDEX repository or copied into release artifacts.

The production gate uses two modes:

- If `external/ESSO` exists, or `--private-esso` is passed, the gate runs
  `python tools/dex_kernel_assurance.py --pretty` and regenerates the
  manifest-backed kernel assurance report from the private toolchain.
- If ESSO is unavailable, the gate verifies a public receipt with
  `tools/check_kernel_assurance_public_receipt.py`. The default path is
  `docs/assurance/kernel_assurance_public_receipt.json`.

The public receipt contains only hashes, solver/toolchain pins, kernel IDs,
corpus statistics, and deterministic verification fingerprints. It explicitly
does not include ESSO source, private worktree paths, or raw private checkout
state.

To refresh the public receipt from a machine that has private ESSO access:

```bash
mkdir -p internal/release_artifacts/kernel_assurance
python tools/dex_kernel_assurance.py --pretty \
  > internal/release_artifacts/kernel_assurance/private_report.json
python tools/check_kernel_assurance_public_receipt.py build \
  --report internal/release_artifacts/kernel_assurance/private_report.json \
  --out docs/assurance/kernel_assurance_public_receipt.json
python tools/check_kernel_assurance_public_receipt.py check --pretty
```

Commit the refreshed public receipt only after the private report is
`ok: true`. Do not commit `external/ESSO` or files under `internal/`.

### What “pass” means

- Kernel assurance returns `ok: true` for **all kernels in** `tools/kernel_assurance_manifest.json`, either by regenerating with private ESSO or by verifying the hash-bound public receipt.
- Container hardening checks pass for compose, AppArmor, and Dockerfile runtime-user artifacts.
- The private ESSO package tree hash, git provenance hash, and solver versions match the manifest pin before any long-running verification starts.
- Trivy finds **0 HIGH/CRITICAL vulnerabilities with available fixes** in the final image artifact.

### Notes

- The gate runs kernel assurance before `pytest` so broken toolchain pins fail fast.
- Docker builds are run with `docker build --network=host` to avoid DNS flakiness in some environments.
- Trivy is downloaded into `tools/_secbin/` when missing or when the existing binary is not at the pinned version, and the pinned tarball checksum is verified before extraction.
- The UI audit gate parses `npm audit --json` and blocks only on high/critical findings or audit execution errors.
- If the private ESSO repo carries intentional local patches, update the manifest with the exact `esso_tree_sha256` after a successful assurance run instead of relying on a clean git checkout alone.
- Experimental Tau specs are checked by promotion metadata before they can be reviewed for runtime activation. The generated trace-report check runs in the public-testnet gate when `generated/tau_lang_optimization_traces/report.json` exists.
- Public-facing ZenoLedger node configs should pass `python3 tools/zeno_ledger_node.py preflight --config <config> --strict-exposure` before exposure. Strict mode rejects all-interface binds with testnet intake or faucet endpoints enabled. Testnet mutation endpoints support bearer auth via `write_auth_token_env`, and submission forwarding supports `submit_peer_auth_token_env`.
