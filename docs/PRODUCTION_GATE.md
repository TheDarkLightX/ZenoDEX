---
title: PRODUCTION_GATE
type: note
permalink: autonomous-tau-dex-review/docs/production-gate
---

## Production readiness gate (local)

This repo includes a single “production gate” script that runs the same checks we treat as launch-blocking:

- Kernel spec assurance (manifest-backed)
- Python unit tests
- UI dependency audit (`npm audit`)
- Build the production container image
- Scan the built artifact with Trivy (HIGH/CRITICAL with fixes)

### Run

From repo root:

```bash
bash tools/prod_gate.sh
```

Optional flags:

```bash
bash tools/prod_gate.sh --skip-docker
bash tools/prod_gate.sh --skip-ui
```

### What “pass” means

- Kernel assurance returns `ok: true` for **all kernels in** `tools/kernel_assurance_manifest.json`.
- The vendored ESSO package tree hash, git provenance hash, and solver versions match the manifest pin before any long-running verification starts.
- Trivy finds **0 HIGH/CRITICAL vulnerabilities with available fixes** in the final image artifact.

### Notes

- The gate runs kernel assurance before `pytest` so broken toolchain pins fail fast.
- Docker builds are run with `docker build --network=host` to avoid DNS flakiness in some environments.
- Trivy is downloaded into `tools/_secbin/` when missing or when the existing binary is not at the pinned version, and the pinned tarball checksum is verified before extraction.
- The UI audit gate parses `npm audit --json` and blocks only on high/critical findings or audit execution errors.
- If the vendored ESSO repo carries intentional local patches, update the manifest with the exact `esso_tree_sha256` after a successful assurance run instead of relying on a clean git checkout alone.