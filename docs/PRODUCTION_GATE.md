## Production readiness gate (local)

This repo includes a single “production gate” script that runs the same checks we treat as launch-blocking:

- Python unit tests
- Kernel spec assurance (manifest-backed)
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
- Trivy finds **0 HIGH/CRITICAL vulnerabilities with available fixes** in the final image artifact.

### Notes

- Docker builds are run with `docker build --network=host` to avoid DNS flakiness in some environments.
- Trivy is downloaded into `tools/_secbin/` if not already present.
