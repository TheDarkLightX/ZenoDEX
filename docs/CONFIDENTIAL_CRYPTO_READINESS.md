# Confidential Crypto Readiness

This repo tracks four confidential-cryptography surfaces separately:

- TEE attestation and confidential-extension receipts
- encrypted SSS wallet backup
- secure multiparty computation
- FHE sealed-bid planning

`src/integration/confidential_crypto_readiness.py` builds a structured readiness
report for those surfaces. The report is conservative by design. A configured
external verifier, local encrypted SSS fixture, MPC placeholder, or FHE alpha
planner does not become a production cryptography claim.

Operators and CI can emit the report with:

```bash
python3 tools/check_confidential_crypto_readiness.py
```

Use `--require-production-ready` when a release gate should fail unless every
surface is production-ready and host-independent.

The public release gate currently uses `--require-non-production-ready`. That
keeps the default posture honest: the repo must continue reporting that the
confidential crypto stack is not production-ready until the missing evidence is
added deliberately.

## Current Status

TEE receipt admission is implemented as a deterministic in-repo boundary, but
vendor attestation verification is external. The repo can bind to an external
verifier command and hash that binding; it still does not prove AWS Nitro,
Azure Attestation, AMD SEV-SNP, or Intel TDX quote verification semantics.

Encrypted SSS backup is not a current runtime claim on `origin/main`. The
production key-management design treats Shamir material as backup and recovery
metadata, not as counted signing authority. The readiness checker can consume an
explicit encrypted-SSS status artifact if one is supplied, but the default repo
posture is `missing` and blocked. Production custody would require live delivery
evidence, replayed recovery, hostile-share replay checks, raw-material absence,
no server-side reconstitution, and signed external audit evidence.

MPC is not implemented. `mpc-placeholder` is treated as a placeholder and blocks
production readiness.

FHE is not implemented as runtime cryptography. The sealed-bid FHE lane is an
alpha planner with explicit fallback to commit/reveal.

## Promotion Rule

For a production claim, the readiness report must have:

```text
production_ready = true
host_independent_ready = true
readiness_gaps = []
```

Today the expected result is `false`. That is the correct result until vendor
TEE verification, audited SSS custody, real MPC, and production FHE backend
evidence are wired into the runtime evidence bundle.
