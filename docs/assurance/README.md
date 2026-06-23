---
title: Public Assurance Artifacts
type: note
permalink: autonomous-tau-dex-review/docs/assurance
---

# Public Assurance Artifacts

This directory is for release artifacts that can be committed without exposing
private proof-toolchain source.

ESSO is private. ZenoDEX can still publish ESSO-derived evidence by committing
hash-bound receipts generated from private ESSO runs. A receipt is acceptable
only when:

- it is produced from an `ok: true` private `tools/dex_kernel_assurance.py`
  report;
- it matches `tools/kernel_assurance_manifest.json`;
- it records the pinned ESSO commit hash, ESSO tree hash, solver versions,
  kernel hashes, corpus hashes, and deterministic verification fingerprints;
- it excludes ESSO source, private checkout paths, and raw files under
  `internal/`.

The private ESSO checkout may be dirty only when the computed ESSO tree hash
matches the manifest pin. Dirty filenames are not copied into the public
receipt.

Refresh command from a private machine:

```bash
mkdir -p internal/release_artifacts/kernel_assurance
python tools/dex_kernel_assurance.py --pretty \
  > internal/release_artifacts/kernel_assurance/private_report.json
python tools/check_kernel_assurance_public_receipt.py build \
  --report internal/release_artifacts/kernel_assurance/private_report.json \
  --out docs/assurance/kernel_assurance_public_receipt.json
python tools/check_kernel_assurance_public_receipt.py check --pretty
```

Public checkouts can then verify the receipt without private ESSO access:

```bash
python tools/check_kernel_assurance_public_receipt.py check --pretty
```
