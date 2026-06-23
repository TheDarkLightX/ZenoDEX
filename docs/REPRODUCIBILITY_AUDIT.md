---
title: REPRODUCIBILITY_AUDIT
type: note
permalink: autonomous-tau-dex-review/docs/reproducibility-audit
---

# Reproducibility Audit

This note records the local reproducibility controls that are currently enforced
from source.

## Python Dependencies

```text
PythonInstallSurfaceOK :=
  RootLockfilesHashComplete
  ∧ RootInstallsUseRequireHashes
  ∧ NoUnlockedRootRequirementInstalls
  ∧ EveryOtherPipInstallIsAllowlisted
```

Plain-English reading: repo Python dependencies install from hash-complete root
lockfiles, and every scanned unhashed Python install command is either rejected
or named as an exception in the audit output.

Replay:

```bash
python3 tools/check_python_hash_locks.py --json
pytest -q tests/test_check_python_hash_locks.py
```

The current audit covers the production `Dockerfile`, root README install
commands, GitHub workflows, security docs, Tau local-node docs, tool docs, and
supported shell/Python tools. The JSON report exposes `pip_install_commands`,
`root_dependency_commands`, and `allowlisted_unhashed_install_commands`.

Current allowlisted unhashed installs are outside the production image and
release gate:

- optional local Tau Testnet checkout dependencies under `external/tau-testnet`
- optional GPU backend installation suggestions printed by `tools/gpu_env_check.py`
- remote ESSO experiment bootstrap packages in `tools/runpod_esso.py`
- optional PyInstaller dependency for native oracle bundle building

## Proof Toolchain Lock

```text
ProofToolchainLockOK :=
  PythonLocks ∧ DockerFiles ∧ LeanManifests ∧ Risc0CargoLocks ∧ TeeRustLocks
```

The proof-toolchain lock manifest hashes the Python lockfiles, Docker build
files, Lean toolchain/lake manifests, Risc0 Cargo manifests and lockfile, and
Rust TEE verifier manifests and lockfile. ZenoLedger proof metadata builders
carry the resulting `toolchain_lock_hash`.

Replay:

```bash
python3 tools/check_proof_toolchain_lock.py --json
pytest -q tests/test_check_proof_toolchain_lock.py
pytest -q tests/integration/test_zeno_ledger_risc0_proof_metadata.py \
  tests/integration/test_zeno_ledger_tee_proof_metadata.py
```

## Boundary

These controls are local source and manifest checks. They do not prove that a
live remote machine executed the same binaries, that optional external checkouts
are hash-locked, or that a latest-main two-machine run has been completed.
