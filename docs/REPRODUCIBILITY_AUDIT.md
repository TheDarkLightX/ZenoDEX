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

Risc0ActivationEligible :=
  CompleteSourceManifestInventory
  ∧ EveryGovernedRequirementIsExactlyEq3_0_6
  ∧ EveryGovernedCoreLockResolvesOnly3_0_6
  ∧ RegistryChecksumsPresent
  ∧ DirectProductionFeaturePolicy
  ∧ NoQuarantinedWorkspace
```

The proof-toolchain lock manifest hashes the Python lockfiles, Docker build
files, Lean toolchain/lake manifests, every discovered source Risc0 workspace
manifest and lockfile, and Rust TEE verifier manifests and lockfile. The Risc0
policy independently parses dependency declarations and lock packages. It
rejects ranged governed versions, mixed core-package versions, missing registry
checksums, unsafe host/guest feature shapes, malformed manifests, and unknown
legacy workspaces. ZenoLedger proof metadata builders carry the resulting
`toolchain_lock_hash`.

The current source inventory is internally valid and activation remains
blocked. `zk/state_proof_risc0` resolves Risc0 1.2.6 and is the single named
historical quarantine for `GHSA-jqq4-c7wq-36h7`. It has authority `NONE` and is
ineligible for governed release, settlement, claim promotion, or production
admission. The command below therefore exits 1 with
`status=blocked_quarantined_legacy` until that workspace is replaced by a
reviewed 3.0.6 release or removed from every authority path.

Expanding the manifest from one legacy workspace to the complete discovered
Risc0 source set changes `toolchain_lock_hash`. Historical metadata remains
historical and cannot be relabeled under the new lock root.

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
are hash-locked, that Cargo exercised every target-specific feature edge, or
that a latest-main two-machine run has been completed.
