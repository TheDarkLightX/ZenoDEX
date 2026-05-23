# Dependency Audit 2026-05-19

Status: refreshed dependency-audit evidence for the locked Python, DEX UI, and
RISC Zero dependency surfaces.

## Commands

```bash
/tmp/zenodex-pip-audit-venv-20260519/bin/python -m pip_audit -r requirements-core.lock.txt
/tmp/zenodex-pip-audit-venv-20260519/bin/python -m pip_audit -r requirements-agents.lock.txt
/tmp/zenodex-pip-audit-venv-20260519/bin/python -m pip_audit -r requirements-dev.lock.txt
python3 tools/check_dex_ui_dependency_audit.py
python3 tools/check_risc0_dependency_audit.py --no-fetch
python3 tools/check_dependency_pinning_status.py
python3 tools/check_python_hash_locks.py --json
```

## Results

| Surface | Result | Notes |
|---|---|---|
| Python core lock | Clean | `pip-audit` reported no known vulnerabilities. |
| Python agents lock | Clean | `urllib3` was refreshed from `2.6.3` to `2.7.0`, closing `CVE-2026-44431` and `CVE-2026-44432`. |
| Python dev lock | Clean | The dev lock now inherits `urllib3==2.7.0`; `pip-audit` reported no known vulnerabilities. |
| DEX UI npm lock | Clean | Removed unused `ethers`, which removed the transitive vulnerable `ws` path. |
| RISC Zero state-proof workspace | Clean for RustSec vulnerabilities | `cargo audit --no-fetch` still reports warning IDs `RUSTSEC-2024-0388`, `RUSTSEC-2024-0436`, and `RUSTSEC-2025-0141`, but no vulnerability IDs. |

## Gate Updates

- `.github/workflows/dependency-assurance.yml` now audits
  `requirements-core.lock.txt`, `requirements-agents.lock.txt`, and
  `requirements-dev.lock.txt` instead of the unhashed convenience
  `requirements.txt`.
- `docs/dependency_pinning_status.json` was refreshed with the new SHA-256
  hashes for the changed lock artifacts.
- `tools/check_python_hash_locks.py` accepts reordered `pip-compile` flags as
  long as the generated lockfile header still records `pip-compile` and
  `--generate-hashes`.

## 2026-05-23 RISC Zero Follow-Up

The RISC Zero state-proof workspace was moved from the RISC Zero `1.2` line to
`2.3` and wired to the repo-local `ark-relations 0.5.1` patch. The patch keeps
the arkworks API version expected by RISC Zero while lifting
`tracing-subscriber` to the patched `0.3` line.

Current evidence:

```bash
(cd zk/state_proof_risc0 && cargo audit --json)
python3 tools/check_risc0_dependency_audit.py --no-fetch
(cd zk/state_proof_risc0 && RISC0_SKIP_BUILD=1 cargo check --workspace)
(cd zk/state_proof_risc0 && RISC0_SKIP_BUILD=1 cargo test -p tau-state-proof-risc0-shared -p tau-state-proof-risc0-cli)
python3 -m pytest -q tests/integration/test_check_risc0_dependency_audit.py
python3 -m pytest -q tests/integration/test_risc0_shared_fixture_equivalence.py tests/integration/test_zeno_ledger_risc0_proof_metadata.py tests/test_check_zeno_ledger_risc0_real_proof_smoke_report.py
```

Result: `cargo audit` reports no vulnerability IDs for the workspace. It still
reports unmaintained-warning IDs for `bincode`, `derivative`, and `paste`.
`tools/check_risc0_dependency_audit.py` now has an empty default allowlist, so a
future RustSec vulnerability fails closed unless an explicit temporary
`--allow` is supplied.

`cargo test --workspace` remains the wrong host-side gate for this workspace
because it tries to execute the RISC Zero guest binary directly on the host. Use
`cargo check --workspace` plus the host package tests listed above unless the
RISC Zero guest target is installed and the guest is being executed through the
prover path.
