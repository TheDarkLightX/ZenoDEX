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
