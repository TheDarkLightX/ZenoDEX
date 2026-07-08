---
title: 2026-07-07-python-lock-security-refresh
type: note
permalink: autonomous-tau-dex-review/docs/dependency-approvals/2026-07-07-python-lock-security-refresh
---

# 2026-07-07 Python lock security refresh

## Change

- Refreshed `requirements-agents.lock.txt` and `requirements-dev.lock.txt` with
  `pip-compile --generate-hashes`.
- Upgraded vulnerable transitive packages in the agent/dev surface:
  `cryptography`, `idna`, `msgpack`, `pip`, `pydantic-settings`, `pyjwt`,
  `python-multipart`, `starlette`, and `urllib3`.
- Left `requirements-core.lock.txt` unchanged; the release audit reported no
  known vulnerabilities for the runtime core lock.

## Why

- `tools/run_release_gate.sh` failed at the final dependency audit because
  `pip-audit` reported known vulnerabilities in the agent/dev locks.
- The refresh keeps the release gate fail-closed and preserves hash-locked
  installs.

## Security Impact

- Runtime core dependencies are unchanged.
- Agent and developer dependency locks now pin fixed versions with SHA-256
  hashes.
- The primary supply-chain risk is compatibility drift in agent/dev-only tools;
  validate with `tools/check_python_hash_locks.py`, `pip-audit`, and the release
  gate before promotion.

## Rollback

- Revert this note plus the two lockfile changes.
- Rerun `pip-audit` on all three lock files.
- Do not promote the rollback unless the dependency audit is clean or an
  explicit vulnerability exception is approved separately.
