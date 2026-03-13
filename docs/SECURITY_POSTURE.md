# Security Posture

This document records a few intentional hardening choices in the runtime and why
they exist. The goal is to make the repo's security posture inspectable from
source, not inferred from tribal knowledge.

## Runtime Boundaries

- The primary semantic acceptance gate is the strong settlement validator in
  `src/core/` and `src/integration/validation.py`.
- Tau is an additional, fail-closed verification layer for specific bounded
  checks. It is not the sole runtime authority.
- Demo APIs under `src/integration/api_server.py`, `src/integration/perps_api.py`,
  and `src/integration/zusd_api.py` are development surfaces, not the production
  transaction path.

## Hardening Decisions

### No `assert` on exposed runtime or signing paths

`assert` statements disappear under `python -O`. On trust boundaries we want an
explicit, fail-closed decision rather than an optimization-dependent check.

Applied to:
- BLS signature verification paths
- proof-verifier subprocess setup
- Tau subprocess setup
- demo API request parsing / state-transition glue

Reasoning:
- Failures on these paths should surface as deterministic rejections or explicit
  misconfiguration errors.
- They should never depend on interpreter optimization flags.

### Canonical encoding for hash/signature inputs

Hash inputs must use the shared canonical encoder in `src/state/canonical.py`.

Applied to:
- agent-side intent ID generation
- policy-artifact serialization helpers

Reasoning:
- Mixed encoders create drift between signing, hashing, receipts, and replay
  validation.
- The shared encoder rejects floats and invalid Unicode scalar values, which
  removes ambiguous or implementation-defined hash inputs.

### Fail-closed external tool resolution

The zUSD Tau gate now defaults `ZUSD_TAU_ALLOW_PATH_LOOKUP=false`.

Reasoning:
- Security-sensitive verifier and Tau binaries should resolve to explicit paths
  in production.
- `PATH` lookup is convenient for local development but weakens determinism and
  makes accidental tool substitution easier.

### Static assets inherit the same security headers

The nginx static-asset cache location now repeats the security headers applied
at the server level, and the API proxy now sets an explicit body limit.

Reasoning:
- Nested `add_header` directives can unintentionally narrow the header set.
- The API body limit should be explicit and aligned with bounded parsing in the
  Python layer.

### Runtime dependencies are smaller than local/dev dependencies

The repo now splits:
- `requirements-core.txt` for production/runtime
- `requirements-agents.txt` for optional agent/orchestration features
- `requirements.txt` as a convenience umbrella for local checkouts

Reasoning:
- The production image should not pull in agent/LLM packages unless an operator
  explicitly opts into them.
- Smaller runtime dependency sets reduce both supply-chain exposure and operator
  confusion about what is actually needed in production.

### Tau transaction envelopes reject malformed numeric metadata

Tau transaction signing now rejects boolean and negative values for
`sequence_number` and `expiration_time`.

Reasoning:
- These fields are ordering / expiry metadata, not free-form payloads.
- Booleans are technically `int` in Python and should not be accepted as valid
  sequence or expiry values.
- Negative values do not make sense for transaction ordering or expiration.
- The helper still accepts other integer-like values that normalize cleanly so
  existing local tooling does not break unnecessarily during hardening.

### Quote-receipt witness validation stays fail-closed per receipt group

The DEX engine validates quote-receipt leg bindings per `quote_receipt_hash`,
rejecting duplicate bindings and incomplete coverage before settlement
application.

Reasoning:
- Quote-bound intents should only prove coverage of the receipt they actually
  reference.
- Reusing leg index `0` across unrelated receipts must remain valid.
- Duplicate or incomplete bindings must remain deterministic rejections even if
  the implementation is simplified internally.

## Operator Notes

- Production/container builds should use `requirements-core.txt`.
- Local development can continue to use `requirements.txt`.
- If demo APIs are exposed beyond loopback, set `DEMO_API_TOKEN`.
- If Tau-backed gates are enabled in production, prefer absolute binary paths.
