# Changelog

All notable changes to `@zenodex/proof-client`.

This project follows [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] — Initial public release

### Added
- `verifyBrowserCheckpointBundleV0(bundle, options)`: verifies bundle shape,
  hash binding, checkpoint binding, caller-pinned previous-header and
  signer-registry anchors, signer-registry content binding,
  signature-set root binding, browser header-chain replay, header app-hash
  consistency, range-summary binding, and quorum summary thresholds.
- `advanceWalletSyncStateV0({ currentState, bundle, surface, updatedAtMs,
  requireIndependentBls, trustBuilderBls })`: monotonic-height wallet sync with
  rollback, same-height drift, chain-id-drift rejection, persisted target-header
  root, signer-registry hash, and trust model.
- `verifyBlsEnvelopeV0(envelope, options)`: independent BLS12-381 G2-Basic
  signature verification via `@noble/curves`.
- `verifyBlsQuorumV0(bundle, options)`: full registry binding re-derivation
  and quorum-report-hash agreement check.
- `hashV0(domain, value)`, `stableStringify(value)`: canonical hashing
  primitives mirroring the Python `zeno_ledger_v0` module.
- TypeScript declarations at `src/index.d.ts`.
- Cross-language test vectors (`test/zenoBlsVerifier.test.mjs`): real
  `py_ecc.bls.G2Basic` envelopes verify under `@noble/curves` byte-for-byte.

### Security posture
- Exact-pinned `@noble/curves@1.2.0`. Bumping requires re-running the
  cross-language vectors.
- Pure JS, no native deps, no runtime fetch, no DOM access.
- All public functions return `{ ok, ... }` discriminated unions; no
  unhandled exceptions escape the public surface.
- Independent BLS is the default. `trustBuilderBls: true` is an explicit weaker
  mode and returns `accepted_with_builder_bls_trust`.
- `auto-strict -> open` ZK fallback status is blocked by the proof-status
  parser and cannot promote a production security claim.

### Known non-claims
- The SDK does not execute full ledger state transitions or recompute every
  body-derived root locally.
- The SDK does not perform header signature aggregation; each envelope is
  verified individually.
- The SDK does not include transport, key custody, or signing primitives.
