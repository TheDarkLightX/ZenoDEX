# Changelog

All notable changes to `@zenodex/proof-client`.

This project follows [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

### Security
- Reject signer registries that assign one canonical BLS public key to more
  than one signer identity, including revoked entries. Quorum verification
  also refuses to count the same public key twice as a defense-in-depth check.

## [0.1.0] — Initial public release

### Added
- `verifyBrowserCheckpointBundleV0(bundle, options)`: verifies bundle shape,
  hash binding, checkpoint binding, signer-registry hash binding,
  signature-set root binding, browser header-chain replay, header app-hash
  consistency, range-summary binding, and quorum summary thresholds.
- `advanceWalletSyncStateV0({ currentState, bundle, surface, updatedAtMs,
  requireIndependentBls })`: monotonic-height wallet sync with rollback,
  same-height drift, and chain-id-drift rejection.
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

### Known non-claims
- The SDK does not execute full ledger state transitions or recompute every
  body-derived root locally.
- The SDK does not perform header signature aggregation; each envelope is
  verified individually.
- The SDK does not include transport, key custody, or signing primitives.
