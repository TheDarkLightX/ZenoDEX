# Security Policy — @zenodex/proof-client

## Threat model

The SDK runs inside an **untrusted browser context** verifying bundles
delivered over an untrusted channel. The trust we grant is:

1. The Node/browser runtime correctly implements `crypto.subtle.digest` and
   `TextEncoder` per the WHATWG spec.
2. `@noble/curves` correctly implements BLS12-381 G2-Basic per the IETF
   draft-irtf-cfrg-bls-signature. We pin it to an exact version (no caret)
   and ship the lockfile.
3. The verifier process is not actively compromised — i.e., an attacker
   cannot read or write SDK memory, only feed bytes into the public API.

We do NOT trust:

- The transport. Bundles may be reordered, replayed, or fabricated.
- The builder. With `requireIndependentBls: true`, every signature is
  re-verified in-browser; the builder's claim of quorum is not credited.
- The signer set. Adversarial validator sets are caught by the existing
  registry-binding checks (see `tests/integration/test_zeno_ledger_chaos_*`).

## What an attacker cannot achieve

Given a verifier in `requireIndependentBls: true` mode, an attacker who
controls the bundle source cannot:

- **Forge a checkpoint**: every signature is cryptographically verified
  against the embedded signer registry. A forged signature fails noble's
  pairing check; a swapped public key fails the registry hash check.
- **Forge the header path**: every header in `header_chain` is replayed from
  `trusted_prev_header_hash`; parent-hash breaks, height gaps, chain-id drift,
  checkpoint/header mismatches, and inconsistent header `app_hash` values
  reject before acceptance.
- **Replay an older checkpoint**: wallet sync rejects any bundle whose
  height is less than `currentState.height`.
- **Diverge same-height state**: if two bundles share a height but have
  different `app_hash` or `checkpoint_hash`, the second is rejected.
- **Cross-chain replay**: `chain_id` is checked at bundle-shape time and
  pinned in the wallet sync state.
- **Smuggle bytes through the canonical hash**: `stableStringify` is sorted
  by key, rejects floats, rejects surrogate code points, and uses the same
  domain-separated SHA-256 scheme as the Python builder.

## What an attacker can still do

- **Mount the SDK out of date.** A consumer who ships an old SDK version
  with a known issue is vulnerable to that issue. The SDK has no
  self-update mechanism. Consumers must pin and monitor.
- **Drop bundles entirely.** Liveness is the caller's responsibility. If
  the transport never delivers, the SDK never accepts — fail-closed.
- **Exhaust browser resources.** The SDK has bounded sizes on signature
  envelopes (≤ 64) and header-chain entries (≤ 4096), and uses safe-integer
  arithmetic for weight sums, but a malicious bundle could still cost CPU time
  on hash replay and BLS pairing checks. The caller should rate-limit
  verification attempts.

## Dependency policy

- **Exact version pins.** `@noble/curves` is `1.2.0`, not `^1.2.0`. Bumping
  requires re-running the cross-language test vectors against `py_ecc` and
  re-publishing.
- **No native dependencies.** Pure JS only. The SDK runs identically on
  browser, Node, Deno, Bun, and React Native.
- **Minimal dependency tree.** The runtime dependency is exact-pinned
  `@noble/curves`; its lockfile records the transitive `@noble/hashes`
  package used by that version.

## Lockfile + integrity

The SDK ships its own `package-lock.json` so consumers installing via
`npm ci` get the exact dependency tree the maintainers tested against.
For browser deployments, integrity-check the bundled distribution via
Subresource Integrity (SRI) — `npm pack --dry-run` shows the file tree
that ends up in the published tarball.

## Reporting

Email security@zenodex.example with:
- A reproducible test case (preferred: a failing test that we can paste in).
- The SDK version (`npm ls @zenodex/proof-client`).
- Environment (browser / Node / Deno / Bun + version).
- Expected vs. observed behavior.

We treat the following as in-scope vulnerabilities:
- Any input that causes the verifier to return `{ ok: true }` when it
  should return `{ ok: false }`.
- Any uncaught exception escaping `verifyBrowserCheckpointBundleV0`,
  `verifyBlsEnvelopeV0`, `verifyBlsQuorumV0`, or
  `advanceWalletSyncStateV0`.
- Any path that reads or writes outside the inputs the consumer provided
  (no DOM, no `localStorage`, no `fetch`).

Out of scope:
- Issues caused by deliberately disabled JavaScript engine features
  (e.g., disabling `crypto.subtle`).
- Issues in the underlying `@noble/curves` library — report those upstream.
