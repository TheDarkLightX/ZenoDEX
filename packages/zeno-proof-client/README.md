# @zenodex/proof-client

Browser + Node SDK for verifying ZenoLedger light-client checkpoint bundles.

## What it does

A ZenoLedger "browser checkpoint bundle" is a self-contained snapshot a
builder hands to a wallet so the wallet can advance its sync state without
trusting the builder. This SDK is what the wallet runs:

- **Bundle shape + hash binding**: every field commits to the bundle's
  embedded `bundle_hash`, checkpoint hash, signer-registry hash,
  signature-set root, and replayed header chain. Any single-bit mutation
  rejects.
- **Header-chain replay**: verifies each header from
  `trusted_prev_header_hash` through the target checkpoint, including
  consecutive heights, parent hashes, chain id, checkpoint/header binding, and
  header `app_hash` consistency.
- **Independent BLS quorum verification** (default): re-verifies
  every BLS12-381 G2-Basic signature against the registry using
  [`@noble/curves`](https://github.com/paulmillr/noble-curves). The browser
  reaches its own quorum verdict, not the builder's. A caller may explicitly
  choose `trustBuilderBls: true` for fixtures or already trusted builders; that
  mode still recomputes signer-registry binding but skips signature checks.
- **Wallet sync state transitions**: monotonic height, no chain-id drift,
  same-height drift rejection, rollback rejection. Modeled in TLA+ at
  `formal/tla/ZenoSdkWalletSyncCheckpoint.tla`.
- **ZK posture parsing**: normalizes authenticated local-testnet or
  checkpoint-adjacent proof status into `strict`, `fixture`, `fallback`,
  `open`, or `rejected` so clients can display proof state without treating
  fallback or fixture modes as production security claims. This parser checks
  field shape and cross-field consistency; it does not authenticate the status
  source by itself.

## Install

```bash
npm install @zenodex/proof-client
```

The only runtime dependency is `@noble/curves` at exactly version `1.2.0` —
pinned, no caret. See [`SECURITY.md`](./SECURITY.md) for the dependency
policy.

## Usage

### Default (independent BLS plus caller-pinned anchors)

The default mode verifies bundle shape, hash binding, header-chain replay,
range-summary binding, the caller-pinned previous-header root, the caller-pinned
signer-registry hash, and the BLS quorum. The previous-header and registry
anchors must come from local trust state or a separately verified pinset.

```js
import { verifyBrowserCheckpointBundleV0 } from '@zenodex/proof-client';

const report = await verifyBrowserCheckpointBundleV0(bundle, {
  expectedTrustedPrevHeaderHash: trustedPrevHeaderHash,
  expectedSignerRegistryHash: signerRegistryHash,
});
if (!report.ok) throw new Error(report.gaps.join('; '));
console.log(`Verified bundle for ${report.chain_id} at height ${report.height}`);
```

### Explicit builder-BLS trust mode

Use this only for fixtures or deployments that already trust the bundle builder
for quorum checking. The trust anchors are still caller-pinned.

```js
const report = await verifyBrowserCheckpointBundleV0(bundle, {
  trustBuilderBls: true,
  expectedTrustedPrevHeaderHash: trustedPrevHeaderHash,
  expectedSignerRegistryHash: signerRegistryHash,
});
if (!report.ok) throw new Error(report.gaps.join('; '));
// report.status === 'accepted_with_builder_bls_trust'
```

### Wallet sync

```js
import { advanceWalletSyncStateV0 } from '@zenodex/proof-client';

const advance = await advanceWalletSyncStateV0({
  currentState,
  bundle: newBundle,
  surface: 'zusd',
  expectedTrustedPrevHeaderHash: trustedPrevHeaderHash,
  expectedSignerRegistryHash: signerRegistryHash,
});
if (!advance.ok) throw new Error(advance.gaps.join('; '));
// Builder-trust advances return status "accepted_with_builder_bls_trust".
const next = advance.state; // ready to persist with next.trust_model
```

### ZK posture parsing

```js
import { parseZkProofStatusV0 } from '@zenodex/proof-client';

const posture = parseZkProofStatusV0(localTestnetStatus.zk_posture);
if (!posture.ok) throw new Error(posture.gaps.join('; '));
if (posture.proof_mode !== 'strict' || !posture.can_make_production_security_claim) {
  // Block governance/tokenomics approval and show the resolved mode.
}
```

Only call this on status carried by a trusted local endpoint or a separately
verified checkpoint bundle. A server-provided posture object is not proof by
itself. The parser never promotes a self-reported `production_security_claim`
into a production security claim by itself.

### Direct envelope verification (advanced)

```js
import { verifyBlsEnvelopeV0, verifyBlsQuorumV0 } from '@zenodex/proof-client/bls';

const result = await verifyBlsEnvelopeV0(envelope, {
  expectedPayloadKind: 'checkpoint',
  expectedPayloadHash,
});
```

## Cryptographic agreement with the Python builder

Python's `py_ecc.bls.G2Basic` and Node's `@noble/curves/bls12-381` agree
byte-for-byte:

| | Python (`py_ecc`) | Node (`@noble/curves`) |
|---|---|---|
| Private key size | 32 bytes | 32 bytes |
| Public key size | 48 bytes (G1) | 48 bytes (G1) |
| Signature size | 96 bytes (G2) | 96 bytes (G2) |
| DST | `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_` | same (default) |
| Hash-to-curve | RFC 9380 hash-to-G2 | same |

The cross-language test vectors live in
[`test/zenoBlsVerifier.test.mjs`](./test/zenoBlsVerifier.test.mjs). They
build real signed envelopes in Python and verify under Node — if the two
libraries ever diverge, those tests fail loudly.

## What the SDK does NOT do

- **It does not replay full ledger state transitions.** The browser verifies
  the header chain and checkpoint commitments, but it does not execute every
  body transaction or recompute every body-derived root locally.
- **It does not fetch bundles.** Transport (HTTPS, IPFS, gossip) is the
  caller's responsibility. The SDK only verifies bundles that arrive.
- **It does not sign anything.** Verification only; signing keys never live
  in the browser.

## Versioning

This SDK follows semver. Breaking changes to the verification semantics
require a major bump. See [`CHANGELOG.md`](./CHANGELOG.md).

The schema constants exported (`*_SCHEMA_V0`) follow ZenoLedger's own
schema-versioning convention — a `v1` bump in a schema means a new SDK
major release with new exports.

## Security

See [`SECURITY.md`](./SECURITY.md) for the threat model, supply-chain
policy, and how to report vulnerabilities.

## License

MIT — see [`LICENSE`](./LICENSE).
