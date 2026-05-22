# Zeno SDK Browser Wallet Sync

The SDK path should be layered. The first useful layer is a proof-carrying
checkpoint bundle plus a monotone wallet-sync reducer for browser and phone
clients.

## What Exists

- `tools/build_zeno_sdk_browser_bundle.py` builds a browser checkpoint bundle
  from the existing light-client verifier inputs.
- `python3 tools/zenoctl.py light-client build-browser-bundle` wraps that
  builder for operators.
- `tools/dex-ui/src/sdk/zenoProofClient.js` verifies bundle shape, canonical
  hash binding, checkpoint hash binding, signer-registry root binding, browser
  header-chain replay, quorum summary thresholds, and wallet-sync rollback
  rules.
- `packages/zeno-proof-client/` packages the same verifier as
  `@zenodex/proof-client` with an exports map, TypeScript declarations,
  package-local tests, exact-pinned `@noble/curves`, and a lockfile suitable
  for `npm ci`.

The browser package supports two verification modes:

- **Default** (`requireIndependentBls: false`, the default) — verifies bundle
  shape, hash binding, checkpoint binding, registry root binding, header-chain
  replay from the trusted predecessor hash, range-summary binding, and quorum
  summary thresholds. Trusts the Python builder's BLS quorum verification.
  Sufficient for surfaces that already trust the bundle source for quorum
  checking.
- **Independent** (`requireIndependentBls: true`) — additionally verifies
  every BLS12-381 G2-Basic envelope signature in the browser using
  [`@noble/curves`][noble], a pure-JS audited cryptographic library that runs
  in both browser and Node. Cross-language test vectors confirm signatures
  produced by `py_ecc.bls.G2Basic` (the Python builder) verify byte-for-byte
  under `@noble/curves`'s `bls12_381.verify` — same DST, same hash-to-curve,
  same point encoding. With this mode enabled, the browser verifies both the
  header chain and the BLS quorum locally.

[noble]: https://github.com/paulmillr/noble-curves

```js
const verification = await verifyBrowserCheckpointBundleV0(bundle, {
  requireIndependentBls: true,  // browser independently verifies signatures
});
```

## Build A Bundle

```bash
python3 tools/zenoctl.py light-client build-browser-bundle \
  --headers-dir /path/to/headers \
  --bodies-dir /path/to/bodies \
  --checkpoints-dir /path/to/checkpoints \
  --registry /path/to/signer_registry.json \
  --envelope /path/to/checkpoint.a.sig.json \
  --envelope /path/to/checkpoint.b.sig.json \
  --from-height 1 \
  --to-height 100 \
  --out /tmp/zenodex-browser-checkpoint-bundle.json \
  --pretty
```

## Use In Browser Code

```js
import {
  advanceWalletSyncStateV0,
  verifyBrowserCheckpointBundleV0,
} from './sdk/zenoProofClient.js';

const verification = await verifyBrowserCheckpointBundleV0(bundle);
if (!verification.ok) throw new Error(verification.gaps.join('; '));

const sync = await advanceWalletSyncStateV0({
  currentState,
  bundle,
  surface: 'zusd',
});
if (!sync.ok) throw new Error(sync.gaps.join('; '));
```

For external web, mobile, or React Native consumers, import the package
surface instead:

```js
import {
  advanceWalletSyncStateV0,
  verifyBrowserCheckpointBundleV0,
} from '@zenodex/proof-client';
```

## Formal Work Needed

The SDK glue itself does not need a large theorem-proving project before it is
useful. The trust boundary does need formal or semi-formal coverage before
public claims:

- wallet sync monotonicity: height never decreases, same-height app hash drift
  is rejected, chain id cannot change under one state;
- bundle binding: `bundle_hash` commits to the checkpoint, registry, envelopes,
  header chain, and verification summary;
- range replay: the browser replays `header_chain` from
  `trusted_prev_header_hash` through the target checkpoint header hash;
- quorum semantics: the browser-independent BLS package must accept exactly the
  same payload hash and registry threshold as the Python verifier;
- replay/downgrade resistance: stale bundles and weaker profiles cannot replace
  a stronger current wallet state.

TLA/PlusCal is the right first formal tool for wallet sync and rollback rules.
Cross-language hash/signature test vectors are higher value than Lean for the
initial SDK. Lean becomes useful if we want a public proof that the bundle
binding relation implies a specific checkpoint commitment.
