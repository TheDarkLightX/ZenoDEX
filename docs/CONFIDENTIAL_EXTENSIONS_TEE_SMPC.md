# Confidential Extensions: TEE First, sMPC Second

## Decision

Use TEE first for private extension logic.

Reason:
- It is operationally simpler than sMPC.
- It fits low-latency advisory services such as premium routing, private quoting, and confidential risk scoring.
- It lets us meter usage and pay providers without exposing extension code.

## What the TEE surface should do

A confidential extension should be treated as an attested advisory sidecar.
The DEX core only accepts its output when all of the following hold:

- the enclave measurement is on an approved allowlist
- the attestation is fresh under a bounded epoch window
- policy binding is explicit and fail-closed
- replay protection is present
- output bounds are checked locally
- fee transfer to the provider is conserved locally

This repo now includes a deterministic receipt format for that boundary:
- `src/core/confidential_extension_receipts.py`
- `src/kernels/dex/confidential_extension_tee_gate_v1.yaml`

## Current sealed-bid experiment

A bounded sealed-bid private-state experiment now exists in the repo:
- `src/core/sealed_bid_auction.py`
- `tools/metamuse_sealed_bid_lane.py`
- `src/kernels/dex/sealed_bid_commit_reveal_gate_v1.yaml`

Scope:
- public commitment receipts hide quantity, price, and nonce
- reveals bind to commitments
- settlement is deterministic uniform-price for a fixed sell inventory
- ESSO verifies the commit/reveal phase discipline; Python covers the bounded settlement experiment

## Where sMPC fits

Use sMPC only where latency is secondary to trust minimization.

Good candidates:
- periodic fee splitting among multiple private strategy providers
- sealed-bid batch auctions with longer clearing windows
- multi-party benchmark computation where no single operator should see all inputs
- institutional crossing / private netting windows

Bad candidates for now:
- hot-path route search
- per-hop quote enumeration
- low-latency order matching
- anything that must run at UI quote speed

## Why not Zama first

FHE and confidential smart contracts are useful when we need on-chain confidential state or encrypted inputs.
That is not the first problem here.

The first problem is private extension code with practical latency and auditable payment.
TEE solves that more directly.

If we later need confidential balances, sealed bids, or encrypted control loops, Zama/FHE becomes a stronger candidate.

## Formal scope

The realistic formal targets today are:
- attested extension metering
- burn receipt accounting
- local conservation / replay-sensitive receipt gates

The harder routing heuristics still need decomposition into smaller witness kernels before they are honest ESSO proof targets.
