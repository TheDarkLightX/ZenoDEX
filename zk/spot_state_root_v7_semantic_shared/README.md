# Spot state-root V7 semantic preparation

This standalone `no_std` crate defines the proof-neutral ABI and composition
kernel for a future source-authenticated Spot V7 guest. It deliberately remains
outside the frozen V6 workspace and does not change any current image ID,
receipt, verifier profile, or evidence record.

## Authority boundary

The future guest has two inputs with different trust origins:

```text
verified V6 child receipt
  + exact full-blob certificate and replay opening
  -> source pre/post snapshots, sender, ingress nonce,
     pre/post app hashes, pre/post nonce roots

untrusted V7 host bytes
  -> bounded canonical post-snapshot,
     proposed pre/post ZenoLedger state-root-v5 commitments
```

The child receipt authenticates only its journal; RISC0 receipt verification
does not expose the child guest's private input. The future V7 guest must
require the supplied full-blob certificate root to equal the authenticated V6
journal, validate the exact replay bytes against that certificate, and only
then decode the source opening. The host post-snapshot remains a proposal and
must equal the post-snapshot in that authenticated replay opening.

This crate implements the host decoder and the pure relation between both
inputs. `LegacySpotSourceProjectionV7` records the future caller precondition;
its public constructor authenticates neither a source receipt nor a replay
opening.

The host ABI omits every profile-fixed field. Snapshot version 1, active pool
status, CPMM with empty parameters, empty LP duration-risk state, and absent
vault/oracle state cannot be selected by host bytes. Counts are bounded by the
restricted bridge profile and the full input has one exact byte ceiling.

## Dependency boundary

Production code depends only on the two existing repository-local semantic
crates needed to reconstruct the legacy snapshot and call the restricted v5
bridge. Their existing `no_std` SHA-256 dependency is reused; this tranche adds
no new external production package. `serde_json` and `sha2` are locked
test-only dependencies used for shared vectors and independent digests. They
are already present in the repository, have the same determinism and license
posture as existing assurance tests, and never enter a guest binary. Removing
them would require a handwritten fixture parser and digest implementation with
less independent parity value and no smaller production closure.

## Exact journal

The fixed 310-byte journal contains only:

1. journal version;
2. restricted compatibility profile ID;
3. state-root-v5 scheme ID;
4. source pre/post app hashes;
5. source pre/post nonce roots;
6. pre/post ZenoLedger state-root-v5 commitments;
7. sender public key;
8. positive ingress nonce.

Program/image identity, receipt profile, source-authentication status, finality,
release authority, and settlement authority are absent. The crate exports
explicit false non-claim constants for source authentication, receipt
authority, and settlement authority.

## Remaining guest and proof work

A promotion tranche must still:

1. add this crate, the restricted bridge, and the legacy shared crate to an
   exact V7 source closure;
2. implement a minimal V7 guest that verifies the governed V6 child receipt,
   binds the exact full-blob certificate and replay bytes to the child journal,
   and only then constructs `LegacySpotSourceProjectionV7`;
3. commit the exact 310-byte journal;
4. build and pin the real V7 image ID and receipt-security profile;
5. produce a fresh positive receipt, exact seal mutation, source-built replay,
   dependency audit, and privacy scan;
6. add a sealed host verifier that checks receipt, image, profile, exact journal,
   and policy binding once;
7. bind that authenticated result to atomic ledger admission.

Until those steps complete, all V7 authority claims remain false.
