# Restricted Spot state-root-v5 bridge

This standalone, `no_std` crate derives ZenoLedger Spot state-root-v5
commitments from a deliberately restricted legacy RISC0 Spot snapshot. It is a
proof-neutral compatibility kernel for a future V7 settlement guest.

The accepted profile fixes every legacy omission that affects the v5 root:

- LP duration-risk metadata is empty;
- pool curves are `CPMM` with empty parameters;
- all pools are active;
- vault and oracle state are absent;
- native-asset balances are absent;
- one positive ingress nonce maps legacy `next_nonce = n` to runtime
  `last_nonce = n - 1` before the transition and `last_nonce = n` after it;
- no other runtime nonce entry exists.

Successful derivation proves only that the supplied snapshots encode to the
supplied v5 roots and caller-provided legacy source commitments under this
profile. The complete accepted domain is committed by the compatibility
profile ID. The crate does not authenticate a receipt, the caller-provided
source commitments, a source opening, a ZenoLedger header, or a finality
certificate. It does not authorize settlement.

## Source-closure boundary

The crate intentionally owns an independent Cargo workspace. Adding it to the
frozen `zk/zrpf_risc0` workspace would change that workspace's manifest,
lockfile, and exact governed inventory even though current V6 guests do not use
the bridge. Current V6 image IDs, receipts, and evidence remain untouched.

## V7 integration surface

A future V7 guest should:

1. verify the exact V6 child receipt and source opening before interpretation;
2. obtain the pre-snapshot, singleton sender, ingress nonce, and legacy nonce
   entries from that authenticated opening;
3. decode a bounded canonical host-proposed post-snapshot, then require its
   derived legacy app hash to equal the authenticated source journal's post app
   hash;
4. obtain expected pre/post v5 roots from the authenticated V7 proposal;
5. construct `ExpectedLegacySpotCommitmentsV1` only from the authenticated
   source journal;
6. call `verify_restricted_spot_state_root_v5_transition_v1`, which compares
   all four derived source commitments and both v5 roots exactly;
7. emit the compatibility profile ID, state-root scheme ID, exact v5 roots, and
   source commitments in a versioned V7 journal;
8. bind that journal to one exact V7 image and verifier profile before atomic
   ledger admission.

V7 must add this crate and its dependencies to its own exact source closure and
must generate a fresh V7 image, receipt, mutation control, and replay record.
Source authentication remains a V7 obligation; this proof-neutral crate cannot
establish that its expected commitment values came from a verified receipt.
The existing strict Spot field
`spot_app_hash_equals_zeno_ledger_state_root_verified` remains `false` because
the two root schemes are different.
