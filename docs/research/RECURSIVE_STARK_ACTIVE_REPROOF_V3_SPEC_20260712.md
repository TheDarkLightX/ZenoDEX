# Recursive STARK Active Reproof V3 Specification

Date: 2026-07-12
Status: implemented; RS-CBC-014 closed for the scoped same-host profile

## Purpose

This profile restores bounded current-image V1 and recursive-v2 computational
integrity evidence after the active lockfiles moved to `anyhow 1.0.103` and
later V1 recursive source hardening changed the guest programs.

The profile is additive. It must not modify or reinterpret either historical
trust root:

- `config/proof_profiles/risc0_recursive_rebuild_reference.json`;
- `config/proof_profiles/risc0_recursive_v2_rebuild_reference.json`.

The eventual active trust root is
`config/proof_profiles/risc0_recursive_active_reproof_reference_v3.json`.
That file must not exist as an accepted reference until every positive receipt
and negative control in this specification has been generated and replayed.

## Construction Boundary

The active recursive-v2 harness is a compatibility fork at
`zk/recursive_stark_v2_active_reproof_risc0`. Its proof algorithm remains
byte-equal to the historical implementation after the bounded identity
preamble. The fork changes only:

- the three governed V1 leaf image IDs;
- default temporary output names;
- package and dependency paths needed for a separate lockfile;
- the pair verifier's topology guard, from the historical one-leaf shape to
  the exact active two-leaf shape.

`tests/test_risc0_recursive_v2_active_reproof_harness.py` rejects proof
algorithm drift and requires the pair verifier to retain its cryptographic and
parent/child binding anchors. The active pair verifier accepts only an inner
node with two immediate leaves and a root with one immediate subtree and two
flat leaves. This separation preserves the source closure behind historical V2
evidence while giving current V1 identities an explicit home.

The active workspace has its own lockfile. The repository dependency-audit
registry must include that lockfile and must reject any `anyhow` version other
than `1.0.103`.

## Locally Rebuilt Candidate Identities

The worktree based on merged revision
`7b495df837e1a877d8c49da0f06ebce85661e39e`, plus the exact source
inventories committed by this profile, produced these candidate image IDs under
the pinned RISC0 3.0.5 and guest Rust 1.94.1 toolchains. The Git value is a
verified base revision. The source inventories bind the proof-generating source
that did not yet exist in that base revision.

| program | candidate image ID |
| --- | --- |
| V1 aggregate | `c4bde351d48e8e775c2e831fc37fb98a9e45ed59455afe761572d2e11ceed6c4` |
| V1 perps leaf | `a0fc064f0c4292473b9d822229c367533302fb11cb7cfdb845332c87d0fe956b` |
| V1 Spot leaf | `59930b80d7f250923cf6d88aab34e431033f35f60343339c37e737fa30847dab` |
| V1 summary leaf | `88e350ecd2eee0eeec2167c8e6d4062c3edf6f8b2d5f598bc8a030279920143a` |
| V1 zUSD leaf | `17d5dd12874cf18efc00869350bbc9c9b43c996629f52957e96e1a8c63e1cdef` |
| recursive-v2 aggregate | `0a678da608708af7bd6c35bf825ffe8815efd67f0a8041466929fb2fcda7ae68` |

These are build observations. They gain scoped evidence authority only through
the active reference and replay checker defined below.

## Required Positive Evidence

The accepted evidence set must contain freshly generated Succinct receipts for:

1. one current V1 Spot leaf;
2. one current V1 zUSD leaf;
3. one current V1 aggregate root over the two leaves;
4. one current recursive-v2 closed subtree over the same two leaves;
5. one current recursive-v2 epoch root over that subtree.

Each receipt must be verified under its independently recomputed image ID. The
checker must independently recompose and require exact authenticated journal
equality. Receipt kind, hash suite, verifier-parameter digest, control ID,
canonical artifact bytes, and bounded artifact size are mandatory fields.

The V1 and V2 roots must bind the same ordered authenticated leaf statements.
They may use different proof topology and journal schemas.

## Required Negative Evidence

The active evidence checker must require all of these controls:

1. a one-word least-significant-bit mutation of the V1 root Succinct seal;
2. a one-word least-significant-bit mutation of the V2 root Succinct seal;
3. the V2 inner execution without a required leaf assumption;
4. leaf order replay with identical canonical composition results;
5. duplicate leaf rejection;
6. wrong V1 leaf image ID rejection;
7. wrong V2 aggregate image ID rejection;
8. receipt-security-profile substitution rejection;
9. exact journal substitution rejection.

A handled verifier rejection may exit zero only when its canonical typed output
unambiguously reports rejection. Process exit status alone never authorizes a
proof.

## Active Reference Contract

The active V3 reference must bind:

- the verified Git base revision and its ancestry relationship to the checkout;
- exact source inventory for V1, V2, and the active harness;
- exact source inventory for the checker, builder, CBC policy, workflow, tests,
  and governing specifications used to promote the claim;
- all three Cargo lockfiles and their SHA-256 digests;
- recorded Cargo, rustc, rustdoc, cargo-risczero, and r0vm identities;
- every rebuilt guest ELF hash, byte count, image-ID words, and image ID;
- active host harness and verifier hashes;
- request, receipt, journal, transcript, and negative-control hashes;
- the exact receipt security profile;
- the exact claims and nonclaims below.

Unknown fields, duplicate JSON keys, noncanonical encodings, integer-for-Boolean
substitution, missing artifacts, extra artifacts, and coherent data-only hash
rebinding under the reviewed checker must reject. Checker and policy edits are
separately review-governed source changes and are bound by the promotion-source
inventory.

The host binaries and guest ELF hashes are retained build observations. Their
files are not committed into this evidence packet. The required CI lane must
rebuild current V1/V2 verifier programs from the pinned source and
cryptographically replay the retained root receipts. The static checker does
not claim to reauthenticate absent historical binaries or the recorded
toolchain executables.

## Promotion Rule

RS-CBC-014 may advance from `pending` only when:

```text
fresh_v1_leaf_receipts_verified
&& fresh_v1_root_receipt_verified
&& fresh_v2_inner_and_root_receipts_verified
&& exact_v1_seal_mutation_rejected
&& exact_v2_seal_mutation_rejected
&& missing_assumption_rejected
&& source_and_toolchain_bindings_match
&& active_reference_checker_accepts
```

The scoped promoted claim is limited to same-host, bounded, current-image
computational integrity for the recorded two-leaf proof tree.

## Required Nonclaims

The active reference and checker must keep all of these false:

- arbitrary-depth recursion;
- general fanout promotion;
- cross-host reproducibility;
- reproducible release;
- proof-byte determinism;
- public replay;
- clean-worktree proof generation;
- retained host-binary or guest-ELF availability;
- checker-side toolchain-binary reauthentication;
- network isolation;
- sandbox assurance;
- semantic asset conservation;
- data-availability verification;
- durable atomic ledger admission;
- privacy or zero knowledge;
- settlement authority;
- release authority;
- production authority.

The accepted active reference is
`config/proof_profiles/risc0_recursive_active_reproof_reference_v3.json`.
Its checker is `tools/check_risc0_recursive_active_reproof_v3.py`. No other
ZRPF obligation advances merely because RS-CBC-014 closes.
