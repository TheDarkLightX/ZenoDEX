# Unified economic root guest and receipt endpoint review

Date: 2026-09-05. Independent bounded advisory review. Authority: `NONE`.
Local integration HEAD observed: `e7948ff0ff9592addf740ea597cfb42e0e6e190f`.
The new root crate and endpoint were uncommitted; the frozen source archive below
identifies the reviewed subject.

Verdict: no blocking behavioral defect found in the scoped dispatcher,
child-claim loop, measured host binding or statically selected receipt endpoint.
**Guest-level negative evidence and exact-build real receipt qualification
remain incomplete.** This review closes no whole-program, production publication
or economic-route correctness gate. Only this report was added.

## Exact source subject

The source04 archive is `zenodex-v3-root-source04.tar.gz`, 624,676 bytes:

```text
archive SHA-256:
f01edeeaba24da97beecd405552710b5c69a4be8905a00de647e063795aeacd9
285-file source manifest SHA-256:
bfe75b4740007791035a6f9ad594da49ca443294138159df92c4c1a51271a2cb
```

The reviewer independently hashed the archive and manifest, read every archived
manifest entry without extraction, and verified all 285 file hashes. The
manifest is `zenodex-v3-root-source04-manifest.json`. Its 20 direct root/endpoint
files include the following critical identities:

| File | SHA-256 |
|---|---|
| `zk/global_economic_root_risc0/shared/src/lib.rs` | `44e75a89c14f5de636ee409ac077fe8a3b030ff1cc16f64f2231cddf89ea4f5c` |
| `zk/global_economic_root_risc0/methods/root/src/main.rs` | `26232395e8766451228bad1e9828392d043da59502f16cfdf33447fcfce56d15` |
| `zk/global_economic_root_risc0/host/src/lib.rs` | `5efc3723d344339a0f8575f8ece9b71c42389ec110c86841ffdcbc3df20e395f` |
| `zk/global_economic_root_risc0/host/src/bin/verify_receipt_v1.rs` | `221071251e7394c8949dddf261c87c083147491d876c5945c6c8fcb6b8d5f84f` |
| `zk/global_economic_root_risc0/methods/build.rs` | `4fdba1c11049637ce580b3c90d39c8f06a25b1e78d72b9884d50af4dd0c7087b` |
| `zk/global_economic_root_risc0/Cargo.lock` | `2a687d7738a1e2f3483b0e4adb11aa086188b1aa9ef084f9cdce99503dcba1fe` |
| `zk/global_economic_root_risc0/shared/tests/root_dispatch.rs` | `9bc22ca99bf9d9c53321107ded3bbb66bd1e8a6ff6649073a83e147ec410040b` |
| `zk/global_economic_root_risc0/host/tests/real_initialization_epoch.rs` | `ea3ca5ddf71b21f19d45a88e962660c10c199da74584262ea903a864576ea473` |
| `zk/risc0_receipt_verifier_v1/mod.rs` | `5a638c33944186c798233fd2bffb919ee9ae9558d13512186e952b44edada050` |
| `zk/risc0_receipt_verifier_v1/protocol.rs` | `d626fc7cc969f42504d9ff19d59570071fd049a6b1fed6e0b6cc2101d8060b82` |

Critical runtime files stayed equal to source04 during review. Two subsequent
ABI dependency changes are present in the working tree but absent from source04:
`asset_transfer_global_allocation.rs` and `asset_transfer_receipt_admission.rs`.
Those are the separately reviewed public pure-relation export packet. Its local
passing tests do not relabel source04's source identity. Qualification of the
integrated successor requires a new dependency manifest and measured rebuild;
reuse of a receipt requires establishing the resulting exact image identity.

The only direct root-file drift during review was
`test_support/mod.rs`: archived SHA
`16ad83fb0ca6eea1a95e114882dae7763f6b16fe86830aceacf9eb40a59154ab`
became `c3a1fe7f0bd706597182c4c6e924dc007bbe38badb108c78d687202e9d3668c2`.
Removing exactly two comments and a scoped
`#[allow(clippy::needless_borrow)]` reproduced the archived bytes. No test
assertion or guest/host behavior changed. The allowance applies to an imported
historical test fixture and does not affect a runtime admission path.

## Dispatcher and statement separation

The guest reads a bounded outer length before allocating its private frame:
at most 8 MiB plus the 13-byte root header. Shared decoding then requires the
`ZDXROOT1` magic, a closed tag, a nonzero per-tag payload length and exact frame
length. Initialization has the existing 8 MiB bound; recursive epochs have the
existing 2 MiB bound. These additions fit the guest's 32-bit address width.

Tag 0 delegates to the existing complete initial-state canonical decoder,
row-count checks, state/profile/policy/statement binding and journal production.
Tag 1 decodes the existing closed recursive enum, rejects trailing bytes, and
requires exact postcard re-encoding before dispatch. It delegates to the
existing direct-epoch, command-aggregation or aggregated-epoch preflight.

`PreparedRootV1` and `RootChildClaimV1` have private fields. The guest receives
the journal and child list through validated construction. Every branch emits
its existing journal format. Initialization and epochs have the same settlement
ABI schema string, but distinct closed field sets and exact expected journals;
command aggregation has its separate journal schema. A tag is not an arbitrary
journal-commit operation.

The actual guest performs one `env::verify(image, journal)` call for each
prepared child claim, in order, before its sole `env::commit_slice` call. Invalid
frames and preflight failures abort before committing a journal. This remains
an accepted-statement proof, with abort-based rejection.

## Images, order and assumption closure

The inherited direct preflight requires 1 through 8 route receipts, exact
cardinality against the certificate vectors, unique occurrence/journal/assumption
roots, exact context and ordered state-root chaining. Its assumption commitment
includes the route release, occurrence, profile, writer epoch, exact journal
digest and selected image. It verifies terminal state-root and module-leaf totals.

Command aggregation retains the same route-claim checks and exact group bounds.
Aggregated epochs require 9 through 64 commands, exact groups of up to eight,
canonical group indices and slices, context including epoch height, state-root
continuity and leaf totals. Every aggregation child image must equal the
certificate's root image. A child produced by a different standalone epoch image
cannot satisfy this image equality for the new root image.

The new host rejects empty/zero placeholder methods, independently computes the
compiled ELF's image ID, and compares it with the compiled image constant. It
binds the initialization/epoch journal's public root image to that measured ID.
The command-aggregation intermediate journal does not carry a root-image field;
its host still measures the actual method, and its parent checks the child image
against the epoch's root image.

The host checks child count before `zip`, then each child's Succinct kind, exact
journal and cryptographic verification before adding it as an assumption. It
verifies the resulting root receipt again against the exact compiled root image
and prepared journal. The host enables RISC0's `disable-dev-mode` feature.

The guest commits the public root-image field supplied through its validated
statement; it does not independently measure its own ELF. The host and accepting
consumer's exact measured-image/journal binding therefore remain necessary to
interpret that field. Generic proof validity alone does not establish a selected
profile or currently authorized deployment.

The endpoint has one compiled ELF/image pair and a function-pointer decoder
selected statically by its measured wrapper. The root wrapper accepts canonical
postcard receipts only, requires complete consumption and exact re-encoding,
and supplies no codec negotiation or image fallback.

The endpoint bounds the whole request to 48 bytes plus a 1 MiB journal and
16 MiB receipt, rejects empty components and trailing data, measures the compiled
method and checks the requested image, then verifies a Succinct receipt with
exact journal bytes. Its success response binds the entire request digest and
image. Output failure returns failure; no ledger or profile authority is granted.

For the cryptographic call's semantics, the reviewer inspected RISC0 3.0.6
`Receipt::verify`, `ReceiptClaim::ok` and guest `env::verify`. Their source bytes
were independently compared to the cached `.crate` archive whose SHA-256 matches
source04's Cargo.lock. After seal integrity verification, `Receipt::verify`
compares the full claim digest to `ReceiptClaim::ok`, binding the image, exact
journal digest, successful `Halted(0)` exit and empty assumptions. Thus the code
does not treat a conditional receipt as an unconditional verified result.
This is source-level dependency evidence; the reviewer did not rerun a genuine
unresolved-Succinct receipt negative case.

## RGR-01: guest assumption enforcement needs direct negative evidence

The ignored real test's missing, changed-journal and Fake child cases in
`host/tests/real_initialization_epoch.rs:72` through the subsequent host checks
reject inside `build_economic_root_executor_env_v1`. They never reach guest
execution. Those tests protect host admission and do not kill a mutant that
omits the guest's `env::verify` call. An honest positive composed receipt also
does not independently distinguish that omission when the host already checked
its children.

No such omission is present in the reviewed source. This is an executable
evidence gap for guest mediation, not a demonstrated acceptance bypass. Retain
a direct guest execution/proof rejection for a missing or mismatched assumption,
with a positive control using the same valid frame and a meaningful
verification-omission mutant. Bind that evidence to the exact rebuilt guest.
Genuine unresolved-Succinct refusal should also be exercised through the new
host/endpoint, beyond the pinned library's source-level guarantee.

The new ignored real test exercises initialization and direct epochs. Recursive
aggregation branches have shared-preflight tests but are not covered by that
test's four real receipts. Their real assumption composition remains separate
qualification work.

## Evidence executed and reported

The reviewer independently ran the endpoint's protocol tests without building
guest or RISC0 dependencies:

```bash
rustc --edition 2021 --test zk/risc0_receipt_verifier_v1/protocol.rs \
  -o /tmp/zenodex-v3-root-protocol-review-tests
/tmp/zenodex-v3-root-protocol-review-tests
```

Result: **4 passed**. Coverage includes a fixed Python-compatible frame, every
truncation of that frame, trailing bytes, wrong magic, zero/overflow lengths,
both maximum field sizes, their immediate upper neighbors and the total bound.
This proves no cryptographic or guest-execution property.

The implementation agent reported **15 release/shared/host/endpoint tests
passed** against its actual-root build and a pending strict Clippy replay after
the test-only annotation. This is agent-supplied status, not an independently
replayed or final cryptographic verdict. Host method tests choose a branch based
on whether a compiled ELF exists; a passing count alone does not prove a genuine
method was built. Preserve actual ELF/image, compiler, lock, source and command
logs when promoting build-specific evidence.

The reviewer inspected the new shared tests for same-image initialization and
direct epochs at counts 1 and 8, aggregation at 9 and 64, ordered-child/image
refusals, closed tags, frame bounds, journal-family separation, context drift and
noncanonical payloads. Source inspection is distinct from executing those tests.
Style routing selected strongly typed transition kernels. All eight scanner
findings were test-only `unwrap` calls or casts of fixed small bound constants.

No heavy local build, real proof generation, remote command or deployment was
performed by this review. The separate real proof run was still unqualified
here; its completion must be recorded with its own exact artifact subjects.

## Claim and resource ceilings

The retained real fixture's structural child commits supplied route-journal
bytes. It does not establish asset-transfer, coordinator or route economic
semantics. Its initial source-authorization roots are fixture commitments,
without external legitimacy. The inherited epoch preflights establish structural
receipt composition; they do not independently establish every economic effect,
body, data-availability or finality claim appearing in the certificate. Selected
route proofs and the actual outer refinement/admission checks must close those
obligations.

The byte ceilings bound the admitted frames and guest's outer input allocation.
They are not measured peak-heap or cycle guarantees for all malformed payloads.
In particular, the host encoder clones initialization bytes or serializes a
caller-created recursive value before checking its resulting payload length.
No mounted host resource-isolation or total allocation-failure contract is
established here.

Source hashes, local parsing tests, a dispatch receipt and advisory review do
not establish all-lane invariant preservation, authorization, allocation
continuity, publication mediation, durable recovery, current authority or
production value safety. The exact trusted cryptographic implementation,
compiler/build provenance, process/OS integrity and consumer binding assumptions
remain explicit boundaries.
