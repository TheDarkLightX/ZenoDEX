# Independent review of the restricted common-profile proof chain

Date: 2026-09-05. Review type: targeted, read-only source review. No build,
test, proof job, remote job or production source change was performed during
this review.

The reviewed working tree was based on commit
`1887059a633bd7fffc75620ba63b35f964db9b2a` plus the then-uncommitted route and
ROOT candidates. HEAD advanced to that commit during the review; the two
primary shared-source hashes below were rechecked and remained unchanged.
This is an exact-file review, not an assessment of every file at that commit
or of later dirty candidates.

## Result and supported composition claim

No concrete blocker was found for the narrow composition claim below:

> Under externally admitted image/profile selections, verified receipts for
> the reviewed guests establish the checked restricted transfer and coordinator
> relation, the exact route journal, and ordered route-receipt membership with
> common context and pre/post-state-root continuity in the epoch journal.

This source result is conditional on genuine, fully verified receipts for the
exact rebuilt images and journals. The final five-receipt evidence packet must
separately bind its actual source closure, compiler, images, input, profile,
journals and receipt verification results. The final fixture and GPU evidence
were outside this review; the parent integration agent reviews them separately.

The new route and ROOT composition code received independent scrutiny. The
reviewer authored the reused W04 allocation relation, so observations about that
relation are explicitly self-review. Earlier independent W04 review and its
retained findings remain relevant; this note does not replace them.

## Checked binding chain

The route shared preflight selects the active profile and governed module,
coordinator, route and asset-policy entries. It restricts the route to one
`ASSET_TRANSFER` lane and one selected module release. It checks the exact
command-body hash, subject and grant binding, then recomputes the existing
module and coordinator results. See
`zk/asset_transfer_route_composer_risc0/shared/src/lib.rs:116` and `:158`.

The restricted allocation relation checks that the module journal's occurrence
identity equals the supplied occurrence, the predecessor root is exact, the
height advances once, and both global snapshots share the module context. It
binds the selected coordinator state projections and full balance/custody/supply
rows, preserves the complete claimant table and other allowed state, and requires
one exact replay insertion. This relation rejects unsupported state categories;
it does not establish the predecessor's allocation partition. See
`zk/global_settlement_abi_v1/src/asset_transfer_global_allocation.rs:65`.

The route then derives its journal from those exact results and supplied full
states. The existing route projection checks profile/state context, exact lane
journal count/order/roots and coordinator context; the existing state/effect
refinement checks the before/after transition against the effects and consumed
occurrence. The derived route journal commits the full pre/post-state roots and
the exact effect and terminal roots supplied by the derived coordinator result.
See route shared `:192` and `:212`, and
`zk/global_settlement_abi_v1/src/route_global_state_projection.rs:114`, `:139`
and `:181`.

The route guest verifies the selected coordinator image and exact derived
coordinator journal before committing the route journal. The route host measures
its compiled route/coordinator ELFs, checks the selected IDs, requires the exact
child journal, and cryptographically verifies a Succinct receipt before adding
the assumption. The coordinator guest separately verifies its fixed module
image. A prepared value alone is not a cryptographic witness.

ROOT's framed private decoder selects initialization or recursive epoch input
using an explicit tag, enforces length and canonical decoding, and returns the
exact existing journal type. Epoch preparation delegates to the existing
preflights. The ROOT guest verifies every prepared child claim before committing
the journal. Its host checks exact receipt cardinality, journal bytes and images,
rejects non-Succinct receipts, verifies every child receipt before installing
assumptions, and binds initialization/epoch public root-image fields to the
measured compiled ROOT image.

For direct epochs, the preflight checks exact child count against the certificate
vectors, validates their unique occurrence/journal/assumption roots, and iterates
in that order. Every child must match its expected occurrence, journal root,
image-bound assumption root, chain, deployment, profile, writer epoch and current
pre-state root. The final state root and counted leaves must equal the declared
terminal values. See epoch `shared/src/preflight.rs:78`, `:118` and `:159`.

For aggregated epochs, each aggregate must use the certificate's ROOT image.
The exact number of aggregates is derived from the command count. Canonical
eight-command partitions bind group position, occurrence/journal/assumption
slices, context, epoch height and state-root continuity. The final root and
counted leaves are checked again. Initialization and command-aggregation
journals retain their distinct closed schemas; using one guest image does not
make those journal shapes interchangeable. See epoch
`shared/src/aggregation.rs:190`, `:251` and `:321`.

## Confirmed limits and claim blockers

1. **Aggregate economic commitments are not derived by ROOT.** Epoch certificate
   validation checks the shapes of `effect_plan_root`,
   `terminal_obligations_root`, `body_commitment`, data-availability/finality
   roots, and source/toolchain manifest roots. Direct and aggregated preflight
   do not recompute those values from child route effects or evidence. See epoch
   `shared/src/lib.rs:183` and `shared/src/preflight.rs:78`. Exact-journal receipt
   verification proves that the guest committed those bytes; it does not supply
   the missing semantic derivation. A claim of complete epoch economic-effect
   aggregation remains blocked without the corresponding external checked
   derivation and its binding.

2. **Image/profile admission remains external.** ROOT validates child image
   selections through the certificate-bound assumption roots. It does not load
   an authoritative active-profile registry and establish its legitimacy. The
   route checks consistency of the disclosed profile and registries, while its
   host binds selected route/coordinator images to measured local ELFs. The final
   common-profile fixture must also match the coordinator's fixed module-image
   pin. These consistency checks do not activate a profile or authorize a writer.

3. **Signer and predecessor authority remain external.** The route binds the
   occurrence to command body, subject and grant fields. It does not verify the
   command signature or establish that the context was authenticated for that
   exact command. Full-state row matching and unchanged claimant rows do not
   establish the original claimant allocation, authenticated store provenance,
   real-asset possession or enforceable ownership. Initialization evidence and
   the verifier/publisher boundary must discharge their own precise obligations.

4. **The module-leaf count uses a one-module premise.** The epoch preflight sums
   `ordered_lane_journal_roots.len()` from route journals. For this restricted
   route there is one lane journal, its coordinator composes one module result,
   and its guest verifies one fixed module-image claim. Therefore that count
   corresponds to one module occurrence per command in this subject. It is not
   a demonstrated count of arbitrary deeper module-proof trees. Generalizing
   coordinators or routes requires an explicit correspondence theorem or a
   stronger checked count representation.

5. **Publication and whole-program safety remain open.** The proof chain does
   not establish store-current authority, durable atomic publication, restart
   authorization, delivery ancestry, no-bypass deployment, complete allocation
   continuity, all twelve lanes, the four intended cross-lane routes, or
   implementation refinement. Disabled or SHADOW lanes do not count as completed
   product features. No live balance migration or authority activation is
   authorized by this review.

The existing route README's signer/allocation/store/publication nonclaims and
ROOT README's profile/refinement/production nonclaims generally preserve these
boundaries. Final artifact descriptions should retain the explicit distinction
between ordered receipt/state-root composition and complete economic semantics.

## Exact reviewed source subjects

All paths are relative to the repository root.

| Source | SHA-256 |
| --- | --- |
| `zk/asset_transfer_route_composer_risc0/shared/src/lib.rs` | `0a242f0a22edb9faa9358919a06fec28e800a88deadb27a1a1978d76df1d7cf3` |
| `zk/global_economic_root_risc0/shared/src/lib.rs` | `44e75a89c14f5de636ee409ac077fe8a3b030ff1cc16f64f2231cddf89ea4f5c` |
| `zk/asset_transfer_route_composer_risc0/methods/guest/src/main.rs` | `f8f169563575dc847150d4041bc4ab89ceebcd2888bb79d11883da195ac4fbfd` |
| `zk/global_economic_root_risc0/methods/root/src/main.rs` | `26232395e8766451228bad1e9828392d043da59502f16cfdf33447fcfce56d15` |
| `zk/asset_transfer_route_composer_risc0/host/src/lib.rs` | `c7dc15e221261037c64f346909df4aab1c1b3778144d47ce3e2aee47b781434d` |
| `zk/global_economic_root_risc0/host/src/lib.rs` | `5efc3723d344339a0f8575f8ece9b71c42389ec110c86841ffdcbc3df20e395f` |
| `zk/global_economic_epoch_risc0/shared/src/lib.rs` | `0a1789fd05159be30464bb0f9081d37450d1249d03186f35ce42c62dfad9a446` |
| `zk/global_economic_epoch_risc0/shared/src/preflight.rs` | `2704b1c6d55a5653904aa32d2e2c1446545c274bf009d6eb975ef3bf7f2d50a8` |
| `zk/global_economic_epoch_risc0/shared/src/aggregation.rs` | `2371d4fbd9cc961253537fed002599328f6056a794ea5fb568f35974a723aac4` |
| `zk/asset_lane_coordinator_risc0/shared/src/lib.rs` | `8d800bf2b9e9d73e705bd58937111ed4ec78284643c4d8d85d192b4e97da2ad5` |
| `zk/global_settlement_abi_v1/src/route_global_state_projection.rs` | `a8e70ae96afd5daa8654031cf2088dba75eb8d29dab90bada08290bb92e2bbbd` |
| `zk/global_settlement_abi_v1/src/asset_transfer_global_allocation.rs` | `96efc2020805b63bb6e7798b9c97aec66207d7e4f45f3450a32e0cc1df556a48` |

Commands used were bounded `sed`/`cat` source reads, `rg` caller and field
searches, `sha256sum` for exact subjects, and `git rev-parse HEAD`. No passing
build or test count is attributed to this review. It is advisory source analysis;
the executable evidence has its own source-bound receipts and retained limits.
