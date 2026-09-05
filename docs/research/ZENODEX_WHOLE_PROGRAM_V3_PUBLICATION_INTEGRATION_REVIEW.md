# V3 isolated publication integration review

Status: **ADVISORY IMPLEMENTATION CONTRACT; NOT QUALIFIED**. This review closes
no formal or value-movement gate and grants no deployment, migration or writer
authority. It identifies a concrete next implementation packet for W03/W04/W06.

## Exact reviewed subjects

Historical implementation references below are at
`c6a9fd028ded9224427a645c1217d0ce576f78af`. The reviewed V3 plan bundle is
`bde0fac341f312b8b12b96d0bf1477a7091cdc3f`; the checkout HEAD observed during this
review was `051ecaa47682c2116d99c58e99ace3d800cfedf0`. Concurrent implementation
files were read as candidates, with these SHA-256 snapshots:

| Candidate file | SHA-256 |
|---|---|
| `src/integration/global_receipt_verifier_v1.py` | `0393f29114b9ceb0ef26ac65baa022eb4f831fb7f0971ee0ca52d83dcf5a07a9` |
| `src/integration/global_allocation_shadow_v1.py` | `fe1f63399bcf64d5d4d28b1c989455f022b49ada3dda6db7ec900015e0c45719` |
| `src/core/global_accounting_allocation_projection_v1.py` | `10433a18db25b4c2e6932d08c9749083daec881aff2bb58a77fdb64db31c364f` |
| `zk/global_economic_epoch_risc0/host/src/bin/verify_receipt_v1.rs` | `1241a627a16e5a44f05fb20ba0f330eb6b5e581647e31d9ba4354efae41e9a3c` |

The existing ASSET_TRANSFER and asset-coordinator guest crates are present in
the baseline Git tree. Sparse working-directory omissions are not missing-source
findings. Their real receipt qualification is separate from source existence.

## Existing publication contract

`VerifiedDurableEconomicPublisherV1.create/open` in
`src/integration/global_economic_durable_publisher_v1.py` reconstructs a verified
genesis, pins a profile and `BoundEconomicReceiptVerifierV1`, and opens an epoch
journal attached to the matching economic-authority store. The constructor mints
a publisher-local binding token and retains a journal-local write capability.

`publish_economic_epoch` currently performs these operations:

1. Own the caller's source head, epoch candidate and complete post-state body.
2. Resolve the named historical source head, compare its coordinates with the
   candidate pre-state, and obtain a current CAS token.
3. Call `_verify_economic_epoch_for_publisher_v1`, which rechecks profile,
   occurrences, routes, effects and disclosed state refinement, verifies the
   exact root receipt, and mints a publisher-bound `VerifiedEconomicEpochV1`.
4. Recheck the retained verifier/profile selection and body binding, derive the
   publication record and complete durable bundle internally, then commit it.

`GlobalEconomicEpochJournalV1._commit_under_lock_v1` owns the existing
linearization point: `BEGIN IMMEDIATE`, full stored-head validation, exact
committed retry recognition, current-authority comparison, source/sequence CAS,
history capacity check, bundle insert, head update, and `COMMIT`. The bundle
contains the complete post-state, including replay state, history root and
outbox rows, plus effect plan, certificate, publication record and root receipt.
The source is `prepare_durable_economic_epoch_bundle_v1` and the closed payload
field sets in `src/integration/global_economic_durable_epoch_v1.py`.

An exact committed retry is recognized before fresh authority admission and
returns the retained result without a new economic transition. Preserve that
contract after revocation. A response lost after `COMMIT` is indeterminate
client knowledge, not precommit rejection. The existing monotonic-anchor code
already distinguishes several such outcomes.

`_validate_store_v1` checks canonical bundle integrity, hashes and lineage. It
does not replay every stored cryptographic receipt. A read-only SHADOW capture
therefore supplies local consistency, not writer authority or independent
authentication. The new publication path must acquire through its own journal
capability and bind trusted history or explicitly reverify retained receipts.

## Confirmed integration gaps

| Gap | Source and consequence | Disposition |
|---|---|---|
| One root image is required for two different current guests | `economic_initial_state_v1.py:405` and `economic_initial_state_publisher_verification_v1.py:71` require the initial certificate/verifier image to equal `profile.root_image_id`; `global_economic_proof_v1.py:1461` uses the same profile field for epochs. The initial host requires its own compiled image (`zk/economic_initial_state_risc0/host/src/lib.rs:153,308`), while the epoch host requires its different compiled image (`zk/global_economic_epoch_risc0/host/src/lib.rs:210`). | Implement a fresh unified root guest as described below. Existing recording backends cannot qualify genuine genesis-to-epoch publication. |
| Receipt-purpose and profile-status contracts conflict | The publisher requires an ACTIVE profile but binds purpose RESEARCH_SHADOW. Bound profile leaf verification requires SHADOW profile/release and forbids new objects. Generic module/coordinator admission instead requires ACTIVE_NEW releases. | Add an explicit isolated-qualification selection contract and narrow fixed-profile receipt ports. Keep SHADOW observational. |
| The measured bytes and backend are separate public binder arguments | `bind_economic_receipt_verifier_deployment_v1` measures caller-supplied bytes, then retains a separately supplied backend callable. | A shell-owned factory must construct the bridge from the same measured artifact and selected image; do not accept an arbitrary backend or caller assurance flag. |
| Source-state acquisition is incomplete | The publisher resolves the source head, but accepts the pre-state disclosure from the candidate. The journal has complete source bundles yet exports primarily head views. | Add one capability-bound source snapshot operation returning owned state, profile/policy material, source bundle, current tip and CAS coordinates from one read transaction. |
| Allocation admission is not a publication prerequisite | The publisher never calls the allocation projection/checker. SHADOW deliberately supplies no authority. | Add a pure source/post-allocation check before the existing journal commit. Leave economic commit identity and journal formats unchanged when the check derives only already-bound facts. |
| Full historical receipt-backed fragment reconstruction is unavailable | The epoch payload retains the root certificate/receipt and complete global state, but not module inputs, private-port preimages, module journals or their receipts. `receipt_archive_root` is a commitment, not an archive reader. | Derive the required predecessor economic view; retain new data only if exact historical fragment/witness reconstruction is required. |

The Rust agent owns the module-state/coordinator-state root relation. This
review relies on its resolution and does not duplicate that implementation.

## Fresh unified root guest: preferred bounded repair

The existing V1 profile has one content-bound `root_image_id`; initialization
and ordinary epoch checking both deliberately bind that field. The ABI reference
also describes root-receipt delegation after exact profile/image and journal
checks (`GLOBAL_SETTLEMENT_ABI_V1_REFERENCE_20260805.md:358`). A fresh root
program supporting both statement families is consistent with that contract.

Create only a new crate tree, `zk/global_economic_root_risc0/`, with this packet:

| New surface | Exact responsibility |
|---|---|
| `Cargo.toml`, `Cargo.lock`, `rust-toolchain.toml` | Pin the existing compatible Rust 1.90/RISC0 dependency versions; reuse the two existing shared crates by path. Record the resolved lock and measured build. |
| `shared/src/lib.rs` and `shared/tests/root_dispatch.rs` | Closed versioned private input tag, for example `InitialStateV1(canonical_initial_bytes)` or `RecursiveEpochV1(existing_recursive_input)`. Canonical round-trip and whole-frame bounds precede dispatch. Reuse initial-state canonical preparation and all three epoch preflights. Return exact journal bytes and an ordered immutable list of required child claims. |
| `methods/root/src/main.rs`, `methods/build.rs`, `methods/src/lib.rs` | Decode one bounded canonical input, run the selected shared preflight, verify every and only prepared child claim through `env::verify`, and commit the unchanged prepared journal bytes. Unknown tags and rejected branches abort before journal emission. |
| `host/src/lib.rs` | Measure the new compiled ELF/image, bind initial profile and initial statement image to it, bind epoch certificate image to it, match child receipts exactly by count/order/image/journal, add only those assumptions, and verify a fully resolved successful Succinct root receipt against the new image. |
| `host/src/bin/verify_receipt_v1.rs` | Reuse the verifier agent's explicit-ELF-and-ID endpoint helper. Keep the V1 subprocess frame and exact response contract; this endpoint selects only the new compiled root method. |
| `host/tests/receipt_admission.rs`, `host/tests/real_initialization_epoch.rs` | Canonical/parser and exact-context controls, then real initialization and epoch receipts sharing one new profile/image. Retain clear structural-child versus actual-module qualification labels. |
| `README.md` | Source/lock/image/ELF pins, complete replay command, isolated scope and residual obligations. |

The private tag is a new input ABI. It does not alter any old receipt, profile,
initialization journal, epoch journal or aggregation journal. Both old guest
crates and their historical host checks remain intact. A new image creates a
new profile identity and requires rebuilt source/toolchain/verifier evidence;
old state is never relabeled under the new profile. Source manifests retain
provenance meaning and never become state-head or finality witnesses.

For aggregated epochs, preserve the existing
`preflight_aggregated_economic_epoch_guest_input_v1` requirement that every
command-aggregation child image equals `certificate.root_image_id`. The new host
binds that certificate field to the measured new root image. Aggregation groups
must therefore be proved by the new root's aggregation branch; old epoch-image
aggregation receipts cannot be substituted. Direct route children retain their
own governed route images. Preserve 1..8 route receipts and 1..64 epoch commands,
all existing exact partition/order checks, and empty unresolved assumptions on
the final root receipt.

Every branch emits its existing closed typed journal shape. Initialization and
epoch share the ABI schema identifier, so schema text alone cannot separate them.
Host and Python
admission select the expected statement kind from their operation and recompute
the expected bytes; a correct initialization proof presented as an epoch must
fail exact journal comparison. No unconditional passthrough or generic
`commit(caller_bytes)` branch is permitted. Accepted-only proof statements with
abort-on-rejection remain sufficient; separately verify refusal behavior.

Compared with separate image fields in a versioned profile, the unified root
adds one measured executable and private input dispatcher while preserving the
public binding surfaces. Separate fields would require a profile/certificate
schema successor, new content roots, decoders and historical compatibility rules
across Python, Rust, guests and publisher admission. That larger option is not
needed to remove the currently demonstrated image mismatch. Compilation cost
and real-proof performance of the new root remain unmeasured.

## Isolated receipt selection and snapshot contract

Use a closed purpose such as `ISOLATED_QUALIFICATION` with an explicit immutable
relation to the selected profile and verifier release. It permits the exact
restricted profile's ACTIVE/ACTIVE_NEW economic semantics on a newly created
isolated store, while leaving production selection rejected. RESEARCH_SHADOW
continues to permit observation only. No `allow_active`, `verified` or
`allocation_ok` argument may upgrade an input.

The shell factory owns the measured backend and exact profile filter. It checks
all profile, verifier registry, release manifest, deployment and image bindings,
then creates narrowly scoped root/module/coordinator/route receipt ports. Each
port implements the existing receipt protocol while selecting only its pinned
guest from the profile. The current epoch-only ELF endpoint cannot verify other
guest images; each endpoint must supply its own compiled image to the common
verification helper. The existing 32 MiB measured-artifact bound also applies,
even though the raw Python executable reader permits 128 MiB.

Acquire the publication source through a new private journal operation, rather
than through `ReadOnlyAllocationSourceV1`. In one read transaction, return:

```text
SourceSnapshot = requested committed source bundle + exact decoded state
               + activation profile/policy components
               + current tip + current authority coordinates + CAS token
```

For a current source, this supplies the pre-state used by the core. For an older
source, retain enough information to recognize an exact committed retry; an
uncommitted stale transition must fail the final CAS. Never replace historical
retry behavior with a blanket requirement that every request reference the tip.
After proving/checking outside the write transaction, the existing
`BEGIN IMMEDIATE` path revalidates current authority and the selected source.

## What predecessor allocation information is sufficient?

For the currently supported one-lane shape, economic rows are derivable from
the exact committed global state: custody gives physical controlled locations,
liabilities give claimant rows, and reserves/outbox/terminal tables retain their
own meanings. They must not be added to balances as duplicate physical holdings.
The projection currently refuses multiple enabled lanes and unsupported row
families; these refusals remain product-scope gaps.

For ASSET_TRANSFER, rebuild the shared asset-lane projection from committed
balances, supplies and custody plus the pinned asset/fee policy roots. Require
its root to equal the stored coordinator lane root. Require the next admitted
module's private-port pre-state to equal that rebuilt projection, and bind its
native module root through the independently reviewed module/coordinator
relation. Recompute the transition from its authenticated command and require
the private-port post-state and full global post-state projection to agree.

That is sufficient in principle for **predecessor economic continuity**, under
the selected ownership policy and authenticated-store premise. It is not
sufficient to reconstruct the exact old `VerifiedLaneAllocationFragmentV1`:
that witness also carries module-journal, semantic receipt, receipt-digest and
image metadata absent from the stored epoch payload. In particular, a root
hash cannot recover its undisclosed module/private-port preimage.

The current `produce_asset_transfer_fragment_v1` reads only lane identity,
enabled/producer kind, release and lane-state root from `prior_fragment`; it
does not consume its old allocation rows or binding root. A narrow predecessor
state view is therefore a better candidate input than fabricating an old
receipt-backed certificate. Factor a successor pure admission helper around
the data actually needed, retaining old decoders and receipt checks. Mint the
new allocation witness from the internally verified current module receipt;
derive binding roots from that witness rather than a second caller argument.

If exact historical allocation-certificate replay is later required, retain the
missing module/private-port preimages and receipt archive under their existing
commitments with bounded availability rules. Demonstrate missing information
before adding any new commitment. An `allocation_root` by itself restores none
of those preimages and should not be added merely to satisfy the old helper's
parameter shape.

Nonempty custody introduces a genuine unresolved question: which pinned policy
authorizes the claimant split? Fragment coverage proves totals per asset/domain,
and certificate equality binds claimant rows to global liabilities, but neither
establishes that a freely chosen liability partition is the right policy. The
current fragment-admission source explicitly retains this nonclaim. The minimum
isolated transfer can use accounts-only balances and empty custody/liability
tables, which exercises value movement without selecting a custody policy.

## Smallest meaningful isolated acceptance

Use one ordinary registered transfer asset, one ASSET_TRANSFER module, its real
asset coordinator, and one real transfer route. Start with a newly certified
accounts-only state; use existing precision and authorization rules. Create no
live migration or external delivery path. Freeze the exact new root, module,
coordinator, route, host verifier and policy artifacts together.

1. Prove initialization under the new root image; admit it through the measured
   Python bridge and create the isolated publisher/store.
2. Authenticate Alice's nonzero transfer to Bob using the selected signature
   verifier. Acquire the committed source inside the publisher. Recompute the
   module transition; verify real module, coordinator and route receipts; mint
   allocation evidence internally and check the state-derived certificate.
3. Prove and verify the epoch under the same root image, then commit through the
   existing single journal transaction. Read back complete state, replay,
   history, receipt and the empty outbox; compare with an independent reference.
4. Close and reopen through fresh authority acquisition. Publish a second
   authorized transfer using the stored first epoch as predecessor. Retry both
   exact committed epochs and verify a single retained history entry for each.

Required isolated controls cover: correct proof/wrong context; unauthorized but
conserving movement; absent or misbound allocation witness; mismatched stored
predecessor/private port; concurrent winner; revoked authority during receipt
verification; exact retry after revocation; capacity/overflow rejection;
precommit crash and postcommit lost response; missing authority on restart; and
SHADOW failure with unchanged economic outcome. Use logical state/history/replay/
outbox observations, not equality of SQLite housekeeping bytes.

The existing retained tests in
`tests/integration/test_global_economic_durable_publisher_v1.py` already define
useful shell histories, including create/publish/reopen/retry, competing writers,
inflight revocation and lost acknowledgment. Their recording receipt backends
are shell-contract evidence only. Real proofs through the measured bridge must
replace that assumption in the new isolated qualification test.

## Remaining nonclaims and next action

This was a bounded static review; no proof build, source change, runtime
activation, external call or economic test was performed. The new root packet
is implementable without choosing an economic policy or changing old public
journals. Its host proof recipe must be run remotely after coordinating the
verifier agent's existing GPU job and build directory ownership.

Genesis source authorization, release evidence admission, authenticated restart
and rollback protection, the module/coordinator refinement relation, the
custody ownership policy, all-lane lifecycle completion, actual outbox delivery,
and deployment-complete writer exclusion remain distinct obligations. Existing
tests explicitly retain replaced-authority-inode, separate-migration-writer,
and restored-store rollback findings. The unified guest does not close them.

Recommended immediate implementation: the new root crate and host
initialization-to-epoch recipe, followed by the isolated-purpose receipt factory
and capability-bound source snapshot. Add the allocation consumer after the
module/coordinator relation is reviewed. Keep the same durable commit point.


## Approved bounded asset route successor packet

The tracked `c6a9fd028ded9224427a645c1217d0ce576f78af` Git inventory contains
`asset_transfer_module_risc0`, `asset_lane_coordinator_risc0` and
`perps_margin_route_composer_risc0`. It contains no asset-transfer route guest.
This conclusion uses `git ls-tree -r --name-only`, independently of sparse
checkout materialization. Parent integration approved the following new crate
after this read-only assessment; no existing route/profile journal changes are
part of that approval.

The perps route shared `prepare_perps_margin_route_composer_v1` calls the
perps-specific lane preflight and copies `declared_pre_state_root` and
`declared_post_state_root` into the route journal. Its documented statement is
structural. Reusing that root-copy as the asset route's complete economic
relation would leave an economic obligation open.

Existing Python `global_economic_proof_v1._derive_route_state_evidence_roots_v1`
uses both `project_route_global_state_v1` and
`refine_route_global_economic_state_effects_v1`. Both have actual Rust twins in
`zk/global_settlement_abi_v1/src/route_global_state_projection.rs` and
`global_economic_state_effect_refinement.rs`. The projection binds the full
state hashes, exact selected lane journal roots and unchanged unselected lanes.
The separate refinement binds sparse amount and supply tables, replay, height
and effects while refusing unsupported transitions. Neither establishes
cryptography, predecessor-store authenticity or publication authority.

Owned successor paths are `zk/asset_transfer_route_composer_risc0/**`, with
small shared/methods/host packages and tests following the root crate layout.
The private input will contain the exact coordinator input, immutable complete
profile/registries, governed route and occurrence, and disclosed pre/post
global states. It will derive one canonical existing `RouteCompositionJournalV1`
from the accepted coordinator journal and those state hashes, check the existing
route projection and economic refinement, and bind the actual module private
projection to the complete state through the restricted W04 relation. Existing
pure helpers will be reused; access changes outside this crate require a
separate owned packet. No duplicate economic arithmetic or policy constants
will be chosen in tests.

The guest will verify exactly one coordinator assumption under the selected
image and exact lane journal before committing the derived route journal. The
host will require the compiled route image and the exact compiled coordinator
image, Succinct receipts, canonical encoding, exact child count and journal.
The Python/Rust route verifier relation already exists in
`route_composition_receipt_verification_v1.py` and
`route_composition_receipt_verification.rs`: both bind the governed route,
occurrence, ordered verified lanes, canonical journal and selected image before
constructing a verification witness.

A necessary build gate precedes this successor: the existing coordinator guest
uses the fixed `ASSET_TRANSFER_MODULE_IMAGE_ID_V1`. A rebuilt module must match
that pin; otherwise a reviewed fixed-pin update creates a new coordinator
image/release/profile subject while historical sources and artifacts remain
preserved. A caller-provided image cannot replace that obligation. The parent
and verifier agent own this pin review.

Acceptance requires a positive real module/coordinator/route chain, exact
Python/Rust journal and refinement agreement, and isolated negative tests for
wrong context, whole-state amount drift, unauthorized but conserving movement,
missing or duplicated child receipts, foreign image, wrong journal, replay,
unsupported state and resource bounds. The eventual root receipt must consume
this real route receipt. The structural leaf used by the root dispatch test
remains explicitly insufficient for this economic route claim. Store-current
source acquisition, signing authority, allocation publication and final atomic
commit remain separately mounted shell obligations.

## Implementation checkpoint, 2026-09-05

The earlier static assessment above is retained as the pre-implementation
record. The new unified root crate is now implemented and has genuine Succinct
receipt evidence under one measured image for initialization, direct epoch,
command aggregation and aggregated epoch. The initial/direct test generated
four proofs; the nine-command aggregation generated twelve, and the admitted
64-command ceiling generated seventy-three. The 65-command certificate was
rejected before proving with `Epoch(InvalidBounds("epoch command count"))`.
The initial maximum-bound test's fixture-construction failure was preserved;
its successor presents the excessive certificate directly to the preflight.

The direct raw-executor controls first verify a retained exact epoch receipt,
then bypass the host guard and run the same guest input with missing or wrong
child assumptions. Both were refused by guest `sys_verify_integrity` because
the required claim was absent. This closes the previous host-only evidence gap
for the guest assumption loop. It does not introduce a two-sided reject journal.

The root evidence archive identities are:

| Scope | SHA-256 |
| --- | --- |
| Initialization/direct, nine-command aggregation, raw guest controls | `dc2843430247e087e9c0220e0cf3916c12b6d1bd41b9005786ea23ae189274d7` |
| 64-command ceiling, exact 65-command refusal and earlier fixture-failure log | `fbdd484426fc452463b8f9ed8b66f6b8fdc7dc12d052170089ae7c8366fcaf52` |
| Source08 manifest, 287 frozen relative source paths | `923b11557e0893fdf0f035278f4823639b7ea77bea951319bec589f917dc4255` |

The final root run retained the same measured image as the earlier dispatch
proofs. It took 121.45 seconds for 73 proof computations, with a 33,579-byte
epoch frame, 14,588-byte journal and 300,322-byte postcard receipt. These are
isolated measurements and do not establish a throughput guarantee. The route
children in these root tests are explicitly structural test leaves.

The new asset route's pure preflight, actual fixed-image host, verification
endpoint and input-file proof exporter are implemented. Candidate source02
passed eleven CPU checks and strict Clippy. Its exported state projection and
state/effect refinement roots agree exactly with the independent Python core;
integer transfer arithmetic and a conserved misattribution mutant were checked
separately. The later small shared-code split removes overlong functions while
preserving guard order and requires replay before any new proof subject is
frozen. The exporter accepts a canonical input file so the final measured
profile and height-zero predecessor can be supplied without recompiling guests.

Real asset route proof qualification remains pending at this checkpoint.
The coordinator's fixed module-image check correctly exposed a build identity
gap: the compiler retained an absolute shared-source panic location in the
module ELF, so equal source bytes compiled from another checkout path produced
a different image. A stable composed build path or reviewed compiler path
remapping must precede the final module/coordinator/route/root image and profile
freeze. No image check was bypassed. Historical proofs remain evidence for
their exact measured ELFs and build subjects.

Signer authentication, certified initial allocation partition, immutable store
source provenance, allocation publication, the single durable commit point and
production writer exclusion remain distinct obligations. Neither this route
preflight nor its synthetic fixture evidence labels grant those capabilities.
