# Custody and global statement V2

Status: bounded native implementation and guest integration candidate. This
specification grants no release, verifier-profile, migration or publication
authority. It extends the explicit V2 custody successor; it does not reinterpret
historical account-only or ABI V1 bytes.

## Economic contract

The typed producer receives an owned ASSET_TRANSFER context, complete custody
lane predecessor, a selected transfer or managed lifecycle command, and complete
global pre/post disclosures. It calls the existing custody coordinator. An
economic rejection returns the unchanged typed rejection before global relation
validation, with identical lane roots and empty effects.

For an accepted command, the existing custody/global refiner must establish the
complete projection, unchanged custody and claimant rows, actual physical supply,
lane/release/writer binding, exact occurrence, replay and global effect relation.
Its current empty-reserve restriction and sender-as-fee-owner admission refusal
remain. No arithmetic, rounding, ownership or command policy changes here.

Only successful refinement produces canonical JSON bytes with these exact fields:

```text
schema: "zenodex/asset-lane-custody-global-statement/v2"
module_journal: the accepted LaneModuleTransitionJournalV2
global_pre_state_root: the refiner's returned predecessor root
global_post_state_root: the refiner's returned successor root
```

The producer reads the roots from the completed refiner result. It does not
validate one snapshot and then reread caller-owned state to select output roots.
Python snapshots context before execution. Rust uses immutable owned inputs.

The journal binds lane states, effects, occurrence and the new coordinator's
semantic receipt commitment. The global roots commit the complete global tables,
including custody and claimant liabilities. Fixed empty terminal/Oracle plans
and derived refinement/delta roots add no independently variable statement
information for this restricted producer.

## Framed witness boundary

`prepare_asset_lane_custody_global_prover_input_v2` prepares this witness from
the context, lane predecessor, command and global predecessor. It captures owned
inputs, executes the existing custody coordinator, derives the global successor,
then emits the unchanged five-component frame. Leaf rejection returns its typed
rejection and empty effects. Invalid structure or global relation produces no
frame. Preparing this witness grants no authentication or publication authority.

The Python and Rust `derive_asset_lane_custody_global_post_v2` functions reuse
the existing global refiner. They project balances and positive supply from the
accepted lane, update only its state root, advance height once, and insert the
occurrence's replay row without overwriting retained rows. Custody, liabilities,
other lane metadata and the remaining global frame are preserved. Existing
height/table ceilings, duplicate replay or occurrence identities, and mismatched
predecessors reject. The current empty-reserve restriction remains in force.

The inner input frame is exactly:

```text
8 bytes:  ZDXCGV2 followed by one zero byte
1 byte:   0 = TRANSFER, 1 = MANAGED_LIFECYCLE
five components, each: length:u32LE followed by exactly length raw bytes
order: context, custody_pre_state, selected command, global_pre, global_post
```

All other route bytes reject. Each component is nonempty and at most 1,048,576
bytes. The frame is at most `8 + 1 + 5*(4 + 1,048,576) = 5,242,909` bytes.
Truncation, oversized lengths and any extra frame bytes reject. The Rust entry
validates the entire structure before decoding context, custody state, selected
command and both global states with their existing exact canonical decoders.
Decoded values then enter the typed producer. A malformed disclosure therefore
can reject before a typed economic rejection; a well-formed disclosure's global
relation is checked only after a successful custody transition.

The Python encoder checks route, exact byte types and individual lengths. It
creates a witness frame; it does not attest canonical or economic validity.
There is no new accepted-witness decoder or caller-constructible authority type.

Guest stdin adds one bounded outer `u32LE` length and requires EOF after the
frame. The guest aborts on transport, decoding, transition or refinement failure
and commits exactly the statement bytes on success. No inner self-image field
or recursive receipt is introduced.

## Conditional receipt verification

The Python integration entry takes the same five typed producer inputs, raw
receipt bytes, and an explicitly configured `GlobalReceiptVerifierV1`. It
requires that exact verifier class and reconstructs its four primitive
configuration fields before preparation. Existing economic rejection returns
unchanged without invoking the verifier. For a successful statement, it invokes
the existing measured transport with the configured image and the exact locally
prepared statement bytes. It returns those bytes only after verification
completes; preparation and verifier failures retain their existing error types.
No caller-supplied expected journal or verification callback is accepted.

This contract depends on a trusted selection of the executable digest and guest
image. Measuring an executable establishes its identity; it does not establish
that arbitrary configured code performs cryptographic checking. The returned
bytes are ordinary data and confer no release, authorization or publication
authority. Every retry verifies again and consumes no replay state.

The fixed custody endpoint selects its compiled guest ELF/image and exact JSON
Receipt codec. It reuses the existing version-1 raw transport protocol and
shared Rust verifier without changing their wire format. The verifier requires
the compiled ELF's actual image, a Succinct receipt, the exact journal, successful
execution and empty assumptions. RISC0 is built with `disable-dev-mode`.
The executable target requires the `compiled-guest` feature and the actual
methods build. Native codec tests build without that feature; they contain no
fallback image or cryptographic-success claim.

## Same-call isolated authentication and receipt consumption

`verify_isolated_authenticated_asset_lane_custody_receipt_v2` combines the
[V2 intent check](ECONOMIC_COMMAND_AUTHENTICATION_V2.md) with this conditional
receipt adapter. It snapshots the candidate, context, typed command, custody
state, both global disclosures and concrete receipt verifier configuration
before signature-verifier I/O. Receipt bytes must have the exact immutable
`bytes` type. The signed envelope must equal the actual owned command's
canonical body bytes, including its origin field.

Before verifier I/O, the pure
`require_asset_lane_custody_profile_binding_v2` predicate reconstructs the
selected profile, context and global predecessor. The profile must be ACTIVE,
its authority epoch must match the context and predecessor, and its governed
command route must select exactly ASSET_TRANSFER. The context's module release
must be that profile's selected ASSET_TRANSFER release. Every predecessor lane
row must match the profile's canonical lane name, release ID and enabled status;
the predecessor profile root must equal the selected profile ID. The profile's
existing constructors validate route/module and coordinator membership.

This explicitly reuses the V1 profile/registry formats without converting V2
states or occurrences. Other enabled lanes and unchanged nonzero disabled roots
remain admissible when their metadata matches the profile. Accepted global
refinement already preserves profile, writer and all lane release/enabled fields
into the successor, so this predicate does not repeat successor validation. This
is a Python admission check; it adds no assertion to the flat Rust guest.

It authenticates the owned context occurrence through the fixed sealed BLS
factory, then invokes the existing custody receipt adapter on those same owned
inputs. Mutation of caller originals during artifact acquisition cannot change
the command, disclosures or configured image later checked. There is no
intermediate authentication handle, caller-supplied journal or deferred use of
the originals.

This entry has explicit rejection order: eager structural snapshot and profile
binding failures precede authentication; signature failure precedes economic execution. After
authentication, typed economic rejection returns unchanged and launches no
receipt verification, including when a well-formed proposed successor has
mismatched profile metadata. Accepted commands undergo the full global relation;
global relation and receipt transport failures propagate.
Successful checking returns ordinary statement bytes and creates no economic,
replay, history, outbox or publication effect.

The integration tests rebind the five retained economic cases to a synthetic
signing profile and independently check their integer row changes. Coherent
foreign writer/module/other-lane metadata and a valid two-lane route reject
before verifier I/O; accepted successor metadata substitutions reject before
receipt verification. The optional
measured-native test executes real sealed BLS verification for all five cases,
including foreign-key failures. Its RISC0 receipt exchange is still a protocol
fixture. Replaying that test requires the same artifact variable and measured
ELF described in the authentication contract:

```bash
python3 -m pytest -q tests/integration/test_authenticated_asset_lane_custody_receipt_v2.py
ZENODEX_BLS_VERIFIER_TEST_BINARY=/path/to/measured/verifier python3 -m pytest -q tests/integration/test_authenticated_asset_lane_custody_receipt_v2.py::test_native_bls_checks_all_five_custody_vectors_before_protocol_receipts
```

## Separately selected custody guest role

`verify_isolated_profiled_asset_lane_custody_receipt_v2` strengthens the isolated
consumer with the explicit `ASSET_LANE_CUSTODY_GLOBAL_V2` role. The normative
[role document](asset-lane-custody-guest-role-v2.json) defines its fixed schema,
journal, receipt and specification coordinates. `AssetLaneCustodyGuestRoleBindingV2`
owns the manifest and artifact rows. Its domain-separated root commits the role,
isolated purpose, profile ID, authority epoch and the complete artifact manifest,
including image, endpoint implementation, source/toolchain commitments and limits.

The expected role root must be selected independently from trusted isolated
configuration. The selector checks that root, active profile, writer epoch and
actual global predecessor before authentication. It never reads a V1 profile
image slot as this role, and no V1 receipt port consumes the four-field journal.
Existing V1 profile decoding and historical verification remain unchanged.

The shell captures the command, context, disclosures and manifests before I/O,
authenticates the exact command occurrence, prepares the statement and measures
the selected receipt endpoint. The existing transport remeasures and executes
sealed bytes, requiring the selected image and exact locally derived journal.
Receipt type, path type and timeout are checked eagerly. Authenticated economic
rejection needs no receipt artifact or verification, even with empty receipt
bytes; it preserves the original typed rejection and empty effects. Receipt
failure propagates and cannot produce success or consume replay state.

Manifest evidence labels are declarations. Source/toolchain commitments must
eventually be qualified against the combined guest and endpoint build. This
binding and the native protocol tests do not establish that qualification.

## Remaining admission obligations

`lean-mathlib/Proofs/AssetLaneCustodyTraceV2.lean` proves that the finite-row
transfer/issue/burn model preserves complete row representability through every
prefix of an arbitrary finite mixed history. Representation is assumed only
for the initial state; selected immutable policies and command widths remain
explicit premises. It also proves exact preservation of custody and registration
through these commands. The proof derives account bounds from total physical
holdings, including custody, rather than assuming bounds for each later state.

Replay with `python3 -m pytest -q
tests/formal/test_lean_asset_lane_custody_trace_v2.py`. The suite checks explicit
theorem signatures, a concrete issue/transfer/reject/burn history against
independently written tables, five false-law refusals, and matching Python
prefixes. Roots remain abstract in this model; it does not prove runtime parser,
resource ceiling, authentication, replay consumption or publication refinement.

The inner economic payload is not a complete admitted CBC profile. Hashing its
route release, subject and grant does not authenticate them. The combined
consumer checks the signed occurrence against supplied governed authorization,
under the authentication contract's trusted profile/status selection premise.
Structural profile binding now establishes writer epoch equality, selected
module membership and predecessor lane metadata consistency. The separate role
now selects fixed custody schema/specification commitments and manifest image
coordinates; its measured image and genuine receipt remain unqualified. No
existing mounted module/coordinator/route/root receipt role accepts this
four-field statement unchanged. Matching the predecessor root establishes
consistency with the supplied disclosures; current
store authority must be acquired and revalidated by the publication shell.

Qualification still requires the actual rebuilt guest image, genuine receipt
verification of the exact image and journal, release/guest-role qualification,
current authentication authority, durable state and atomic publication. A proof
producer or compromised publisher must have no alternate value-writing path.
Native tests and this format do not discharge those obligations.

Retained five-case Python/Rust replay includes custody-bearing transfer, issue,
full account burn preserving custody, dormant issue and return to dormancy.
Regenerate disclosures and independent expected frame hashes with:

```bash
python3 tools/render_asset_lane_custody_statement_v2_golden.py
python3 tools/render_asset_lane_custody_statement_v2_golden.py --check
```
