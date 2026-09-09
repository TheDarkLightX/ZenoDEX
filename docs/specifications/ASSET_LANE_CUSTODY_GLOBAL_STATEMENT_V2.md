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

It authenticates the owned context occurrence through the fixed sealed BLS
factory, then invokes the existing custody receipt adapter on those same owned
inputs. Mutation of caller originals during artifact acquisition cannot change
the command, disclosures or configured image later checked. There is no
intermediate authentication handle, caller-supplied journal or deferred use of
the originals.

This entry has explicit rejection order: eager structural snapshot failures
precede authentication; signature failure precedes economic execution. After
authentication, typed economic rejection returns unchanged and launches no
receipt verification. Global relation and receipt transport failures propagate.
Successful checking returns ordinary statement bytes and creates no economic,
replay, history, outbox or publication effect.

The integration tests rebind the five retained economic cases to a synthetic
signing profile and independently check their integer row changes. The optional
measured-native test executes real sealed BLS verification for all five cases,
including foreign-key failures. Its RISC0 receipt exchange is still a protocol
fixture. Replaying that test requires the same artifact variable and measured
ELF described in the authentication contract:

```bash
python3 -m pytest -q tests/integration/test_authenticated_asset_lane_custody_receipt_v2.py
ZENODEX_BLS_VERIFIER_TEST_BINARY=/path/to/measured/verifier python3 -m pytest -q tests/integration/test_authenticated_asset_lane_custody_receipt_v2.py::test_native_bls_checks_all_five_custody_vectors_before_protocol_receipts
```

## Remaining admission obligations

The inner economic payload is not a complete admitted CBC profile. Hashing its
route release, subject and grant does not authenticate them. The combined
consumer checks the signed occurrence against supplied governed authorization,
under the authentication contract's trusted profile/status selection premise.
It does not establish writer epoch equality with the profile, context/module
membership in its selected lane release, or the flat guest's admitted role,
specification and measured image. Do not equate that image with a V1 profile
image slot without a defined role mapping. Matching the
predecessor root establishes consistency with the supplied disclosures; current
store authority must be acquired and revalidated by the publication shell.

Qualification still requires the actual rebuilt guest image, genuine receipt
verification of the exact image and journal, explicit release/profile/context
admission, current authentication authority, durable state and atomic publication. A proof
producer or compromised publisher must have no alternate value-writing path.
Native tests and this format do not discharge those obligations.

Retained five-case Python/Rust replay includes custody-bearing transfer, issue,
full account burn preserving custody, dormant issue and return to dormancy.
Regenerate disclosures and independent expected frame hashes with:

```bash
python3 tools/render_asset_lane_custody_statement_v2_golden.py
python3 tools/render_asset_lane_custody_statement_v2_golden.py --check
```
