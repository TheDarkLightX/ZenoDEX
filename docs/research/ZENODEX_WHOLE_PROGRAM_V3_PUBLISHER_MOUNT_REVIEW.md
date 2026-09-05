# V3 publisher mount and BLS integration review

2026-09-05. Git baseline: `dbba47bb7199dd4c5f81ad7fb1fb87abef311873`.
Disposition: bounded mount repair reviewed; mandatory raw-evidence publication
mediation remains open. Authority: `NONE`.

This reviewer independently examined the parent's publisher changes and the
concrete BLS backend. The reviewer authored the receipt ports and synthetic
publisher transport fixtures, so observations about those components are
self-review. The reviewer also supplied the harmless subclass regression below;
the parent implemented its production guard. No independent endorsement of
the reviewer's own port implementation is implied.

The exact reviewed subjects are SHA-256 hashes of these files:

| Subject | SHA-256 |
| --- | --- |
| `src/integration/global_economic_durable_publisher_v1.py` | `f6bf3eaf51724f9bba2270f4ccaa51b14c2a97ab588f0dc5aa4a5719ba3bd80e` |
| `src/integration/economic_command_bls_signature_verifier_v1.py` | `f19644aa318824c8308622f5cc78b218890517661b94f56d8292e94a38da0c82` |
| `tests/integration/test_economic_command_bls_signature_verifier_v1.py` | `8e6f8381fbe50963dfdf16886dc6fb0c8f3298739f5e74e5aa02c80148e4c88d` |
| `tests/integration/test_global_economic_durable_publisher_v1.py` | `345e57f0742b2f61147ace3d01d5671aa9b09d0ba545ded1d1963b3e010966a1` |
| `src/integration/isolated_profile_receipt_ports_v1.py` (self-review) | `aee2c8de566727da7d214fd6af08b291af0966428c7fca4b458aa5f1b9aa6843` |
| `tests/integration/publisher_receipt_port_fixtures_v1.py` (self-review) | `e21b85c2c928a1771c6aeacaa73a8565fff4104f39d35f1f03fe09e970059984` |

PMR-01, repaired: publisher factories dispatched through `cls` without closing
the receiver type. A benign subclass with no overrides was accepted by
`create`; open variants reached journal lookup. This violated exact-class
capability ownership. The retained four-case regression initially failed.
The repaired `create`, `open`, `open_with_monotonic_anchor`, and `_open_v1`
call `_require_exact_publisher_class_v1` before work; the private constructor
also checks `type(self)` before its mint token. All four cases now refuse
before receipt calls or target journal/authority writes. No capability
extraction, external target, or offensive reproduction was used.

At the repaired subject, every constructor path also requires the exact
factory-minted profile-port handle. `_mount_isolated_receipt_ports_v1` checks
the admission type, selected ACTIVE profile, deployment and verifier registry;
the private port accessor returns its original bound verifier. Genesis
verification and complete-bundle checks precede authority installation. The
private constructor remounts against the journal's deployment and retains an
owned profile plus original port/verifier identity and binding coordinates.
This early no-write result applies to rejected handles and receiver types;
later interrupted bootstrap remains the existing recoverable lifecycle.

`publish_economic_epoch` snapshots untrusted values, acquires the predecessor
through the journal's private writer capability, compares the complete
disclosed predecessor, and passes the acquired state to the pure verifier.
It remounts the port and checks identities/profile bytes after verification.
The existing journal CAS still checks current publication and authority at
`BEGIN IMMEDIATE`, with exact committed retry recognized as historical success.
An exact retry after revocation is not fresh publication authorization.
Lower-level journal helpers and the Python process remain trusted boundaries;
this review establishes no deployment-complete writer inventory.

PMR-02, open integration obligation: the publisher still takes an
`EconomicEpochReceiptCandidateV1` containing caller-origin verified routes.
The mounted ROOT verifier establishes its exact execution claim, and the core
also checks route/state/effect structure. Neither operation independently
reauthenticates raw command signatures and leaf receipts through the mounted
ports. The new allocation consumer is also not called by this reviewed
publisher. These are explicit remaining obligations, not properties supplied
by the epoch certificate's name or by immutable witness types.

The BLS backend uses the existing `BLS12_381_G2_BASIC_V1` contract. It accepts
canonical lowercase compressed G1 keys encoded as 98-character `0x` strings,
96-byte compressed G2 signatures, and bounded exact message bytes. It forwards
the core's domain-separated authentication bytes directly to `G2Basic.Verify`,
without another hash or the legacy DEX signing domain. Core authentication
binds policy/authorization/verifier registries, selected release, full intent,
body digest, algorithm and signer; occurrence binding separately checks
chain/deployment/profile/body/route/subject/grant/nonce/objects and height.
Valid cryptography alone does not authorize an unregistered subject.

Installed `py-ecc` reported 8.0.0, matching `requirements-core.lock.txt`.
Inspection of its `G2Basic._CoreVerify` and `KeyValidate` confirmed compressed
point decoding, public-key infinity rejection, subgroup checks and pairing
verification. Tests include genuine signatures, foreign keys/messages and
ciphersuites, invalid encodings/infinity, canonical spelling/type/size bounds,
scope changes, unauthorized subjects, incompatible releases and unavailable
dependencies. Invalid signatures return false; core authentication rejects;
missing/broken backend availability propagates an error. No blocking defect
was found in this bounded BLS implementation review. Measurement of an
arbitrary supplied artifact still does not prove that loaded Python and its
dependencies correspond to it; the documented trusted-process premise remains.

The synthetic publisher fixture calls the actual measured-set/port factories,
remeasures and seals real synthetic ELF bytes, and retains exact request and
response binding. Only process execution is simulated. A separate per-test
MonkeyPatch survives scenario-local `monkeypatch.undo()`, and per-thread
selection keeps competing callbacks distinct. Its callback-pinning test is
behavior evidence over that simulated process; it is not cryptographic
qualification. Real port replay remains separately archived as
`zenodex-v3-profile-ports-replay01.tar.gz`, SHA-256
`ffeeef49e569d52d4eedd78421c04bf35977af342ce258ca909befb98c8d0855`:
five genuine receipts accepted and five altered-journal requests rejected,
with 182 source files and 20 input files unchanged. That evidence verifies
receipts, not the publisher's full economic workflow.

The next mount should require an exact private-minted admission pipeline as
the third argument at all publisher constructors and the private initializer.
Its factory must own the selected profile, receipt ports and concrete BLS
binder; generic pre-bound backends and caller-provided acceptance flags must
not be constructors. ROOT verification remains an internal genesis/history/
epoch operation. Each publication must own raw signed intent, exact command
body, sequenced occurrence, module input/receipt, coordinator receipt, route
receipt and state disclosures; rebuild every witness through existing core
functions and the captured ports; then run allocation and epoch verification
against the acquired predecessor before the unchanged atomic commit. Merely
wrapping old caller-origin witnesses would leave PMR-02 open. Unsupported
lanes and allocation/height shapes must remain explicit typed limitations.

Preserve journal tests by migrating their fixture to the restricted ASSET
profile and canonical BLS signatures, without changing default core fixtures.
Retain existing ROOT callback counts and fault scheduling; record leaf calls
separately and assert their order in dedicated pipeline tests. Raw evidence
must track each altered nonce, predecessor and command body. Existing supplied
core witnesses should be treated as untrusted/ignored fixture input, never as
a product fallback. Preserve all head, conservation, no-effect, history,
revocation, crash and concurrency assertions. Initial ownership/partition and
external authorization remain explicit premises; the retained composed real
fixture has zero module custody and does not qualify nonzero-custody cases.

Executed evidence during this review:

- `pytest -q -p no:cacheprovider` over the BLS backend, core authentication and
  core signature deployment files: **116 passed**, 13.81 seconds.
- The subclass, generic/forged-handle, create/reopen/retry and method-replacement
  tests in the durable publisher file: **14 passed**, 4.38 seconds, after repair.
- Style routing and targeted red-flag scan: two existing recovery exception
  handlers flagged for inspection; no new broad catch in the BLS or mount.

No remote job, guest build, production activation, full critical gate, complete
dependency attestation, initial ownership proof, or whole-program safety
qualification was performed by this review. Later source hashes require a new
review or an explicit scoped delta assessment.
