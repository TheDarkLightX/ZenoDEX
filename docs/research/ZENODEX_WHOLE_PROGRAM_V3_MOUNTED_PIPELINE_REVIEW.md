# V3 mounted raw-evidence pipeline review

2026-09-05. Git baseline: `d02e2693476e597bbbb7cae75fb2905e004b0fff`.
Disposition: restricted isolated integration reviewed after MPR-01 repair.
Authority: `NONE`. No production promotion or whole-program safety verdict.

The reviewer independently examined the parent's publisher implementation and
Maxwell's raw-evidence pipeline, concrete BLS backend and signature-purpose
changes. The reviewer authored the earlier receipt ports, extracted and adapted
the shared test fixtures, and added the two-row regression below. Those parts
are self-review. Existing pipeline test assertions originated with Maxwell;
their fixture migration is not an independent cryptographic implementation.

## Findings and disposition

**MPR-01, repaired: enforce the isolated vector bound before deep copying.**
The publisher previously called `_snapshot_economic_epoch_candidate_v1` before
the pipeline's `_require_single_occurrence_shape_v1`. The general candidate
constructor bounds command count, but permits extra route journals and route
effect plans. This made the mounted path copy out-of-scope parallel rows before
refusal. Two ordinary rows, with a sentinel replacing deep snapshot after
publisher creation, demonstrated the ordering defect without a load test.
Both retained cases failed against publisher SHA-256
`7811cc8674a7a8ac58d2ca99fc6778fe0039ed5b55ef27b7e1807ebc49c388f3`.
The parent now invokes the existing shared shape guard immediately after exact
candidate-type checking, before `replace` or deep snapshot. Both cases pass;
the entire nine-case publication suite passes. The regression observes no
snapshot call, no additional ROOT call, unchanged head and unchanged economic
rows. This closes the identified ordering defect, not all resource-exhaustion
or whole-runtime totality obligations.

**Earlier PMR-02, mounted in this subject:** publisher construction requires an
exact factory-minted `IsolatedAssetReceiptPipelineV1`; generic bound verifiers,
bare measured ports and unregistered handles are refused. Publication requires
raw evidence and discards caller route witnesses before any witness field is
read. The live call path now includes fresh signature, module, coordinator,
route and allocation admission before ROOT verification and commit. No new
economic acceptance or origin bypass was found within that restricted path.

## Trace and authority assessment

`VerifiedDurableEconomicPublisherV1.create`, `open`,
`open_with_monotonic_anchor`, `_open_v1` and the private constructor retain
exact-class checks. `_mount_isolated_receipt_ports_v1` compares the minted
pipeline's owned profile, deployment and complete policy bytes to the supplied
initial admission. `_prepare_verified_activation_v1` verifies initialization
and checks the complete activation bundle before creating journal/authority
state. The private constructor remounts using policy bytes from that journal's
activation. Rejected origin/type checks precede target filesystem writes;
later interrupted bootstrap retains its existing recovery contract.

Publication snapshots the candidate with `verified_routes=()` and owns the
body. `_publication_source_for_verified_publisher_v1` requires the exact
journal's private writer capability and reads validated activation, source,
current head and authority under one SQLite transaction. It decodes the full
stored predecessor and checks its root, chain, deployment, profile, writer
epoch and height against the committed head. Publication compares complete
pre-state values and remounts the pipeline against the acquired activation
policy. The ROOT core boundary receives the actual acquired state object.

The pipeline factory owns profile/policy snapshots, accepts only minted
measured receipt ports and internally constructs the concrete G2Basic backend.
It fixes `ISOLATED_QUALIFICATION`; there is no supplied backend or trust flag.
Raw intent, envelope, authorization/signature/asset registries, module input
and receipt bytes are snapshotted before any receipt callback. Profile-policy
bindings select authorization and signature releases. Authentication checks
the exact core message, signer, grant, subject, body, nonce and validity;
occurrence binding additionally checks every signed occurrence coordinate.
The module transition is recomputed, its release/route binding is rebuilt,
and the module receipt verifies the exact selected image/journal. Fresh
receipt-backed coordination supplies the exact coordinator statement; fresh
route verification binds its selected release and ordered lane occurrence.
No supplied accepted module or authentication witness enters this public API.

`_admit_source_bound_epoch_v1` passes those fresh module witnesses and acquired
predecessor into `check_asset_transfer_epoch_allocation_v1`. That fold checks
occurrence/module/route membership, each prospective allocation, complete
projection/certificate acceptance and final state equality. Its ordinary
result is consumed immediately; callers cannot submit a replacement verdict.
The publisher then verifies ROOT, rechecks selected pipeline/ports/verifier
identity and profile bytes, binds certificate/effects/body, and constructs the
complete durable epoch bundle. The epoch-position arithmetic/refinement is
separately reviewed and tested; this integration review is not its proof.

The sole economic linearization remains the journal's `BEGIN IMMEDIATE`
transaction and final `COMMIT`. The journal recognizes byte-identical committed
retry before requiring fresh authority. Otherwise it rechecks authority and
source/CAS coordinates, bounds history, inserts the complete epoch and advances
the head atomically. Authentication and receipt witnesses consume no replay
state before that commit. Signature, leaf and allocation failures therefore
leave economic rows PRE. Concurrent winners and SQLite housekeeping may still
change physical files, so byte-for-byte database identity is not the contract.

The anchored path distinguishes commit acknowledgment/anchor failure and exact
recovery, preserving process-control exceptions. The default unanchored path
can rethrow an unexpected journal exception after a possible commit; a generic
exception is consequently not evidence of precommit rejection. Exact retry
and retained history resolve that ambiguity. A uniform client-facing outcome
taxonomy for unanchored unexpected exceptions remains an operational task.

## Purpose and historical compatibility

Production authentication and binding defaults remain `PRODUCTION_NEW`, with
ACTIVE releases and the full production evidence requirement. Isolated
selection requires a nonaccepting SHADOW signature release and the five named
baseline evidence statuses. Unknown purpose types, retired/revoked/draining
releases, insufficient evidence, cross-purpose use and foreign deployment or
profile bindings fail closed. The purpose survives bound verifier, authenticated
intent and sequenced command handles. Callback revalidation includes purpose
and backend identity. Isolated binding identities wrap the historical binding
root in separate domains. AST comparison with the Git baseline confirmed that
all three production canonical hash expressions remain exactly unchanged.
The signing-message wire format and existing profile/receipt journals retain
their formats; changed policies still produce changed profile/signing subjects.

The generic module receipt API commits the authenticated command's binding root
but does not independently expose or establish production qualification. Its
reuse by the isolated pipeline is intentional. A future production pipeline
must freshly authenticate under the production purpose or explicitly enforce
the required purpose when consuming command witnesses. A module witness alone
does not establish production authorization. No current mounted writer accepts
a caller-supplied module witness through this path.

## Executable observations

These are isolated deterministic tests, not new RISC0 proof generation:

- `python3 -m pytest -q tests/core/test_economic_command_signature_verifier_purpose_v1.py tests/core/test_economic_command_authentication_v1.py tests/integration/test_economic_command_bls_signature_verifier_v1.py tests/integration/test_isolated_asset_receipt_pipeline_v1.py`: **150 passed**, 38.25 seconds.
- The migrated publisher/source/legacy-factory/publication suites: **84 passed**, 129.54 seconds, before MPR-01's new two cases and guard. Existing state/history/nonce/concurrency/fault assertions were preserved. An AST comparison found the same 44 publisher and four source test functions, with only the required API-signature assertion changed.
- `python3 -m pytest -q tests/integration/test_isolated_asset_publication_v1.py -k extra_parallel_row`: **two failures** before repair; only two ordinary rows were used.
- `python3 -m pytest -q tests/integration/test_isolated_asset_publication_v1.py`: **nine passed**, 14.61 seconds after repair. Scoped Ruff also passed.

The tests use actual G2Basic signatures and explicitly simulated RISC0 process
replies behind the real measured-set/port framing and sealing. They check raw
authorization failures before receipt callbacks, each leaf refusal, mandatory
allocation refusal followed by a valid resubmission, alias mutation isolation,
source/policy/profile mismatch, opaque origin, and existing ROOT failure and
recovery behavior. The fixture captures ROOT callbacks separately so historical
fault scheduling and callback counts retain their purpose. Its scenario-local
`monkeypatch.undo()` does not remove the separately owned transport fixture.

## Remaining nonclaims

The mounted pipeline admits one ASSET_TRANSFER occurrence and retains the
coordinator's nonzero-custody restriction. It does not enable the other eleven
lanes or close cross-lane routes. Initial ownership, profile/release admission,
loaded Python/dependency integrity and correspondence to the measured BLS
artifact remain explicit premises. The existing genuine five-receipt fixture
uses a different signature-policy subject; this new BLS policy requires new
proofs before a genuine fully mounted chain can be claimed.

Committed source acquisition relies on checked original publication and trusted
store/process ancestry; it does not cryptographically replay stored history.
The durable epoch contains its receipt, state and effects, while raw BLS and
leaf disclosures are transient here. Historical authentication replay and
complete restart provenance remain W11 work. The retained authority rollback,
inode replacement, separate migration/old-writer and deployment no-bypass gaps
remain blockers. ROOT's structural execution statement does not become a full
economic-preservation theorem through this mount. Full formal refinement,
outbox/delivery lifecycle and production qualification are not claimed.

No remote job, heavy build, live activation, migration or target exploitation
was performed for this review. Parent-wide final gates and separate independent
reviews remain separate evidence and are not inferred from these results.

## Exact reviewed source subject

Unlisted unchanged dependencies are anchored to the Git baseline above. This
table identifies the reviewed integration/purpose sources and the changing
allocation callees; it is not a whole-deployment dependency manifest.

| Path | SHA-256 |
| --- | --- |
| `src/integration/global_economic_durable_publisher_v1.py` | `110b593788fc1abf732975d5f24e512549f87594935ee9a12417fd48d7790768` |
| `src/integration/isolated_asset_receipt_pipeline_v1.py` | `9e8d763a18f5b327cc2656d48d07d5cd1d8d2399b5d3f8fb2d8e297a36b4daf7` |
| `src/integration/economic_command_bls_signature_verifier_v1.py` | `3dbf54e13400fe84f78bb1be78238c037b43e8e068b4d07bbda68290652a75f9` |
| `src/integration/economic_command_signature_verifier_deployment_v1.py` | `a9f93aa7788c55260907c20ac155b62ae385c37d3e60dd000b00a11ad517b55c` |
| `src/core/economic_command_authentication_v1.py` | `187002fb050c9509fda60340a6ff6920e6e5da48eb69620b10fdef33d2697bf5` |
| `src/core/economic_command_authentication_witness_v1.py` | `077166fd0ba242af3e8ea8a0ed8a4535b7ebba872128f1ea47364354800c9ada` |
| `src/core/economic_command_signature_verifier_capability_v1.py` | `2a6b8e7030c126bd4c5e307241e5f3200a4dda68a3bebd63fbee4eb455b3aa4c` |
| `src/core/economic_command_signature_verifier_deployment_v1.py` | `b211532aa50ea90747b181cad97cdbdcce5ca65e94907b669f2283031cbe98b6` |
| `src/core/economic_command_signature_verifier_registry_v1.py` | `001302fd7816d130487e5c0efc01bdaffe9340435b1098ad193bd2e47133d7aa` |
| `src/core/asset_transfer_epoch_allocation_v1.py` | `34a5012d84f130921ce80c87e367c56bfe92d6e6d7c59ccd6774d8fbc3bcb071` |
| `src/core/asset_transfer_epoch_position_v1.py` | `87e04c3ea4bf0fc8889b978a691f3d644110dbf7406001d47e015b39da39bf78` |
| `src/core/asset_transfer_global_allocation_v1.py` | `a4099cb3e53c26ef981e384e92cbdc5c04b80d5bdf7c14cd3b2d296a8830f028` |
| `src/core/asset_transfer_receipt_admission_v1.py` | `2a954812ee4d4cbcb537872ff108c52576c6c5aef7eaca28bab124d27488837f` |
| `src/integration/global_economic_epoch_journal_v1.py` | `7c52b02dae0fe2ab9650543a82b96d3761cef698f278e4107a36938173faa08a` |
| `src/core/lane_module_receipt_verification_v1.py` | `518ecd4a92593d7b7108e45787334e6c44201ef15510fc8e234e60aa30f92829` |
| `src/integration/isolated_profile_receipt_ports_v1.py` (self-review) | `aee2c8de566727da7d214fd6af08b291af0966428c7fca4b458aa5f1b9aa6843` |
| `tests/integration/test_isolated_asset_publication_v1.py` (two-case reviewer addition) | `cb0542c1521b920b6498c03570140e2c60795d68f358b420c05f82ebce4123fd` |
