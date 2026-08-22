# ZRPF ShapeForge Global Epoch Admission V1

Status: `RESEARCH_ONLY_UNMOUNTED`

This ShapeForge increment connects existing scoped ZenoDEX settlement evidence
to the new GlobalSettlementABI V1 publication boundary. It preserves the
evidence class of the RC3 donor surfaces and makes the additional authority
obligations explicit.

## Shape state

```text
Phi := <
  M = zenodex_shape_reference_v3,
  S = global_epoch_receipt_admission,
  A = evidence,
  T = contract strengthening,
  V = profile, certificate, route journals, route-assumption roots, opaque
      verified-route witnesses, disclosed route effect plans, composed epoch
      effects, receipt, verifier, body and state, ledger head,
  O = verify_economic_epoch, commit_verified_economic_epoch,
  G = active governed route, exact epoch binding, exact route-witness,
      assumption-root, and route-effect pairing, checked epoch aggregation,
      release-selected succinct receipt, opaque witness, atomic
      head/profile/body binding,
  Obs = verification outcome, commit outcome, published record,
  K = (height, tx_index, op_index),
  E = scoped proved settlement donor, contract references, tested direct RISC0
      recursion plumbing, one real ASSET_TRANSFER module receipt, and one
      source-scoped recursive lane receipt consuming that exact module proof,
  Gap = successful real release-aware lane replay, route proof consumption,
      remaining economic module guests, mounted verifier, durable publisher,
      full 64-command real replay, mounting, migration,
  N = synthetic structural journals cannot authorize publication,
  Delta = explicit RC3-to-ZRPF authority refinement
>
```

The single perturbation keeps the command, economic state, route, and effect
plan fixed while replacing cryptographic receipt verification with a
structurally valid or synthetic journal.

The next operator-axis increment is:

```text
Phi_asset := <
  M = zenodex_shape_reference_v3,
  S = asset_transfer_lane_module_output,
  A = operator,
  T = contract strengthening,
  V = typed module input, base result, private port, rebound journal,
  O = run asset transition, emit bound lane output,
  G = complete typed input, reject exact no-op, exact port binding,
      exact receipt binding,
  Obs = typed result, statement root, private-port root, journal root,
  K = (asset, owner, custody_domain),
  E = Python contract, Rust implementation, exact parity regressions,
  Gap = active release registration, lane and route proof consumption,
  N = host fixture rebinding is not constructor-authority equivalence,
  Delta = accepted asset transfers now own their coordinator-ready output
>
```

The managed lifecycle increment applies the same operator refinement to
ordinary-token issue and self-burn:

```text
Phi_lifecycle := <
  M = zenodex_shape_reference_v3,
  S = managed_asset_lifecycle_lane_module_output,
  A = operator,
  T = contract strengthening,
  V = typed lifecycle input, base result, private port, rebound journal,
  O = run managed lifecycle transition, emit bound lifecycle output,
  G = complete typed input, reject exact no-op, exact port binding,
      exact receipt binding,
  Obs = typed result, statement root, private-port root, journal root,
  K = (asset, owner, custody_domain),
  E = Python contract, Rust implementation, issue/burn parity regressions,
  Gap = RISC0 guest, release registration, cryptographic receipt,
  N = lifecycle host rebinding is not constructor-authority equivalence,
  Delta = accepted issue and burn now own coordinator-ready outputs
>
```

The release-route guard increment binds both module families to governed
occurrences:

```text
Phi_release_route := <
  M = zenodex_shape_reference_v3,
  S = lane_module_release_route_binding,
  A = guard,
  T = contract strengthening,
  V = active profile, governed route, command occurrence, complete module
      input, accepted output, structural binding witness,
  O = bind transfer output, bind managed lifecycle output,
  G = exact input/output statement, command semantics, subject, grant, chain,
      deployment, profile, writer epoch, lane, release, and occurrence,
  Obs = typed binding outcome, cross-language binding root,
  K = (route_release_id, route_lane_index),
  E = Python contract, Rust implementation, parity and substitution regressions,
  Gap = cryptographic receipt verification, coordinator guest, mounted route,
  N = occurrence id alone does not bind actual module command semantics,
  Delta = accepted outputs gain fail-closed active-profile release-route binding
>
```

The module-receipt evidence increment upgrades the structural witness into an
opaque verifier-owned witness while preserving the real-proof boundary:

```text
Phi_module_receipt := <
  M = zenodex_shape_reference_v3,
  S = lane_module_receipt_verification,
  A = evidence,
  T = contract strengthening,
  V = active profile, command occurrence, complete module input, accepted
      output, structural binding, release guest image, receipt bytes, verifier,
  O = verify transfer receipt, verify managed lifecycle receipt,
  G = exact structural rebinding, ACTIVE_NEW release, explicit nonempty
      SUCCINCT receipt, canonical journal byte ceiling, exact image and journal
      verifier acceptance, opaque constructor,
  Obs = verification outcome, verifier call, receipt digest, verified root,
  K = (route_release_id, route_lane_index),
  E = Python contract, Rust implementation, parity and negative regressions,
      plus one real ASSET_TRANSFER RISC0 3.0.6 Succinct receipt admitted by a
      pinned verifier adapter,
  Gap = real managed-lifecycle receipt, governed profile selection, route
        proof, mounted route,
  N = structural binding and deterministic receipt_root do not carry
      cryptographic proof authority,
  Delta = accepted module outputs can gain release-image and exact-journal
          verifier-port authority without gaining publication authority
>
```

The receipt-backed lane-composition increment carries exact module proof
authority across the deterministic coordinator edge while keeping coordinator
proof authority closed:

```text
Phi_receipt_backed_lane := <
  M = zenodex_shape_reference_v3,
  S = receipt_backed_asset_lane_composition,
  A = evidence,
  T = contract strengthening,
  V = active profile, command occurrence, coordinator context, module journal,
      private port, effects, opaque verified-module witness,
  O = compose receipt-backed single asset lane,
  G = exact active route, single ASSET_TRANSFER lane, exact occurrence and
      release, verified journal root and canonical digest, selected module
      image, deterministic coordinator acceptance, structural-only authority,
  Obs = composition outcome, binding root, authority level,
  K = (route_release_id, lane_id, module_journal_root),
  E = Python contract, Rust implementation, parity and substitution regressions,
      plus one source-scoped RISC0 coordinator guest and real recursive receipt,
  Gap = successful real receipt admission under the content-derived test
        profile, deployment-selected profile and verifier, route composer
        proof, mounted route,
  N = a valid module receipt cannot authorize a different module journal,
  Delta = the exact verified module can back a structural lane candidate without
          being relabeled as a cryptographically verified lane composition
>
```

The governed route-receipt increment constructs the exact child witness used by
epoch admission:

```text
Phi_route_receipt := <
  M = zenodex_shape_reference_v3,
  S = route_composition_receipt_verification,
  A = evidence,
  T = contract strengthening,
  V = active profile, occurrence, ordered lane journals, opaque verified-lane
      witnesses, route journal, route receipt, selected route image,
  O = verify route composition receipt,
  G = exact route release, lane cardinality and order, exact lane witnesses,
      nonempty SUCCINCT receipt, canonical route journal and image,
  Obs = route witness, binding root, journal digest, verifier call,
  K = (route_release_id, route_lane_index),
  E = Python contract, Rust implementation, parity and substitution regressions,
  Gap = real route guest, exact RISC0 assumptions, multi-lane effect pairing,
  N = a valid verified-lane witness cannot authorize another route journal,
  Delta = exact route proof evidence becomes an opaque epoch input
>
```

The current increment closes the host-side route-to-epoch admission edge:

```text
Phi_epoch_route_witness := <
  M = zenodex_shape_reference_v3,
  S = global_epoch_receipt_admission,
  A = evidence,
  T = contract strengthening,
  V = ordered occurrences, route journals, route-assumption roots, opaque
      verified-route witnesses, disclosed route effect plans, epoch certificate,
      composed effect plan, root receipt, selected root image,
  O = verify bounded economic epoch receipt,
  G = 1..64 canonical occurrences, one exact route witness, public
      image-and-journal assumption root, and root-bound effect plan per journal,
      checked connected aggregation equal to the certificate effect plan,
      sequential state roots, unique replay keys, nonempty SUCCINCT root receipt,
  Obs = epoch witness, ordered route binding roots, commit id, verifier call,
  K = (height, tx_index, op_index),
  E = Python contract, Rust implementation, golden parity and BVA regressions,
  Gap = economic route guests, full 64-command real replay, durable publisher,
  N = structural, foreign, substituted, or reordered route evidence cannot
      authorize an epoch,
  Delta = the weaker structural-journal epoch constructor is removed
>
```

The bounded recursive increment closes the first cryptographic plumbing seam:

```text
Phi_epoch_direct_risc0 := <
  M = zenodex_shape_reference_v3,
  S = global_epoch_receipt_admission,
  A = evidence,
  T = contract strengthening,
  V = canonical epoch bytes, 1..8 exact child image-and-journal claims,
      public assumption roots, pinned epoch ELF,
  O = add_assumption on the host, env::verify in the guest, emit Succinct root,
  G = canonical postcard input, canonical JSON journals, exact image endian,
      exact state-root sequence, exact assumption roots, Succinct-only receipts,
  Obs = child receipt kind and journal, root receipt kind and journal, image ID,
  K = route occurrence order,
  E = no_std BVA and substitution tests, one real three-receipt branch proof,
      and one real 12-receipt 9-command RISC0 3.0.6 proof,
  Gap = route guest consuming the economic lane receipt, full 64-command real
      replay, release mount and publisher,
  N = the structural test leaf commits supplied bytes and proves no economics,
  Delta = direct and canonical fanout-8 recursive assumption resolution is
      executable for 1..64 claims, with real proof evidence through 9
>
```

The first economic-leaf increment proves the exact stable Rust transition in a
separately versioned module image:

```text
Phi_asset_transfer_risc0 := <
  M = zenodex_shape_reference_v3,
  S = lane_module_receipt_verification,
  A = evidence,
  T = contract strengthening,
  V = canonical AssetTransferLaneModuleInputV1, deterministic accepted result,
      canonical LaneModuleTransitionJournalV1, pinned image, Succinct receipt,
  O = execute transition, commit exact journal, verify image and journal,
  G = strict canonical JSON, one-megabyte input and journal ceilings, typed
      economic acceptance, non-placeholder image, Succinct-only receipt,
  Obs = typed preflight result, exact journal, receipt kind, image root,
      verifier outcome,
  K = command_occurrence_id,
  E = no-build Rust BVA and rejection suite plus one real local RISC0 3.0.6
      Succinct proof under the exact current guest,
  Gap = deployment profile registration, successful release-aware lane replay,
      route proof, recursive economic epoch, durable publication,
  N = one module receipt carries no lane, route, epoch, migration, settlement,
      or publication authority,
  Delta = one actual ASSET_TRANSFER transition has computational-integrity
      evidence under the stable module journal ABI
>
```

The first recursive economic-lane increment consumes that exact leaf under a
separately pinned coordinator image:

```text
Phi_asset_lane_coordinator_risc0 := <
  M = zenodex_shape_reference_v3,
  S = receipt_backed_asset_lane_composition,
  A = evidence,
  T = contract strengthening,
  V = canonical coordinator input, re-executed module output, exact module
      journal, pinned module image, module receipt, exact lane journal,
      coordinator image and receipt,
  O = verify module receipt assumption, compose deterministic lane, commit and
      verify exact lane journal,
  G = strict canonical bounded input, hard-coded nonzero module image,
      Succinct-only child and parent receipts, exact image and journal bytes,
      typed module and coordinator rejection before lane-journal emission,
  Obs = preflight result, module and lane journal roots, receipt kinds, image
      roots, pinned verifier outcomes,
  K = command_occurrence_id,
  E = no-build BVA and rejection tests plus one historical local RISC0 3.0.6
      module-to-lane Succinct recursion replay under the unchanged guest images;
      the current release-aware fixture compiles and passes fast gates,
  Gap = successful real release-aware replay and recorded
      VerifiedLaneCompositionV1 binding root, deployment-selected profile and
      verifier, route proof, epoch consumption, durable publication,
  N = a source-scoped coordinator receipt carries no governed route, epoch,
      settlement, migration, or publication authority,
  Delta = the first actual economic module receipt is recursively bound to its
      exact deterministic lane-composition journal
>
```

## Functional-core preflight

The new `AssetTransferLaneModuleInputV1` is one immutable owned aggregate for
context, pre-state, command, policy roots, and named custody. The accepted
result owns its post-state, global effect plan, private port, and rebound
journal. No mutable aliases or external handles cross the boundary.

The wrapper delegates economic semantics to the existing
`transition_asset_transfer_v1` core. Acceptance adds only canonical statement,
projection, private-port, receipt, and journal commitments. Rejection returns
the existing typed rejection unchanged, with identical pre/post state, empty
effects, and no private port. No API, ledger, route, database, or proof-system
shell changed in this increment.

`ManagedAssetLifecycleLaneModuleInputV1` provides the parallel immutable
aggregate for ordinary-token issue and burn. Its wrapper delegates all asset
class, authority, grant, amount, balance, and supply rules to
`transition_managed_asset_lifecycle_v1`. Accepted results own their common lane
port and rebound journal. Every lifecycle rejection returns the existing typed
no-op unchanged. Named protocol assets remain excluded from generic supply
authority.

`ReceiptBackedAssetLaneCompositionCandidateV1` is one immutable aggregate for
the profile, occurrence, coordinator input, and opaque verified-module witness.
The boundary rechecks the exact module journal root and canonical digest before
calling the existing deterministic coordinator. Its constructor-private output
uses the closed authority level `RECEIPT_BACKED_STRUCTURAL_ONLY`; no route or
publisher accepts that type.

The separate `zk/asset_lane_coordinator_risc0` workspace owns one complete
guest input containing the module input and coordinator context. Its preflight
re-executes the exact module wrapper and deterministic coordinator. The guest
then calls `env::verify` with a source-pinned ASSET_TRANSFER image ID and the
exact canonical module journal before committing the exact canonical lane
journal. The host admits only a cryptographically verified `Succinct` child,
adds it as an assumption, proves a `Succinct` coordinator receipt, and verifies
the exact coordinator image and journal. Its pinned adapter implements the
stable lane-composition receipt-verifier port. The current test fixture invokes
that port under a content-derived active test profile whose evidence labels and
placeholder route image confer no deployment authority.

Python and Rust use the same canonical schemas and domain-separated roots.
Focused parity tests pin the statement, pre-projection, post-projection,
private-port, receipt, and module-journal roots. A coordinator regression shows
that the accepted result composes directly without host fixture rebinding.
The lifecycle regressions pin the same six roots independently for issue and
burn, giving twelve additional Python/Rust root comparisons.

`ReleaseRouteBoundLaneTransitionV1` is constructible only by the new binder.
The binder consumes the complete typed input and accepted output, derives the
active route from the occurrence command kind, and checks the selected lane
release plus subject, grant, chain, deployment, profile, writer epoch, and
occurrence bindings. A managed burn output labeled with a managed-issue
occurrence now rejects before the structural witness is constructed. Python
and Rust pin the same binding root. This witness remains structural and does
not verify the receipt root cryptographically.

`VerifiedLaneModuleTransitionV1` has a separate verifier-controlled
constructor. Its boundary recomputes the structural binding from the complete
typed input and accepted output, selects `guest_image_id` from the active lane
release, requires explicit nonempty `SUCCINCT` receipt bytes, enforces the
release journal-byte ceiling, and passes the exact canonical module journal to
the injected verifier port. Python and Rust pin the same verified binding root,
canonical-journal SHA-256 digest, and cryptographic receipt digest. The
deterministic `module_journal.receipt_root` remains a statement commitment and
is never used as the receipt artifact digest.

`VerifiedRouteCompositionV1` is now required at the next boundary. Python and
Rust pair each opaque route witness with the exact active profile, route
release and image, command occurrence, writer epoch, ordered lane journals,
route-journal root, and canonical journal digest. The bounded host reference
accepts 1, 8, 9, and 64 exact route witnesses and rejects missing, foreign,
substituted, or reordered witnesses before invoking the root verifier. The
shared commit-id vector binds the certificate root, ordered route-witness
binding roots, and root receipt digest. The epoch certificate also commits one
`ordered_route_assumption_roots` entry per route, binding the exact child image,
canonical journal digest, route release, occurrence, profile, and writer epoch.
Each route journal now also requires one disclosed effect plan with the exact
committed root and occurrence. A pure checked Python/Rust composer folds
sequential single-lane `ASSET_TRANSFER` plans into the only admissible epoch
plan. It rejects disconnected lane or conservation histories, repeated
occurrences, signed or unsigned overflow, terminal obligations, external
outbox rows, zero plans, and 65 plans. A shared golden vector fixes the exact
aggregate root across both languages.

`EconomicEpochReceiptCandidateV1` now owns the parallel profile, certificate,
occurrence, route-journal, opaque route-witness, route-effect plans, composed
epoch effect plan, receipt, and expected binding inputs in both Python and
Rust. The Python verifier consumes this one
immutable aggregate instead of a caller-managed parallel argument list. The
candidate remains untrusted data; only complete verification constructs the
opaque epoch witness.

## Promoted claim

The Python reference constructs `VerifiedEconomicEpochV1` only through
`verify_economic_epoch_v1`. That function consumes one immutable typed
candidate and checks the active profile, governed route chain, canonical
occurrence order, one exact opaque route witness, public assumption root, and
root-bound route effect plan per journal, exact checked epoch aggregation, root
image and journal, body commitments, receipt digest, and the selected verifier
call. The Rust ABI implements the parallel bounded boundary. The reference
publisher accepts only the resulting opaque
epoch witness and rechecks current head, profile, body, post-state, data
availability, finality, height, and command cardinality under one lock.
The pre-release ABI now includes the canonical command-body hash in each
occurrence identity. Implemented asset transfer and managed issue/burn binders
derive that hash from the exact command in the module statement, while epoch
verification and commit require the exact ordered body-hash sequence. This is
structural reference evidence; authenticated ingress and canonical-byte
availability remain outer premises.

This reaches evidence class `contract`. The existing settlement
strong-validation slice retains its scoped `proved` status. The sibling RISC0
3.0.6 crate adds tested cryptographic recursion plumbing for one through eight
direct children. Its real child is a quarantined structural journal emitter,
so it contributes no route-economic, release, mounting, or publication claim.

The independent `zk/asset_transfer_module_risc0` workspace adds one tested
economic leaf. Its guest imports the exact stable Rust transition, commits the
canonical accepted module journal, and aborts without a receipt on typed
economic rejection. The host generated and verified one Succinct receipt under
image root
`0x226651d0ba0e014c84331a521d78de508a5ede995990a7745d7ae61d93c22e24`.
The pinned adapter rejected a wrong image and wrong journal, while a Fake
receipt rejects on kind. This receipt is unregistered and unmounted.

The independent `zk/asset_lane_coordinator_risc0` workspace recursively
consumed a newly generated instance of that exact module receipt. The
coordinator image root is
`0xdba71555eb4790fd0146032e88f7c4720b343f08a1de785982b3c4faf14cfa61`.
Its 659,560-byte embedded method SHA-256 is
`0bef82521f2ab986cc1e4e3ec8f6f39e79a172189bdeb17095a4ddf80f6bd438`,
and its 627,136-byte guest ELF SHA-256 is
`407e3dae554b509580e67030dbb80148ca695fd0ce0f208012398e50cae649fe`.
The child module proof took 522.722552067 seconds and the complete recursive
run took 1,443.666295007 seconds. The pinned lane adapter accepted the exact
image and journal and rejected substitutions. That successful replay is
historical source-scoped evidence for the unchanged guest images. The current
host fixture additionally binds a content-derived active test profile, module
and coordinator releases, route, occurrence, and stable opaque lane verifier.
It passed fast compile, test, Clippy, formatting, and structural checks. Its
real replay was interrupted with exit code 130 for local thermal safety, so no
successful release-aware `VerifiedLaneCompositionV1` binding root is recorded.

## CBC boundary and negative knowledge

The following worlds are inadmissible for publication:

- a zero private-port module journal;
- a synthetic structural journal without a verified receipt;
- a missing, duplicated, foreign, substituted, or reordered opaque route
  witness;
- a missing or substituted public route-assumption root;
- an unrelated epoch effect plan, wrong route-effect root, disconnected
  history, repeated occurrence, or arithmetic overflow;
- an empty, fake, conditional, development, wrong-image, or wrong-journal
  receipt;
- a caller-constructed substitute for `VerifiedEconomicEpochV1`;
- a caller-selected route or a managed issue occurrence paired with a burn
  module input;
- a structural release-route witness or deterministic module receipt root used
  in place of release-image and exact-journal cryptographic verification;
- a valid verified-module witness paired with another accepted transition's
  module journal, private port, or effects;
- a receipt-backed structural lane candidate relabeled as coordinator-proof or
  route-composition authority;
- a historical source-scoped coordinator receipt relabeled as a current
  release-aware `VerifiedLaneCompositionV1` witness;
- synthetic active evidence labels or a placeholder route image relabeled as
  deployment governance;
- a substituted valid module statement paired with another statement's
  structural witness;
- a stale head, inactive profile, mismatched body, or mismatched post-state.

Legacy asset-lane coordinator tests intentionally use synthetic bound journals
to exercise deterministic coordinator behavior. The guest-ready wrapper
constructs its own bound port and structural journal, and the separate RISC0
coordinator now consumes one exact module receipt into that module-owned lane
journal. All of these surfaces remain unmounted and have no settlement
authority.

## Replay

```bash
python3 tools/shapeforge_validate.py \
  docs/zenodex/shapeforge_promoted/zenodex_world_model.seed.json
python3 tools/shapeforge_validate.py \
  docs/zenodex/shapeforge_promoted/zenodex_negative_knowledge.seed.json
python3 tools/check_zrpf_shapeforge_global_epoch_admission_v1.py
python3 -m pytest -q \
  tests/test_check_zrpf_shapeforge_global_epoch_admission_v1.py
PYTHONPATH=. python3 tools/render_global_settlement_abi_v1_golden.py \
  --check tests/data/global_settlement_abi_v1_golden.json
PYTHONPATH=. python3 -m pytest -q \
  tests/core/test_global_settlement_abi_v1.py \
  tests/core/test_global_settlement_abi_v1_parity.py \
  tests/core/test_asset_transfer_lane_module_v1.py \
  tests/core/test_managed_asset_lifecycle_lane_module_v1.py \
  tests/core/test_lane_module_release_route_binding_v1.py \
  tests/core/test_asset_lane_coordinator_v1.py
cargo test --offline --locked \
  --manifest-path zk/global_settlement_abi_v1/Cargo.toml

cd zk/global_economic_epoch_risc0
cargo test --locked -p zenodex-global-economic-epoch-risc0-shared
RISC0_SKIP_BUILD=1 cargo test --locked --workspace
cargo clippy --locked --workspace --all-targets -- -D warnings
cargo test --locked -p zenodex-global-economic-epoch-risc0-host \
  --test real_composition \
  real_succinct_child_assumption_resolves_into_exact_epoch_journal \
  -- --ignored --nocapture
cargo test --locked -p zenodex-global-economic-epoch-risc0-host \
  --test real_aggregation_nine \
  nine_routes_compose_through_two_groups_into_one_exact_epoch_root \
  -- --ignored --nocapture

cd ../asset_transfer_module_risc0
RISC0_SKIP_BUILD=1 cargo test --locked --workspace
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- \
  -D warnings
cargo fmt --all -- --check
cargo test --locked -p zenodex-asset-transfer-module-risc0-host \
  --test real_proof \
  real_asset_transfer_transition_proves_the_exact_module_journal \
  -- --ignored --nocapture

cd ../asset_lane_coordinator_risc0
RISC0_SKIP_BUILD=1 cargo test --locked --workspace
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- \
  -D warnings
cargo fmt --all -- --check
cargo test --locked -p zenodex-asset-lane-coordinator-risc0-host \
  --test real_composition \
  real_module_receipt_composes_into_the_exact_lane_journal \
  -- --ignored --nocapture
```

## Remaining gaps

- Successful Runpod replay of the current content-derived test profile through
  the stable release-aware lane verifier, followed by a real economic route
  guest that consumes the resulting `VerifiedLaneCompositionV1`. Managed
  lifecycle and every other module family still lack a real module guest.
- A full real 64-command recursion replay and resource benchmark; typed BVA
  and fail-closed partition evidence already cover the boundary.
- An authenticated governed verifier implementation and registry selection.
- Deployment-selected coordinator releases and verifier implementations with
  authenticated evidence rather than synthetic test-profile status labels.
- Durable atomic publication with crash and reopen evidence.
- Complete M6 routes and closure of every reachable value writer.
- Proved state migration, profile activation, writer rotation, and retirement.

## Shape delta

Existing RC3 economic evidence is now represented as reusable donor evidence.
The additional publication-authority refinement has explicit variables,
operators, guards, observables, a total occurrence key, evidence classes,
negative knowledge, source pins, and fail-closed replay. Structural journal
acceptance can no longer be mistaken for global receipt authority inside the
promoted ShapeForge model.

The epoch route-witness increment removes the structural-journal-only
constructor path. Epoch admission now requires exact opaque route witnesses in
canonical command order, records their ordered binding and public assumption
roots, and has matching Python/Rust 1/8/9/64 boundary and substitution
regressions.

The route-effect increment closes a separate relabeling path. Every disclosed
route plan must match its route-journal root and occurrence, and the checked
aggregate must equal the certificate-bound epoch plan before the root verifier
is called. This remains host-side contract evidence for one ASSET_TRANSFER lane.
The recursive guest does not yet prove the aggregation.

The RISC0 increment makes bounded direct and grouped recursion executable. A
pinned 3.0.6 host admits only exact Succinct child receipts, calls
`add_assumption`, and proves a Succinct root whose guest rederives every public
assumption root and calls `env::verify` over exact journal bytes. Direct BVA
accepts one and eight. Grouped BVA accepts nine and 64 through canonical groups
of eight and rejects zero, 65, reordered groups, split drift, wrong images, and
module-leaf drift. A real 9-command run generated nine structural route
receipts, `8+1` same-image command aggregations, and one exact epoch root in
985.82 seconds. The economic lane receipt is not one of those route children.
The full 64-command replay, economic route recursion, release registry,
publisher, migration, and production authority remain open.

The asset-transfer operator increment replaces host-owned fixture rebinding
with a module-owned accepted result in the deterministic Python and Rust cores.
It closes one structural guest-readiness gap while preserving the explicit
cryptographic guest, release, verifier, route, and publication gaps.

The managed lifecycle increment closes the corresponding structural gap for
registered ordinary-token issue and self-burn. It preserves the named-module
boundary for native coin, zUSD, LP shares, ZDEX, and sealed-bid assets and does
not promote either lifecycle operation beyond contract and tested evidence.

The release-route increment closes host-side command relabeling and
caller-selected-route gaps for the implemented asset-lane wrappers. It adds an
opaque structural witness over the exact active profile, route, lane release,
occurrence, input statement, journal, producer schema, route position, and port
schema.

The module-receipt increment closes the contract-level gap between that
structural witness and a verifier-owned module witness. It makes the selected
guest image, exact canonical journal bytes, explicit receipt kind, separate
receipt digest, and verifier call observable in both language references. The
injected recording verifier remains the general contract evidence. A separate
pinned adapter and real RISC0 3.0.6 proof now establish computational integrity
for one ASSET_TRANSFER transition under image root
`0x226651d0ba0e014c84331a521d78de508a5ede995990a7745d7ae61d93c22e24`.
The generated method SHA-256 is
`30278587c905f74373fb496acf518ffdfef7b415ad3c3ca6585b0a011b781c21`,
the guest ELF SHA-256 is
`b3b58f60f38cfa8916c240d659a4e7728a8227e3215384f8eaee0b80b6780374`,
and the local proof took 569.750161942 seconds. A historical source-scoped lane
recursion consumes this image. The current release-aware fixture compiles under
an exact content-derived test profile; successful real replay, deployment
profile selection, route recursion, mounting, publication, and a proved
resource envelope remain open.

The receipt-backed lane increment closes the next structural composition edge.
It binds one exact verified-module witness to the journal, private port, effects,
active single-lane route, deterministic coordinator output, and a shared
Python/Rust root. A separate source-scoped RISC0 coordinator now re-executes
that transition, verifies the exact module receipt as an assumption, commits
the module-owned lane journal, and verifies one real Succinct coordinator
receipt under image root
`0xdba71555eb4790fd0146032e88f7c4720b343f08a1de785982b3c4faf14cfa61`.
The generated method and ELF hashes are recorded above. The stable profile,
coordinator registry, and opaque lane-verifier constructor are implemented.
Successful real replay under the current test profile, authenticated deployment
selection, route-proof consumption, and all publication authority remain
explicit barriers.
