# GlobalSettlementABI V1 Reference Slice

Status: `RESEARCH_ONLY_UNMOUNTED`

Production promotion: `false`

## Claim scope

This slice implements immutable Python and Rust reference contracts for the
modular whole-economy settlement boundary. It closes the lane identifier set,
binds module and route release IDs to canonical content, commits every lane in
the global state root, checks common conservation equations, defines the
recursive journal shapes, and models one atomic in-memory compare-and-swap
publisher. A shared corpus refinement-checks eighteen canonical release,
registry, profile, state, effect, occurrence, journal, epoch, migration, and
verified-epoch commit projections across Python and Rust.

The lane-core checkpoints add authenticated transfer and separately versioned
generic issue/self-burn transitions for `ASSET_TRANSFER`. Both remain outside
every active route, proof profile, writer adapter, and publication path. A
separate unmounted RISC0 workspace now proves one exact transfer-module
transition under the same Rust core and canonical module journal.

The lane-coordinator checkpoint adds a shared accounts, custody, and supply
projection plus an exact private-port binding for those two module families.
The stable ABI also commits a typed coordinator-release registry in each
profile and exposes release-aware receipt verification that alone constructs
opaque `VerifiedLaneCompositionV1`. A second unmounted RISC0 workspace proved
one exact transfer module-to-lane composition by verifying the module receipt
as an assumption and committing the canonical lane journal. The current
content-derived active test-profile source is statically coherent; the changed
host fixture has not been rebuilt in this checkpoint. Its real receipt
admission run is deferred to Runpod and no deployment profile admits it.

The implementation is:

- `src/core/global_settlement_types_v1.py`
- `src/core/global_economic_proof_v1.py`
- `src/core/global_oracle_occurrence_authority_v1.py`
- `src/core/oracle_current_dispute_status_v1.py`
- `src/core/route_composition_receipt_verification_v1.py`
- `src/core/global_settlement_abi_v1.py`
- `src/core/asset_transfer_types_v1.py`
- `src/core/asset_transfer_module_v1.py`
- `src/core/asset_transfer_policy_registry_v1.py`
- `src/core/lane_module_release_route_binding_v1.py`
- `src/core/lane_module_receipt_verification_v1.py`
- `src/core/managed_asset_lifecycle_types_v1.py`
- `src/core/managed_asset_lifecycle_module_v1.py`
- `src/core/asset_lane_projection_v1.py`
- `src/core/asset_lane_coordinator_v1.py`
- `src/integration/global_economic_commit_v1.py`
- `zk/global_settlement_abi_v1/`
- `zk/global_economic_epoch_risc0/`
- `zk/asset_transfer_module_risc0/`
- `zk/asset_lane_coordinator_risc0/`
- `tools/render_global_settlement_abi_v1_golden.py`

Focused evidence is:

- `tests/core/test_global_settlement_abi_v1.py`
- `tests/core/test_global_settlement_abi_v1_parity.py`
- `tests/core/test_global_oracle_occurrence_authority_v1.py`
- `tests/core/test_oracle_current_dispute_status_v1.py`
- `tests/core/test_asset_transfer_module_v1.py`
- `tests/core/test_asset_transfer_policy_membership_v1.py`
- `tests/core/test_lane_module_release_route_binding_v1.py`
- `tests/core/test_managed_asset_lifecycle_module_v1.py`
- `tests/core/test_asset_lane_coordinator_v1.py`
- `tests/core/test_asset_lane_coordinator_rejections_v1.py`
- `tests/data/global_settlement_abi_v1_golden.json`
- `zk/global_settlement_abi_v1/tests/golden_vectors.rs`
- `zk/global_settlement_abi_v1/tests/global_oracle_occurrence_authority.rs`
- `zk/global_settlement_abi_v1/tests/asset_transfer.rs`
- `zk/global_settlement_abi_v1/tests/managed_asset_lifecycle.rs`
- `zk/global_settlement_abi_v1/tests/asset_lane_coordinator.rs`
- `zk/global_settlement_abi_v1/tests/lane_module_release_route_binding.rs`
- `zk/global_economic_epoch_risc0/shared/tests/epoch_preflight.rs`
- `zk/global_economic_epoch_risc0/shared/tests/aggregation_preflight.rs`
- `zk/global_economic_epoch_risc0/host/tests/receipt_admission.rs`
- `zk/global_economic_epoch_risc0/host/tests/real_composition.rs`
- `zk/global_economic_epoch_risc0/host/tests/real_aggregation_nine.rs`
- `zk/asset_transfer_module_risc0/shared/tests/transition_preflight.rs`
- `zk/asset_transfer_module_risc0/host/tests/receipt_admission.rs`
- `zk/asset_transfer_module_risc0/host/tests/real_proof.rs`
- `zk/asset_lane_coordinator_risc0/shared/tests/coordinator_preflight.rs`
- `zk/asset_lane_coordinator_risc0/host/tests/receipt_admission.rs`
- `zk/asset_lane_coordinator_risc0/host/tests/real_composition.rs`

## Stable reference boundary

The closed lane registry contains exactly:

```text
ASSET_TRANSFER
SPOT_LIQUIDITY
FARM_INCENTIVES
ZDEX_TOKENOMICS
ZUSD_MONETARY
PERPS_MARKET
ORACLE_MARKET
SEALED_AUCTION
STRATEGY_ESCROW
PROOF_REWARDS
EXTERNAL_CUSTODY
GOVERNANCE_MIGRATION
```

An `ACTIVE` profile accepts a lane only when the lane is `ACTIVE_NEW` with the
complete evidence-status set, or when it carries
`DISABLED_PROVED_NO_WRITER`. An active route binds one governed command kind to
one ordered sequence of one through eight exact module release IDs. Route
selection is derived from the command registry; a mismatched caller claim
rejects.

`GlobalEconomicStateV1` commits chain, deployment, writer epoch, profile,
height, all lane roots, balances, supplies, custody, liabilities, reserves,
Oracle occurrences, replay state, terminal obligations, history, and external
outbox state. All collections use immutable canonical tuples with unique keys.

`GlobalOracleOccurrencePolicyV1` gives the existing route
`oracle_policy_root` a typed content-derived meaning: one Oracle object ID and
one maximum observation age in blocks. The Python and Rust authority checkers
require the command to bind the exact global pre-state root, content-derived route
release, command kind, next height, and consumed Oracle object ID. The selected
Oracle occurrence must exist in that pre-state, be finalized, be no newer than
the state height, and satisfy the route-selected freshness ceiling. Acceptance
constructs an opaque witness that commits all of those coordinates. Maximum
age, one-block-stale, future-height, unfinalized, omitted-consumption,
policy-substitution, and stale-head controls have cross-language evidence.
Active-profile and route-registry selection remain obligations of the existing
route and epoch verifiers.

The current perps dispute-status bridge converts only the representation of
the same SHA-256 digest between the legacy `sha256:` spelling and ABI V1's
`0x` spelling. It accepts an opaque global authority only for the reserved
`zenodex.oracle.current-dispute-status.v1` object ID. The status verifier still
recomputes the complete status body, report scope, dispute set, and Oracle
epoch before consumption.

`GlobalEconomicEffectPlanV1` checks:

```text
owned_and_custodied_post
  = owned_and_custodied_pre + authorized_issue - authorized_burn

supply_post
  = supply_pre + authorized_issue - authorized_burn

fee_charged
  = current_allocations + carried_residue
```

Issue, burn, and fee projections must equal their canonical effect rows.
Same-ledger destinations cannot enter the external outbox.

Consensus control fields use unsigned 64-bit integers. Non-negative holdings,
supply, custody, liability, reserve, fee, and conservation quantities use
unsigned 128-bit atoms. Signed effect deltas use signed 128-bit atoms. Python
rejects values outside those widths before hashing; Rust decodes directly into
the corresponding widths and uses checked arithmetic for composition.

## Rust parity boundary

The Rust crate is an isolated library with its own exact Cargo lock. It does
not modify or join the dirty historical RISC0 workspaces. Its public types use
closed enums, owned values, `deny_unknown_fields`, canonical lowercase roots,
bounded printable-ASCII tokens, checked arithmetic, and explicit `validate`
methods. Canonical JSON is formed through a sorted `serde_json::Value` before
hashing with the same domain framing as Python:

```text
SHA256("zenodex:" || domain || ":v1\\0" || canonical_json)
```

The committed corpus includes an atom amount of `2^64 + 1`, so agreement does
not rely on JavaScript-sized or unsigned-64-bit JSON numbers. Rust recomputes
each canonical-byte SHA-256 and each domain-separated root independently. The
epoch vector also compares the exact public-journal byte length and digest.
The fourteenth vector fixes the public route-assumption root over the profile,
route release, occurrence, writer epoch, exact route-journal root and digest,
and expected child image. The fifteenth fixes the canonical fanout-8 command
aggregation journal. The remaining vectors fix the epoch certificate,
cross-language commit identity over its ordered opaque route-witness bindings,
and migration certificate.

## ASSET_TRANSFER module checkpoint

The closed command shape is:

```text
asset_transfer(asset, sender, recipient, amount_atoms, max_fee_atoms)
```

The occurrence identity includes a domain-separated hash of the exact canonical
typed command payload. The explicit context binds chain, deployment, profile,
writer epoch, module release, occurrence, authenticated subject, and grant root.
The release-route binder recomputes the command-body hash from the command
inside the module statement and requires equality with the occurrence before
receipt admission. The transition
accepts only when the context release matches the state release, the command
kind and asset are registered, the asset is enabled, the sender is the
authenticated subject, the recipient differs from the sender, the amount is
positive, the flat fee carried by the pre-state policy row is within the
caller's fee ceiling, and all signed-effect and unsigned-balance arithmetic is
representable. The transition reads that policy row as state; release-route
binding separately requires the row, and both opaque registry roots, to be
exact members of the typed asset-transfer policy registry that the active
profile's economic policy registry governs for `asset_transfer`.

Acceptance returns a new immutable state, canonical account and fee effects,
asset and fee conservation rows, one `ASSET_TRANSFER` lane write, one consumed
occurrence, an empty external outbox, and a receipt root binding the complete
context, command, pre/post roots, effect-plan root, empty private-port root, and
empty terminal-obligation root. The result owns the shared
`LaneModuleTransitionJournalV1` projection. Every typed rejection returns the
exact pre-state root as its post-state root with an empty effect plan.

One fixed vector locks six canonical byte hashes and five domain-separated
roots in Python and Rust. Additional tests cover every reachable reject class,
strict Rust unknown-field decoding, signed-effect overflow, fee-owner aliasing,
and zero-fee split/merge state equivalence. This checkpoint excludes
transaction-fee policy envelopes, external custody, module release
registration, route composition, RISC0 guests, verifier admission, migration,
and durable publication.

## Managed asset lifecycle checkpoint

The separate module schema preserves the transfer-only V1 canonical roots and
defines two command variants:

```text
managed_asset_issue(asset, account_owner, amount_atoms)
managed_asset_burn(asset, account_owner, amount_atoms)
```

Its closed state-policy rows use the six source-bound M6 asset classes. Generic
supply authority is representable only for `registered_ordinary_token`.
Native coin, canonical zUSD, LP shares, ZDEX, and sealed-bid payment or
inventory assets reject both generic commands so their named economic modules
remain responsible for issue and burn.

Ordinary-token issue requires the authenticated subject and grant root to equal
the policy's named issuer and versioned issue-policy root. It may credit the
command's account owner. Generic burn is self-account only and requires the
authenticated subject to equal the account owner plus the versioned burn-policy
root. Disabled, unknown, foreign-release, wrong-subject, wrong-profile, zero,
insufficient, or unrepresentable commands return the exact pre-state root and
an empty effect plan.

Base-core acceptance changes account holdings and supply by the same atom count,
emits paired account and `ISSUE` or `BURN` rows, consumes one occurrence, and
creates no outbox work. The deterministic lane wrapper adds declared accounting
locations to the complete conservation projection and rebinds the effect,
private-port, journal, and receipt roots before coordinator admission. Python
and Rust independently lock issue and burn to twelve canonical-byte hashes and
ten domain-separated roots. The tests cover every protocol-managed asset class,
authority substitution, signed-effect width, supply overflow, strict decode,
and journal-binding mutation.

This checkpoint does not register an active release, prove authority-profile
membership, mount the legacy token stream, define protocol-specific issue or
burn semantics, or authorize a ledger commit. The single-module coordinator
below demonstrates a common state projection. It does not establish safe
cross-release coexistence.

## ASSET_TRANSFER lane-coordinator checkpoint

`AssetLaneStateProjectionV1` is the common state contract behind module-local
schemas. It commits the asset-policy and fee-policy registry roots, account
balances, named non-account custody buckets, and supply. Every holding names a
committed supply and every asset satisfies:

```text
sum(account balances) + sum(named custody) = supply
```

The transfer and managed-lifecycle adapters project their module states into
this exact shape. The private port binds producer schema, module release,
command occurrence, complete pre/post projections, module effect-plan root,
and terminal-obligation root. The coordinator accepts one module journal only
after checking chain, deployment, profile, writer epoch, lane, registered
release/schema, occurrence, nonzero exact port root, effects, terminal roots,
policy roots, one exact module-local lane write, one exact occurrence
consumption, conservation coverage, absolute conservation values, and exact
account/custody deltas. It rejects liability, reserve, reward, and slash rows
because this projection has no corresponding state fields. It also forbids
external outbox rows in this same-ledger coordinator slice.

Acceptance preserves module-owned economic rows and rewrites the single lane
write to the common projection roots. Rejection returns the exact common
pre-root as post-root and an empty effect plan. Python tests cover all 21
closed reject classes. Rust mirrors bound transfer and issue acceptance plus
binding and economic mutations. One cross-language transfer vector locks seven
canonical-byte hashes and six derived roots for projection, port, context,
module journal, normalized effects, and lane-composition journal.

Current transfer and managed-lifecycle V1 journals intentionally commit the
zero private-port root. The guest-ready lane-module wrappers instead derive an
exact nonzero private port and rebound journal from the accepted transition.
Legacy coordinator tests use a synthetic structurally bound journal to exercise
the deterministic contract; that fixture grants no authority. The new transfer
guest emits the wrapper's exact journal and a pinned adapter verifies one real
receipt. The separate asset-lane coordinator guest hard-codes that exact module
image, re-executes the module and coordinator, verifies the module receipt over
the canonical module journal with `env::verify`, and commits the exact lane
journal. Its host admits only a verified `Succinct` child before
`add_assumption`, requests a `Succinct` parent, verifies the parent image and
journal, and exposes a pinned stable-ABI verifier adapter. No active module or
coordinator release selects either image. This V1 coordinator handles one
module journal; multi-module sequencing and cross-release coexistence remain
open.

### Pattern selection record

- Domain and invariant: one closed whole-economy ABI owns release/profile
  identity, canonical state/effect roots, proof-journal bindings, conservation,
  and migration continuity.
- Representation: Python frozen value objects and Rust owned typed structs were
  selected. Raw mappings and `serde_json::Value` remain confined to fixture
  decode and canonical ordering.
- Mechanical guarantee: Rust rejects unknown fields and unrepresentable numeric
  widths at decode; both implementations validate semantic ordering, bindings,
  resource ceilings, and content-derived IDs before accepting a vector.
- Explicit non-guarantees: the corpus is bounded differential evidence. It does
  not prove requirements completeness, parser equivalence for every JSON byte
  string, universal RISC0 guest compatibility, or durable publication. Separate
  evidence establishes one exact asset-transfer module receipt only.
- Trusted construction boundary: Python builders derive release/profile IDs;
  Rust recomputes those IDs after owned decode. Neither value is an authority
  witness.
- Staleness, aliasing, concurrency, crash: the fixture is source-generated and
  checked byte-for-byte; Rust owns decoded data. Runtime profile races, proof
  staleness, database CAS, crash recovery, and outbox delivery remain separate
  shell obligations.
- Serialization and migration: canonical JSON and domain labels are versioned
  V1 ABI. Width, field, ordering, or framing changes require a new version or
  explicit compatibility evidence. Migration rows bind predecessor profile,
  exact writer-epoch rotation, object classification, and continuity roots.
- Evidence hooks: Python fixture drift check, Python invariant tests, Rust
  golden differential tests, malformed-input negatives, clippy, and local
  security red-flag scans.

## Proof and publication boundary

The reference defines module, lane-composition, route-composition, epoch, and
migration journals. Epoch construction enforces:

```text
1 <= commands <= 64
1 <= module leaf occurrences <= 64
module leaf occurrences >= commands
route module count <= 8
aggregation fanout = 8
aggregation levels <= 2
```

`verify_economic_epoch_v1` consumes one immutable
`EconomicEpochReceiptCandidateV1`, matching the Rust candidate aggregate. It
requires an `ACTIVE` profile, canonical occurrence order, and an exact
`VerifiedRouteCompositionV1` for every ordered route journal. Each opaque route
witness must bind the governed route release and image, occurrence, writer
epoch, lane order, route-journal root, canonical journal digest, and exact
public route-assumption root. Each route journal also has one disclosed effect
plan whose root and occurrence must match. A checked deterministic composer
derives the exact certificate-bound epoch plan from 1..64 sequential
single-lane `ASSET_TRANSFER` route plans. It rejects disconnected histories,
duplicate occurrences, overflow, terminal obligations, external outbox rows,
and unsupported routes before receipt verification. The boundary then checks
profile/image, chain/deployment, pre-root, exact ordered occurrence/body-hash
pairing, body commitment, journal-byte, and receipt-hash
bindings before it delegates root-receipt acceptance to
`SuccinctReceiptVerifierV1`. Only that function can
construct `VerifiedEconomicEpochV1` inside the Python module.

Repeated identical command payloads may share a body hash. Their occurrence
coordinates, authenticated subject, grant, nonce, and replay ID remain distinct.
This V1 contract is still pre-release and unmounted; adding the body-hash field
invalidates all earlier occurrence IDs, journals, receipts, vectors, and guest
images, which must be rebuilt together before any activation. Authenticated
ingress and canonical-byte availability remain outer requirements.

The Rust reference implements the parallel bounded admission function in
`economic_epoch_receipt_verification.rs` and the pure composer in
`epoch_effect_composition.rs`. Python and Rust share a golden aggregate root,
accept exact witness and effect-plan counts at 1, 8, 9, and 64, and reject
unrelated plans, wrong roots, disconnected histories, duplicate occurrences,
overflow, zero, 65, missing, foreign, substituted, or reordered evidence before
invoking the root verifier. These are typed
contract tests with injected verifier doubles.

The isolated `zk/global_economic_epoch_risc0` sibling pins RISC0 3.0.6 and adds
one no_std recursive guest for direct epochs, command aggregations, and grouped
epochs through 64 commands. Its preflight rederives canonical route roots and
digests, little-endian image roots, public assumption roots, context bindings,
state-root sequencing, canonical groups of eight, and exact module-leaf totals
before calling `env::verify` for each child. The host accepts only verified
Succinct children with exact journals, installs them with `add_assumption`, and
asks for a Succinct root. Ignored release-evidence tests generated a real
three-receipt direct/aggregation branch and a real 12-receipt 9-command tree.
The route children only commit caller-supplied bytes, so this is bounded
recursion-plumbing evidence without economic route correctness.

The isolated `zk/asset_transfer_module_risc0` sibling also pins RISC0 3.0.6.
Its guest consumes strict canonical `AssetTransferLaneModuleInputV1` bytes,
executes `transition_asset_transfer_lane_module_v1`, and commits the exact
accepted `LaneModuleTransitionJournalV1`. Typed economic rejection aborts and
produces no receipt. Its host accepts only a non-placeholder compiled image and
a Succinct receipt with the exact journal, then verifies that receipt under the
compiled image. `PinnedAssetTransferModuleReceiptVerifierV1` implements the
stable ABI verifier port and rejects foreign image, journal, encoding, receipt
kind, or cryptographic verification.

One ignored local replay generated and verified a real receipt under image root
`0x226651d0ba0e014c84331a521d78de508a5ede995990a7745d7ae61d93c22e24`.
The generated method SHA-256 is
`30278587c905f74373fb496acf518ffdfef7b415ad3c3ca6585b0a011b781c21`,
the 504848-byte guest ELF SHA-256 is
`b3b58f60f38cfa8916c240d659a4e7728a8227e3215384f8eaee0b80b6780374`,
and that local proof took 569.750161942 seconds. These values establish one
source-scoped computational-integrity replay and no throughput or resource
envelope.

The isolated `zk/asset_lane_coordinator_risc0` sibling pins the same toolchain.
Its guest consumes one strict canonical aggregate containing the complete
module input and coordinator context, re-executes both deterministic cores,
and calls `env::verify` with the source-pinned module image and exact module
journal before committing the exact lane journal. Its host verifies the child
as `Succinct`, installs it with `add_assumption`, proves a `Succinct` parent,
and verifies the exact parent image and journal. The pinned adapter implements
`LaneCompositionSuccinctReceiptVerifierV1`.

One ignored local replay generated the child and recursively verified it under
coordinator image root
`0xdba71555eb4790fd0146032e88f7c4720b343f08a1de785982b3c4faf14cfa61`.
The 659560-byte embedded method SHA-256 is
`0bef82521f2ab986cc1e4e3ec8f6f39e79a172189bdeb17095a4ddf80f6bd438`;
the 627136-byte guest ELF SHA-256 is
`407e3dae554b509580e67030dbb80148ca695fd0ce0f208012398e50cae649fe`.
The child proof took 522.722552067 seconds and the complete recursive run took
1443.666295007 seconds. This is source-scoped computational-integrity evidence
with no governed profile, `VerifiedLaneCompositionV1`, route, settlement, or
publication authority.

The stable ABI already defines `LaneCoordinatorReleaseV1`,
`LaneCoordinatorRegistryV1`, the profile's
`lane_coordinator_registry_root`, release-aware
`verify_asset_lane_composition_receipt_v1`, and opaque
`VerifiedLaneCompositionV1`. The current real-composition test builds a closed,
content-derived active test profile selecting the exact module and coordinator
images and invokes that verifier through the pinned RISC0 adapter. Fast tests,
Clippy, formatting, and structural checks pass. The real replay was interrupted
with exit code 130 for workstation thermal safety, so no successful
release-aware witness construction is claimed. Synthetic active evidence labels
and the placeholder route image in that fixture are not deployment governance.

`GlobalEconomicCommitPortV1` rechecks the current profile and state under one
lock. It atomically installs the complete post-state and publication record,
supports exact idempotent retry, and rejects stale competing heads without
mutation.

## Evidence commands

```bash
python3 -m ruff check \
  src/core/global_oracle_occurrence_authority_v1.py \
  src/core/oracle_current_dispute_status_v1.py \
  src/core/global_settlement_types_v1.py \
  src/core/global_economic_proof_v1.py \
  src/core/global_settlement_abi_v1.py \
  src/core/asset_transfer_types_v1.py \
  src/core/asset_transfer_module_v1.py \
  src/core/managed_asset_lifecycle_types_v1.py \
  src/core/managed_asset_lifecycle_module_v1.py \
  src/core/asset_lane_projection_v1.py \
  src/core/asset_lane_coordinator_v1.py \
  src/integration/global_economic_commit_v1.py \
  tools/render_global_settlement_abi_v1_golden.py \
  tests/core/test_global_settlement_abi_v1.py \
  tests/core/test_global_settlement_abi_v1_parity.py \
  tests/core/test_global_oracle_occurrence_authority_v1.py \
  tests/core/test_oracle_current_dispute_status_v1.py \
  tests/core/test_asset_transfer_module_v1.py \
  tests/core/test_managed_asset_lifecycle_module_v1.py \
  tests/core/test_asset_lane_coordinator_v1.py \
  tests/core/test_asset_lane_coordinator_rejections_v1.py

PYTHONPATH=. python3 tools/render_global_settlement_abi_v1_golden.py \
  --check tests/data/global_settlement_abi_v1_golden.json

python3 -m pytest -q \
  tests/core/test_global_settlement_abi_v1.py \
  tests/core/test_global_settlement_abi_v1_parity.py \
  tests/core/test_global_oracle_occurrence_authority_v1.py \
  tests/core/test_oracle_current_dispute_status_v1.py \
  tests/core/test_asset_transfer_module_v1.py \
  tests/core/test_managed_asset_lifecycle_module_v1.py \
  tests/core/test_asset_lane_coordinator_v1.py \
  tests/core/test_asset_lane_coordinator_rejections_v1.py

cargo test --offline --locked --manifest-path zk/global_settlement_abi_v1/Cargo.toml
cargo clippy --offline --locked --manifest-path zk/global_settlement_abi_v1/Cargo.toml \
  --all-targets -- -D warnings

cd zk/global_economic_epoch_risc0
cargo test --locked -p zenodex-global-economic-epoch-risc0-shared
RISC0_SKIP_BUILD=1 cargo test --locked --workspace
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- -D warnings
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

The focused suite covers missing lanes, content-ID drift, governed route
selection, incomplete release evidence, conservation and fee mutants,
same-ledger outbox rejection, reject-is-no-op, opaque verifier construction,
wrong image binding, exact route-witness substitution and ordering, 1/8/9/64
admission boundaries, zero and 65 command bounds, nine-module routes, skipped
migration predecessors, epoch jumps, binding no-ops, exact retry, and two-root
concurrency. Cross-language negatives additionally cover unknown top-level and
nested fields, Boolean aliases, numeric strings, malformed enums, exact integer
widths, mutated release content, conservation drift, zero/nine route shapes,
and zero/65 epoch shapes. The module-guest suite adds strict canonical input,
one-atom and exact-balance-neighbor BVA, overflow, reject-is-no-op, placeholder,
Fake-receipt, wrong-image, and wrong-journal evidence.
The coordinator-guest suite adds module/coordinator rejection before journal
emission, amount BVA through the composition boundary, strict canonical input,
exact module-owned lane-root regression, fake child rejection, exact child
assumption resolution, and parent wrong-image/wrong-journal rejection.

## Research writer-command coverage checkpoint

The initial source census now contains 23 writer entrypoints and 23 closed
command-coverage rows in:

```text
tools/m6_writer_inventory_manifest_v1.json
```

Each row binds one inventoried writer to a canonical command family, the
relevant `GlobalSettlementABI V1` lane IDs, M6 workflow IDs, and these eight
mandatory dimensions:

```text
module release
transition
canonical effect projection
proof profile
route
terminal path
adapter
evidence
```

The structural command passes only when every inventoried writer has such a
row, every adapter reference resolves to the exact inventoried source symbol,
the lane registry matches the global ABI, and unknown fields or values reject:

```text
python3 tools/check_m6_writer_inventory.py --json
```

The release command is expected to return nonzero at this checkpoint:

```text
python3 tools/check_m6_writer_inventory.py --require-release-ready --json
```

The v1 coverage schema accepts only `GAP`, `LEGACY_ONLY`, and
`RESEARCH_ONLY` bindings. It cannot encode `RELEASE_BACKED`, and every current
row remains `OPEN`. Promotion requires a separately reviewed schema that
verifies each claimed binding against the executable module, route, proof,
terminal, adapter, and evidence registries.

## Nonclaims and residual risk

- The eighteen-vector Python/Rust corpus is refinement-checked only on the
  committed examples and negatives. It is not a formal refinement theorem or
  exhaustive parser equivalence result.
- The recursive epoch sibling is compiled as one RISC0 guest and has real
  direct, command-aggregation, and 9-command nested Succinct replays. It has no
  cycle benchmark or release manifest.
- The real child in that test is quarantined structural code which commits
  caller-supplied bytes and proves no route economics, authorization,
  conservation, or release status.
- The recursive guest supports direct one-through-eight and canonical grouped
  nine-through-64 statements. The full 64-command, 73-receipt real replay is
  still absent, so no 64-command performance or release-backed claim exists.
- The real ASSET_TRANSFER module receipt is consumed by one separate
  source-scoped coordinator test. No governed route-composer or economic epoch
  receipt includes the resulting lane receipt yet.
- The stable release-aware lane constructor and coordinator registry exist.
  The changed content-derived active test-profile host fixture has not been
  rebuilt in this checkpoint. Its earlier real RISC0 replay was interrupted and
  has not produced a recorded
  `VerifiedLaneCompositionV1` binding root. No deployment-selected profile or
  authenticated verifier registry promotes the historical receipt.
- The transfer core is not registered as an active `LaneModuleReleaseV1`,
  selected by a `RouteReleaseV1`, or mounted behind a runtime adapter. The
  pinned module verifier establishes one exact receipt only.
- The general `SuccinctReceiptVerifierV1` contract tests use deterministic
  recording adapters. The separate RISC0 adapter establishes cryptographic
  validity only for the exact ASSET_TRANSFER image and journal tested here.
- The Oracle occurrence authority checker is deterministic ABI infrastructure.
  No perps lane guest, route-composer guest, epoch receipt, active profile, or
  atomic publication path currently consumes its opaque witness. Static
  environment-selected dispute roots remain a research adapter seam and carry
  no production authority.
- The in-memory commit port does not establish datastore durability,
  crash/reopen safety, consensus finality, or destination delivery.
- Existing Spot, zUSD, perps, M6, FCIS, and recursive branches remain donors or
  research inputs. They are not mounted through this ABI.
- A deployment-complete value-writer inventory, arbitrary-name writer
  discovery, the 81 scenarios plus 11 expansions, the complete asset lifecycle,
  remaining module economic transitions, migration totality, cross-version
  zUSD theorem, real mixed-lane proofs, and no-bypass runtime mount remain open.
- Current repository dirt and low disk space prevent a clean release candidate
  or broad proof build from being claimed by this work.

## Next safest step

Run the current release-aware lane replay on Runpod and record a successful
opaque `VerifiedLaneCompositionV1` binding only if the exact content-derived
profile, coordinator release, image, occurrence, and canonical journal all
verify. Then build the corresponding route-composer guest, keep deployment
releases in `SHADOW`, and compose that economic route through the existing
epoch guest before considering any mount. Run the full 64-command replay only
with an explicit resource budget. Complete named custody inputs,
transaction-fee policy, terminal asset lifecycle evidence, and multi-release
sequencing before enabling a route.
Extend the census across API, CLI, node, Tau, recovery, migration, workers,
administrative paths, generated artifacts, and deployed configuration before
claiming no-bypass closure. Preserve the separately pinned RISC0 3.0.6
guest/toolchain lane and rebuild images without changing or relabeling
historical donor evidence.
