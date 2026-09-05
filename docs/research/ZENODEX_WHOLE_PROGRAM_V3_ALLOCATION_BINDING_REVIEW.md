# V3 allocation binding review

Date: 2026-09-04. Base: `c6a9fd028ded9224427a645c1217d0ce576f78af`.
Status: `RESTRICTED_BINDING_IMPLEMENTED_TESTED_W04_PARTIAL`. Authority: `NONE`.
This review concerns the isolated V3 candidate. The initial read-only review
below established the defect before the parent approved the narrow repair.
The implementation and verification record follows the original packet.

## Finding and evidence

The transfer module and the asset coordinator deliberately commit different
state shapes. The allocation producer currently requires the module state root;
the committed global state carries the coordinator projection root. A genuine
module witness from the existing verifier boundary therefore cannot presently
produce an allocation fragment for the corresponding committed lane state.
The local witnesses below use an explicit recording **mock cryptographic
verifier**. They establish the binding defect, not receipt cryptographic validity.

The existing certificate already rejects a fragment whose `lane_state_root`
differs from `GlobalEconomicStateV1.lane_roots`: see
`global_accounting_allocation_certificate_v1._check_lane_bindings`. Removing or
loosening that equality would erase a necessary safety check.

For the retained transfer fixture:

```text
module journal post_lane_root = accepted.post_state.state_root
  = 0xf6b85b20f1751b63b8d60b0a3ba3cf212e3e691239f31e98cbf1b652268de1a1
accepted.private_port.post_state.state_root = committed global lane state_root
  = 0x66669af90c305309acae21de0d9c9a4fc852e3f9150af8a32e3c9e5f7d27824c
```

The parent retained the two-root discovery in
`tests/integration/test_global_allocation_shadow_v1.py` under
`test_module_and_coordinator_roots_expose_unresolved_allocation_bridge`.
Independent local replay also opened an actual committed isolated SQLite epoch,
obtained the current and immediate predecessor through the new read-only
consumer, and observed:

```text
private_port_pre_equals_committed_predecessor: True
private_port_post_equals_committed_current: True
committed_snapshot_admission_result: JOURNAL_ROOT_DRIFT post root
database_bytes_and_logical_state_unchanged: True
```

The old module-scoped fixture remains a passing positive control. Replacing
only its input lane-root coordinates with those read from the committed
snapshot causes the rejection. No committed root was edited in this replay.

## Existing semantic contract

The normative reference is
`docs/research/GLOBAL_SETTLEMENT_ABI_V1_REFERENCE_20260805.md`, section
`ASSET_TRANSFER lane-coordinator checkpoint`. It defines the common projection
as policy roots plus complete account balances, named controlled locations and
supply. It explicitly defines coordinator acceptance as preserving economic
rows while rewriting the lane write to those projection roots. Its V1
coordinator supports one module journal; sequencing and cross-release shared
asset coexistence remain open.

The executable relation is:

1. `asset_transfer_lane_module_v1._private_port` derives complete pre/post
   `AssetLaneStateProjectionV1` values from the transfer state, pinned policy
   roots and custody rows. The accepted value validates the projection,
   module effects, module post-state and private-port binding.
2. `_bound_journal` keeps the module-local pre/post roots and includes
   `private_port.port_root`. `AssetLanePrivatePortV1.to_canonical` commits both
   full projections, producer schema, module release, occurrence, effects and
   terminal root.
3. `lane_module_receipt_verification_v1` re-executes the exact module input and
   verifies its canonical journal under the selected release image. Opaque
   `VerifiedLaneModuleTransitionV1.module_journal_root` binds an accepted
   private port when admission rebuilds the accepted value and checks journal
   equality. Caller-supplied projections alone establish no such binding.
4. `asset_lane_coordinator_v1` checks the module-local write, context, policy
   roots, complete private port and economic deltas. Its normalized effect
   plan and `LaneCompositionJournalV1` use the private-port projection roots.
5. `receipt_backed_asset_lane_composition_v1` pairs the exact module witness
   with this composition and grants only structural evidence. Separate
   `lane_composition_receipt_verification_v1` selects a coordinator image and
   mints `VerifiedLaneCompositionV1` after receipt verification. A module proof
   alone grants no coordinator, route, epoch or publication authority.
6. `global_accounting_lane_producers_v1.produce_asset_transfer_fragment_v1`
   currently compares the **module journal** post root to the committed lane
   root, and its pre root to the caller's prior fragment root. Rust makes the
   same comparisons. Receipt admission reruns this producer, then mints the
   fragment witness. This is the integration mismatch.

## Proposed repair packet

Preserve the existing V1 module-scoped producer and admission behavior for
historical callers and retained vectors. Add an explicitly named global-state
admission entry point. It must not implement an `either root is acceptable`
fallback or change the meaning of old encoded states.

The proposed pure input aggregate contains the opaque module witness, exact
accepted module output, and complete predecessor/current global state values.
It contains no arbitrary claimant partition, prior fragment, database handle,
publisher, or writer capability. The shell remains responsible for acquiring
and authenticating those immutable snapshots and proving that they are the
adjacent committed states for the selected publication. Pure core types do not
establish store provenance.

For an initial **single ASSET_TRANSFER occurrence** scope, the new boundary
must establish all of the following before constructing a global fragment:

- Rebuild exact owned inputs, validate finite bounds, and bind the supplied
  accepted output to the opaque module witness at the canonical journal root.
- Bind chain, deployment, profile, writer epoch, lane and module release
  across both snapshots and the receipt-bound journal. Require the exact
  height/occurrence publication relation supplied by the shell contract.
- Require ASSET_TRANSFER to be the sole enabled lane for allocation ownership
  in this restricted profile. Reject unsupported reserve, external and
  terminal families, with no truncation or guessed ownership.
- Match the predecessor lane root to the verified private-port **pre**
  projection root and current lane root to its **post** projection root.
  Match the complete snapshot balances, custody and supplies to the respective
  projections. Root equality alone cannot establish these duplicate-table
  consistency requirements.
- Require the complete predecessor/current entitlement tables to be equal for
  this account-transfer operation. Derive claimant rows from that retained
  state partition; compare exact identities and atom amounts, not only totals.
  Validate per-domain backing independently. Custody remains unchanged under
  this module. New claimant allocation and changes to claimant ownership
  require a separately specified enabling operation.
- Derive the fragment's controlled rows from verified post custody and its
  lane root from the verified post projection. Preserve its module receipt
  binding fields. Only a checked derivation may mint the existing opaque
  fragment type; do not expose a generic relabeling or mint API.
- Pass the result through the existing projection and certificate checker,
  preserving lane-state equality, witness/header checks, total row coverage,
  canonical ordering and typed rejection.

The same checks must exist in Python and Rust. The implementation may reuse
the existing module admission internally with values derived from the already
validated module/private-port relation. Such temporary module-scoped values
must never be returned as committed snapshot data or used as evidence of a
prior receipt. A dedicated root-scope implementation is also acceptable; the
review should prefer the smaller auditable boundary after checking retained
source-based tests.

Proposed owned paths after integration approval:

| Path | Change |
| --- | --- |
| `src/core/asset_transfer_receipt_admission_v1.py` | Add separately named checked global-state entry point and typed result family; preserve old function behavior |
| `src/core/asset_transfer_global_allocation_v1.py` | Optional new pure snapshot relation/derivation helpers if needed to keep admission small |
| `zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs` | Equivalent checked entry point inside the existing private witness owner |
| `zk/global_settlement_abi_v1/src/asset_transfer_global_allocation.rs` | Optional Rust snapshot relation helper and minimal module export |
| `tests/core/test_asset_transfer_global_allocation_v1.py` | New semantic and malformed-boundary controls |
| `zk/global_settlement_abi_v1/tests/allocation_projection/receipt_tests.rs` | Bounded Rust receipt-backed snapshot cases |
| `tests/integration/test_global_allocation_shadow_v1.py` | Add actual committed-snapshot positive path; retain root-difference discovery |
| Dedicated generated allocation-binding fixture/renderer if required | Shared independently specified outcomes; regenerate only by recorded command |

No producer registry expansion, changed journal bytes, stored root rewrite,
certificate guard weakening, publisher hook or real authority activation is
part of this repair. If implementation needs an existing producer refactor,
present that exact additional edit for review before changing old semantics.

## Predecessor sufficiency and ownership limits

The current predecessor fragment argument is an exact typed value, but its
own receipt and claimant allocation are not authenticated by the old admission.
Only its lane/release/enabled/kind/root coordinates are checked. Requiring an
arbitrary prior fragment perpetuates this gap; it is unnecessary for the
restricted transfer relation once complete authenticated predecessor state and
the verified private-port preimage are available.

The existing journal stores complete global state including liabilities.
`ZENODEX_ACCOUNTING_SOURCE_CLASSIFICATION_CONTRACT_V1.md` defines liabilities
as claimant entitlements and distinguishes the custodian from the claimant.
For one enabled ownership lane, unchanged custody and unchanged liabilities,
the predecessor's controlled and entitlement rows are deterministically
derivable. Pre/post projection roots are also already committed through the
private port. These facts justify no new allocation or predecessor-root fields
on the journal for this narrow case.

However, certified initialization and the version-pinned policy must still
establish that the original liability partition is authorized. Conservation
and preserved claimant rows cannot certify a wrongful initial assignment.
The current admission explicitly records that policy gap. Multiple enabled
lanes, pending external obligations, terminal ownership, reserve policy and
shared assets require their own complete source classification. This report
does not choose policy values or infer that missing lane provenance is present.

## Acceptance and remaining obligations

The required minimized failing positive scenario was: commit the existing
module/coordinator/epoch fixture through normal isolated journal APIs, capture
the authentic-by-construction test predecessor/current pair, admit its module
witness, derive the allocation and pass the existing checker. Before repair,
the old root-scope path rejects `JOURNAL_ROOT_DRIFT`. The expected new path must
preserve the two distinct module/coordinator roots and all stored bytes.

Independent negatives must include a foreign module witness/private port;
stale or substituted predecessor; mismatched current root or duplicated state
tables; every context coordinate drift; conserved claimant substitution;
changed liability split; missing/extra custody; unsupported lane/family; and
row/atom ceilings. A caller-provided previous fragment or claimant rows must
have no influence because the new API does not accept them. Meaningful mutants
remove each exact binding and must be killed by its corresponding control.

This removes a concrete W04 blocker only for the admitted one-occurrence
transfer relation. Current SHADOW reads establish local journal consistency,
not cryptographic store authenticity. Real module and coordinator receipts,
authenticated snapshot sourcing, historical ownership policy, full formal
projection/refinement, all-lane completeness, multi-command composition and
publication-current authority remain separate obligations. A single module's
pre-state cannot stand in for an epoch predecessor when earlier commands have
already changed that lane within the same epoch.

## Reviewed source identities

```text
437973db878e23ba2b37bdd7a6b761f539167a3468f9fbf4059d3cc9a25cf41e  src/core/global_accounting_lane_producers_v1.py
a926bf7dd37e147b46f4e4815ffc167520d91fca0b2b8df520d3d33ae2a1d213  src/core/asset_transfer_receipt_admission_v1.py
7c043b222d4e8aa3d54477ad7508ff65afd716f1b720f76f63995afc4daa7c1a  src/core/asset_transfer_lane_module_v1.py
6047468214d835ff9d6d9823d845df4ef0c4a1cd6d94f098911377daaf4996ae  src/core/asset_lane_coordinator_v1.py
5420112e2dd321ce7f74604e66c13933ca714fc93467150f5cb6358f403b6839  src/core/asset_lane_projection_v1.py
e27b05cfb6c8749366f11f88856ff25602a0aec9237d64d66b40fc5a84dc6b88  src/core/global_accounting_allocation_certificate_v1.py
7254bc00bf6fe894581e26047486704a9c6385a9c0bb54092b171daa04a21c3c  zk/global_settlement_abi_v1/src/global_accounting_lane_producers.rs
07f8c57310088df79ccb496ffc34e5862e0463468fe2680154ab6deb7eb44b11  zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs
```

## Implemented restricted relation

The approved repair adds `verify_asset_transfer_global_fragment_receipt_v1`
alongside the unchanged module-scoped admission in Python and Rust. Its two
inputs are the opaque verified module witness and
`AssetTransferGlobalAllocationCandidateV1`, an ordinary immutable/borrowed
aggregate of accepted output, explicit occurrence, predecessor and current
state. The aggregate carries no authority. Exact snapshot reconstruction
preserves the existing u64/u128 and per-table bounds.

The occurrence preimage is mandatory. The module journal binds its occurrence
ID, which commits subject, exact command body hash, nonce, height and complete
predecessor global state root. The relation checks that exact preimage, the
adjacent height and the one exact new replay row. It does not derive occurrence
identity from height. The selected module verifier already authenticates the
subject/body/policy relation before minting its witness; this entry point
retains that premise by checking the exact journal through the legacy admission.

The new relation refuses multiple enabled lanes, foreign context/release,
projection-root or complete projection-table drift, altered claimant identity
or split, reserve/outbox/terminal state, changed oracle state and replay drift.
It derives entitlements from the complete unchanged predecessor liability
table. It uses only internally derived module coordinates for the existing
module admission, then lifts its receipt-bound fragment to the checked common
projection root inside the private witness owner. The certificate and producer
registry are unchanged. No arbitrary root-lifting constructor was exposed.

The new ordinary-commit integration scenario creates the restricted test profile
and complete state before mock signing, admits activation and one epoch through
the existing journal/writer interfaces, captures its actual committed
predecessor/current snapshots, and reaches SHADOW `PROJECTED`, `AGREES`,
`DIFFERS` and visible `MISSING_WITNESS`. Module and coordinator roots remain
distinct. All database-family byte hashes, logical rows and the profile remain
unchanged by admission and observation. The earlier two-root discovery remains
retained because it documents why the separately named path is necessary.

Verification:

- **183 Python tests passed:** new global allocation tests, historical module
  admission, historical projection, projection parity, and SHADOW integration.
  The new controls include eight in-memory semantic guard-family bypass
  mutants, conserved predecessor/current claimant substitutions, exact foreign
  receipt rejection, zero/one/large atom cases, the full 4096-row claimant
  partition, a conserved first-to-last row shift and 4097-row boundary rejection.
- **77 Rust release/module/route harness tests passed**, including the five
  allocation projection cases and historical module admission tests. The new
  opaque-receipt positive case has nonempty custody, with Alice as claimant and
  a distinct custodian. Its negative controls preserve totals while changing
  predecessor/current claimants, or substitute a foreign module witness.
- **16 shared pure-relation vectors passed in Rust** after Python independently
  checked the explicitly specified reject outcomes. They bind context,
  occurrence subject/body, predecessor identity, root scope, duplicate economic
  tables, claimant continuity and unsupported/replay state. This is differential
  relation evidence; these vectors do not mint or verify a cryptographic receipt.
- Rust library Clippy with `-D warnings`, Python Ruff, new-helper mypy, fixture
  replay, formatting and whitespace checks passed. The security scanner's
  eleven Rust findings are `expect` calls inside `#[cfg(test)]` fixture decoding;
  none is in runtime admission. The source style is deterministic functional
  core, with an explicit immutable snapshot boundary.
- Targeting the existing Python admission with mypy reports four pre-existing
  dictionary-splat type errors in `_rebuild_prior_fragment_v1`. Repeating mypy
  with `--shadow-file` containing its exact c6 source reproduces the same four
  errors. The unrelated old helper and historical behavior were preserved.

Replay from the repository root:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/core/test_asset_transfer_global_allocation_v1.py \
  tests/core/test_asset_transfer_receipt_admission_v1.py \
  tests/core/test_global_accounting_allocation_projection_v1.py \
  tests/core/test_global_accounting_allocation_projection_v1_parity.py \
  tests/integration/test_global_allocation_shadow_v1.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/render_asset_transfer_global_allocation_v1_golden.py --check
PYTHONDONTWRITEBYTECODE=1 python3 -m mypy --follow-imports=silent src/core/asset_transfer_global_allocation_v1.py
```

Rust commands were run from `zk/global_settlement_abi_v1`, using a previously
populated `CARGO_TARGET_DIR` and no dependency downloads or guest proof builds:

```bash
CARGO_INCREMENTAL=0 cargo test --offline --lib global_allocation_relation
CARGO_INCREMENTAL=0 cargo test --offline --test lane_module_release_route_binding
CARGO_INCREMENTAL=0 cargo clippy --offline --lib -- -D warnings
```

The new shared fixture is
`tests/data/asset_transfer_global_allocation_v1_golden.json`. Regeneration is
`python3 tools/render_asset_transfer_global_allocation_v1_golden.py`; it stores
the exact four source hashes as well as the sixteen relation cases. Changing a
source requires rerunning that recorded command, then both parity checks.

Remaining nonclaims are unchanged: real receipt qualification, authenticated
store ancestry, authorized original claimant allocation, arbitrary command
histories, multiple lanes, formal refinement and publication mediation are
separate unfinished obligations. The read-only SQLite observer can still
contend with writers in DELETE journal mode; no mounted timing/resource
isolation is claimed. This implementation closes the scoped two-root derivation
defect and tests an ordinary committed transfer observation. It does not close
whole W04, W05, W06 or production value safety.
