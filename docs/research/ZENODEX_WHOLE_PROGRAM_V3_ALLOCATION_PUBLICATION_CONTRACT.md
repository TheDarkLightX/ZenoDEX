# Isolated ASSET allocation publication contract

Implementation checkpoint, 2026-09-05: the pure consumer in
`src/core/asset_transfer_epoch_allocation_v1.py` now performs ordered membership,
fragment derivation, twelve-slot projection and mandatory certificate checking.
It grants no publication authority and is not yet mounted in the publisher.
Its current positive scope is one occurrence with zero custody. Retained tests
expose two further composition obligations: same-height intermediate epoch
states fail the standalone height-step relation, and nonzero transferred-asset
custody fails the existing module/coordinator conservation-total comparison.
These are unfinished requirements, not completed disabled features.

Consumer source SHA-256:
`f4f1383101224a20652d6c1a0d3c87159604dfd831b35baa9f780de23f4a1c4d`.
Test source SHA-256:
`243e30d5a9268b0663e4eb40c7ad7c06c33098cddf0a3cbbbe02b11c8b4f509e`.
The following command passed 244 tests, including the 28 new consumer controls:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q --tb=short -p no:cacheprovider tests/core/test_asset_transfer_epoch_allocation_v1.py tests/core/test_asset_transfer_global_allocation_v1.py tests/core/test_asset_transfer_receipt_admission_v1.py tests/core/test_global_accounting_allocation_projection_v1.py tests/core/test_global_accounting_allocation_certificate_v1_golden.py
python3 -m ruff check src/core/asset_transfer_epoch_allocation_v1.py tests/core/test_asset_transfer_epoch_allocation_v1.py
python3 -m mypy --cache-dir=/dev/null src/core/asset_transfer_epoch_allocation_v1.py tests/core/test_asset_transfer_epoch_allocation_v1.py
```

Ruff and mypy passed. No Rust or Lean proof build is claimed for this consumer.
The design handoff below is retained with its original reviewed subject.

Date: 2026-09-05. Status: `REVIEWED_DESIGN_HANDOFF`, authority `NONE`.

Subject: committed `0bb6ac79c3d505c0a01eb0cfd4dfb281c9499ae6` plus the separately
identified frozen ASSET route candidate. This note recommends a bounded consumer;
it does not report that consumer as implemented or qualified. The author
implemented the W04 relation, Rust projection and accounting lift, so examination
of those components is self-review. Publication and disclosure analysis is an
additional read-only integration review.

The existing journal contains enough predecessor information for restricted
ASSET allocation continuity. Add current module evidence to the isolated
publication input, derive allocation rows from the acquired state, and require
the existing certificate checker before constructing a durable epoch bundle.
No new predecessor-allocation or claimant journal commitment is required for
this scope.

## Scope and questions that the consumer must answer

The scoped transition has exactly one enabled lane, `ASSET_TRANSFER`, and one
module occurrence per route. All other lanes remain registered empty. Current
W04 admission requires unchanged custody, the complete claimant table, history
root, oracle occurrences and other lane roots; exact replay insertion; and
empty reserve, outbox and terminal tables on both sides. A non-OPEN terminal
row still lies outside this scope. More enabled lanes or new producer variants
must fail closed until their ownership and admission contracts exist.

For each occurrence the consumer must establish:

1. The predecessor is the exact acquired committed source, or the preceding
   checked intermediate state in the same prospective epoch.
2. The selected module executed the same authenticated command, governed policy
   and private input that produced the disclosed global state projection.
3. That module journal is the exact member of this occurrence's lane journal,
   which is already bound to this occurrence's verified route and epoch.
4. Every controlled-location and claimant row is represented exactly once with
   its original identities, domain, amount and receipt provenance; no supported
   allocation row is omitted or assigned to another claimant.
5. Admission succeeds before publication effects, and the existing commit still
   fences the current head and writer authority.

This is a sufficient disclosure design for the existing restricted interfaces,
not a proof that it is the coarsest possible abstraction. Removing committed
state fields would change the consumer's query surface and is not proposed.

## Authoritative sources and minimum additional disclosures

| Value | Source and check | Additional journal data |
| --- | --- | --- |
| Initial predecessor, source publication, current tip and authority, CAS token | Journal-owned `_publication_source_for_verified_publisher_v1`; complete state decode and head binding under one read transaction | None |
| Selected profile and outer economic policy registry | Publisher selection and the acquired activation's existing `PROFILE` / `POLICY_REGISTRY` components | None |
| Typed asset/fee policy rows | Disclosed `AssetTransferPolicyRegistryV1` preimage; both domain-separated roots must be governed by the selected outer registry | None |
| Authenticated command and exact occurrence | Opaque `AuthenticatedEconomicCommandV1` from the signature boundary, exactly equal to the epoch occurrence at that index | None |
| Module input, including module state and private-port preimage material | Disclosed exact `AssetTransferLaneModuleInputV1`; existing transition recomputation, policy membership and receipt journal binding | None |
| Current module receipt | Exact succinct receipt bytes verified by the selected, measured module endpoint | None |
| Accepted module output and release/route binding | Recompute from the above values; existing candidate fields may be retained as checked redundant disclosures | None |
| Intermediate / final global states and lane journals | Existing ordered `EconomicEpochRouteStateDisclosureV1` values, checked against route and epoch commitments | None |
| Claimant entitlements and allocation roots | Derive from acquired/chained predecessor rows and current verified module fragment; never accept a caller claimant list or prior fragment | None |

The journal's source handle carries data; possession of it does not grant write
authority. Acquisition verifies local canonical contents and committed ancestry
under the journal's process/store assumptions. It does not independently replay
cryptography for every stored ancestor. See
[source acquisition](../../src/integration/global_economic_epoch_journal_v1.py),
`_CommittedEconomicSourceV1` at line 164 and acquisition at line 780, and
[publisher source replacement](../../src/integration/global_economic_durable_publisher_v1.py),
`publish_economic_epoch` at line 892.

The outer policy registry is already retained as canonical activation bytes.
`_validate_policy_payload_v1` binds those bytes to the profile root. A minimal
adapter can compare a supplied exact typed registry's canonical bytes with that
component; an exact typed decoder is another implementation choice. Neither
choice makes an arbitrary caller registry authoritative. The asset-policy
preimage is not presently stored there, but
`require_governed_asset_transfer_policy_registry_v1` and
`require_asset_transfer_policy_membership_v1` authenticate it through the
governed asset and fee roots, selected module release, command asset and every
carried state policy. See [policy membership](../../src/core/asset_transfer_policy_registry_v1.py),
lines 147 and 195, and [activation components](../../src/core/global_economic_durable_activation_v1.py),
lines 466, 719 and 791.

The present `EconomicEpochReceiptCandidateV1` contains route state disclosures
and opaque verified routes. It does not contain module private inputs, accepted
private ports or module receipts. `VerifiedRouteCompositionV1` exposes bound
commitments rather than these preimages. Reconstructing missing module evidence
from those hashes is unavailable. The smallest practical change is a closed,
ordered sidecar of module disclosures, owned and checked by the isolated shell,
without changing existing receipt journals or their roots.

An existing `AssetTransferLaneModuleReceiptCandidateV1` is a reusable internal
adapter shape. Its profile, policy registry, accepted output and release binding
are redundant input fields, not fresh sources of authority. A narrower external
disclosure can omit derivable fields and materialize that existing candidate
inside the shell. Missing evidence must reject this publication path; it must
not become a warning, optional observation or caller-selected bypass.

## Concrete admission sequence

Preserve the publisher's existing immutable snapshots, exact selected-profile
comparison, source acquisition, verifier identity checks, atomic commit and
monotonic-anchor outcome handling. Insert a mandatory bounded allocation gate
before durable bundle construction. A successful projection alone is not the
acceptance criterion.

For occurrence `i`, use the journal's acquired source for `i = 0` and the
previous checked disclosure thereafter. Require equal counts for occurrences,
module disclosures, route journals, route disclosures and route effects; use
strict ordered pairing. A final-state witness cannot cover omitted intermediate
occurrences. Retain the epoch's 1–64 command ceiling. Qualifying one occurrence
first is valid if the unqualified larger scope remains explicit.

1. Bind the disclosure's authenticated command to the exact epoch occurrence,
   selected profile, governed policy and module release. Use
   `transition_asset_transfer_lane_module_v1` and
   `bind_asset_transfer_lane_output_to_release_route_v1` when constructing the
   internal existing receipt candidate. The latter recomputes supplied output;
   duplication can be avoided only without weakening ordered validation.
2. Invoke `verify_asset_transfer_lane_module_receipt_v1`. Its structural binding
   checks, deterministic output recomputation and exact image/journal receipt
   verification construct `VerifiedLaneModuleTransitionV1`.
3. Bind the same accepted module journal to the disclosed
   `LaneCompositionJournalV1.ordered_module_journal_roots`. For this coordinator
   the tuple must equal `(accepted.module_journal.journal_root,)`. Require the
   same occurrence and existing exact route/lane membership and order checks.
   A shared post-state root alone is insufficient membership evidence.
4. Pass that opaque module witness to
   `verify_asset_transfer_global_fragment_receipt_v1` with
   `AssetTransferGlobalAllocationCandidateV1(accepted, occurrence, predecessor,
   current)`. This relation checks exact before/after projection rows, both
   coordinator roots, context, occurrence/predecessor root/height, claimant
   continuity, unsupported state and exact replay insertion. It derives all
   claimants from predecessor liabilities. It retains the distinct module and
   coordinator roots; neither stored root is rewritten.
5. Construct the twelve ordered witness slots with this ASSET witness and eleven
   `None` entries. Derive the only supplied lane binding pair from
   `(ASSET_TRANSFER, witness.fragment.binding_root)`. Invoke
   `project_allocation_certificate_v1(current, binding_pairs, witness_slots)`.
   Require its exact certificate result, then require
   `check_global_accounting_allocation_certificate_v1(certificate, current,
   witness_slots)` to return `AllocationCertificateAcceptedV1`.
6. Continue existing epoch verification and publication binding checks. Before
   committing, retain the same bound verifier identity and selected profile.
   The journal's existing CAS and current-authority checks remain the
   linearization fence. Allocation acceptance grants no publication capability.

The generic `BoundEconomicReceiptVerifierV1.verify_succinct_receipt` accepts
only its root image. Module admission needs a shell-owned narrow adapter that
delegates to `verify_profile_lane_receipt` with the selected profile, lane and
module release. The existing `_ProfileLaneReceiptVerifierV1` in
[purchase/burn receipt verification](../../src/core/zdex_purchase_burn_receipt_verification_v1.py)
at line 907 shows the adapter shape. Use the measured
[isolated verifier-set factory](../../src/integration/isolated_economic_verifier_set_v1.py)
for all selected endpoints; the root-only factory cannot qualify module
verification. No caller-supplied backend or image choice may replace it.

The global fragment admission docstring currently calls both snapshots
"adjacent committed state." For prospective publication, only the initial
source is committed. Each later state is a candidate checked by the exact
module relation and enclosing route/epoch contract. This wording should be
clarified when the consumer is implemented, without attributing store authority
to an immutable Python value.

## Why a previous allocation receipt is unnecessary here

The current module/private-port journal already commits its before and after
projections. Its verified preimage is compared with complete predecessor rows.
The full predecessor claimant table comes from committed state, and the entire
table plus custody is required unchanged. The current certificate then checks
the exact per-domain partition and all row identities. An independently
caller-supplied previous fragment would add an unverifiable authority premise;
it supplies no missing information for this restricted transition.

Genesis has no previous module receipt. Current exact partition plus unchanged
custody/claimants also establishes that same partition for the predecessor.
This does not authorize the original assignment of claimants. Initial source
classification and its authorization commitments retain their explicit
initialization/policy premises. Wrongful ownership already present at genesis
is not repaired by conservation or continuity. This agrees with the retained
[W04 binding review](ZENODEX_WHOLE_PROGRAM_V3_ALLOCATION_BINDING_REVIEW.md),
"Predecessor sufficiency and ownership limits," and the
[accounting source classification contract](ZENODEX_ACCOUNTING_SOURCE_CLASSIFICATION_CONTRACT_V1.md).

The new [constructive Lean lift](../../lean-mathlib/Proofs/AssetTransferGlobalPreservationV1.lean)
derives `step_owned_supply` from the existing transfer semantics, explicit
single-asset representation, exact-once principal coverage and pre-state owned
supply. `step_exact_allocation` preserves the per-domain equality through its
unchanged frame; `step_changes_only_for_context_subject` and
`run_preserves_accounting` add scoped authorization and finite-trace results.
Its `ExactAllocation` predicate is an aggregate equality, while runtime
certificate checking additionally binds exact row identities and receipt
provenance. The theorem is not a full runtime `Verified` constructor. Its
nonzero-terminal example does not widen the current runtime admission scope.
Accounting uses physical balances/custody/reserves as owned atoms; liabilities
are entitlements and are not added to physical supply again.

## Independent semantic controls for the new consumer

The following are required implementation tests, not newly executed results in
this design pass. Retain existing core certificate, projection, W04 relation,
signature, source-acquisition and publisher regressions.

| Control | Required observation |
| --- | --- |
| Correct module receipt, nonzero custody and exact original claimants | Full admission, projection and checker acceptance followed by complete atomic publication |
| Account recipient or fee-owner substitution preserving total supply | Command/policy/module projection binding rejects; allocation alone is not the oracle |
| Redistribute claimant amounts or replace claimant identity while conserving per-domain totals | Whole-table continuity or exact certificate/fragment identity rejects |
| Substitute a predecessor claimant table and rebuild its state root | Original occurrence's authenticated predecessor-root binding rejects |
| Omit a claimant, duplicate a semantic key or duplicate a lane/module disclosure | Exact row decoder, partition or cardinality/order check rejects without silently normalizing |
| Shift identical amounts across control domains or controlling principals | Exact rows and same-domain partition reject |
| Omitted / injected / differently owned terminal row, including CLOSED-only input | Current restricted relation refuses all nonempty terminal tables; no claim of terminal support |
| Nonempty reserve/outbox; extra enabled lane; unsupported producer | Closed scope refusal, even if total supply is conserved |
| Valid module proof for a different occurrence, module journal or lane-journal member | Exact occurrence and singleton membership refuse before commit |
| Missing witness, foreign/fake/unresolved receipt, unavailable endpoint | Explicit admission failure; no observational fallback |
| Correct candidate under stale head, revocation or competing writer | Existing CAS/current-authority refusal; source validation cannot upgrade stale authority |
| Exact committed retry after a later head, or lost response after commit | Historical source remains usable for exact retry; preserve existing committed-retry / indeterminate outcome classes |
| Any precommit allocation failure | No economic state, replay consumption, history entry or outbox effect attributable to this attempt |

Include semantic mutants removing module membership, claimant identity equality,
the mandatory certificate call, and exact disclosure cardinality. Each mutant
must fail a retained behavioral oracle. Logical rejection purity permits
database housekeeping and another concurrent winner. Do not use physical file
equality as the only concurrent purity oracle.

## Retrieval and evidence limits

Research Kernel retrieval was available and queried read-only with:

- `ZenoDEX O-008 allocation certificate authenticated predecessor journal sufficiency claimant ownership`
  using lexical, semantic, failures and contradictions modes, limit 6.
- `"O-008" "allocation" "predecessor"` using lexical, failures and contradictions
  modes, limit 4.

Both returned `ok: true`; neither recovered an accepted current O-008 decision.
Adjacent historical results concern exact claimant-row distribution and a
refuted aggregate-determines-allocation claim. Useful returned content hashes
were `sha256:ec160d34bd755f4fa774e175e8f57cf19046e8540e90dca0a9f2e85e87e9b233`
and `sha256:b8122c08c1249afd0ce01f27311166458e45363fe9a1324ff63a80734a66550b`.
They are retrieval leads, not acceptance evidence. LEAP campaign tools were
available, but no applicable existing campaign identifier or prior-decision
retrieval endpoint was identified; no LEAP verdict is claimed. No research
atom, claim or authority record was promoted.

Evidence here is source inspection (`rg`, `sed`, `sha256sum`, Git subject and
dirty-file inventory) and the existing accepted contracts. The style classifier
identified a public claim surface. No new proof compilation, solver campaign,
Rust build, runtime test, remote job or live publication was performed. The next
step is the isolated consumer and its source-bound semantic controls. Production
no-bypass, compromised-process/OS resistance, original claimant authorization,
all twelve lanes, terminal/external lifecycles and full runtime/formal refinement
remain outside this handoff.

## Exact inspected source subjects

SHA-256 entries below identify the inspected bytes, not a complete transitive
release manifest. The ASSET route file is an uncommitted candidate at this HEAD;
the listed Python, ABI and Lean files match the committed subject when read.
Parent implementation can supersede these bytes without retroactively changing
this review subject.

```text
e45ffb3b2851fbaba9de869f9af6c5a03da64fa8b71ade2d8d3f59aea57c1780  src/integration/global_economic_durable_publisher_v1.py
7c52b02dae0fe2ab9650543a82b96d3761cef698f278e4107a36938173faa08a  src/integration/global_economic_epoch_journal_v1.py
71f27ecafb61568c89fdd861787316ab4725f561484c64821a723d81a652d57d  src/core/global_economic_durable_activation_v1.py
f9ff27f3d346c2099ab3678ae87961cbc09653b6c641650ea0db0bf3bac23a50  src/core/global_economic_proof_v1.py
518ecd4a92593d7b7108e45787334e6c44201ef15510fc8e234e60aa30f92829  src/core/lane_module_receipt_verification_v1.py
842897dea14ab65e3bccee6c13a44f4f56e6533a6daf3a0844f00372d3bf305c  src/core/lane_module_release_route_binding_v1.py
3078bb86c1225a9035d1603654a901973092ef9d430959ba4c18f83d97863a0d  src/core/asset_transfer_policy_registry_v1.py
a11df90d2ccba89063b14ea9f740352bcdb439a3cfd5ab79544524041aaddfca  src/core/asset_transfer_global_allocation_v1.py
091e206cd7baa10f5ad020bc660213cf0ef1c01fbd4675b305413d5035052a57  src/core/asset_transfer_receipt_admission_v1.py
10433a18db25b4c2e6932d08c9749083daec881aff2bb58a77fdb64db31c364f  src/core/global_accounting_allocation_projection_v1.py
e27b05cfb6c8749366f11f88856ff25602a0aec9237d64d66b40fc5a84dc6b88  src/core/global_accounting_allocation_certificate_v1.py
eb36d6a631e875777c565c77ff3f9c9955e1e89e599a7c2cd820dae6fd990fff  src/core/economic_receipt_verifier_deployment_v1.py
5bf788f676c771a6ee0dd80ab30a53a289037314d2419d0984d2c573e081becd  src/integration/isolated_economic_verifier_set_v1.py
c66448fb090a687aebfa00b1fa31b01099e24087e8cbf50ce9763b5c03e0d8d0  src/core/economic_command_authentication_v1.py
96efc2020805b63bb6e7798b9c97aec66207d7e4f45f3450a32e0cc1df556a48  zk/global_settlement_abi_v1/src/asset_transfer_global_allocation.rs
4129a028378b1cac34c0395f3315cfab0d613d58003d2e2424d3ea05efd320ff  zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs
de91fa4425f541a41d18cfca7a7ceb7cd769987c4e273696db1fb5dbec8727e7  zk/global_settlement_abi_v1/src/global_accounting_allocation_projection.rs
538428762e558db31db886f9662329a4e8787875ca9e1186d87882ca201526af  zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs
350d22ed8796f9c847913f7b5a03f079ec33b484de1786fe3e95158c514aec7f  lean-mathlib/Proofs/AssetTransferGlobalPreservationV1.lean
0a242f0a22edb9faa9358919a06fec28e800a88deadb27a1a1978d76df1d7cf3  zk/asset_transfer_route_composer_risc0/shared/src/lib.rs
```
