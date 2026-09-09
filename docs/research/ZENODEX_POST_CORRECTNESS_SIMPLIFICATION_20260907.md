# Post-correctness simplification in V3

Status: **bounded proposal review complete; scalar-copy patch applied**,
updated September 8. Five Luna
Max tasks and an independent overlapping Opus review have root dispositions
below. Each reviewed selected functions and evidence, with explicit scope
limits. The scalar-copy adoption below has focused source and runtime evidence;
the remaining proposals are not qualified source patches.

The [September 8 follow-up](ZENODEX_SIMPLIFICATION_REVIEW_20260908.md) records
Fable 5.1's formal-core proposals and independent Astra Max/Daybreak Max reviews.
It narrows journal, decoder and acceptance-check sharing, rejects context aliases
and replacement-API removal, and retains custody/provenance obligations for a
V2 migration. Its counterexamples prevent treating those proposals as equivalent
refactors. The scalar-copy result below remains a separate completed patch.

This September 7 execution addendum implements the user's request to examine
simplification after an initial correct implementation. It operates within
W07, W09 and W13 of the admitted V3 graph. It does not replace that immutable
graph, select another active plan, change economics or grant authority.

The reviewed source subject is
`8217e2f9e3c7b50d6ac6d5df91752755badd472b`. Candidate discovery may run while
correctness work continues. Application requires the corresponding boundary's
correctness evidence, complete caller review and requalification of the actual
patch. Formal-core and production completion remain separate open obligations.

## Acceptance rule

Prefer deletion, direct functions and derivation of non-independent data when
they reduce maintenance, proof, state or measured resource burden. Preserve the
applicable accepted outputs, first rejection code/detail, canonical bytes,
authorization, ownership, supplied commitments, effects, retries and recovery.
Keep policy, rounding, wire commitments and historical decoding fixed during a
refactor. Representation changes need an explicit old-to-new contract and an
appropriate compatibility or version-transition decision.

A source hash identifies what was reviewed. A syntax observation is advisory.
Bounded model equivalence or minimum guard count does not prove whole-runtime
equivalence. A smaller candidate is adoptable only after its actual callers and
relevant formal/runtime evidence preserve the contract. No candidate score or
line count establishes the remaining amount of possible simplification.

## Reviewed candidates

### Scalar receipt-field copies

**Applied after the affected boundary's passing correctness baseline.**
The two positional reconstruction helpers
`_copy_verified_zdex_lane_fields_v1` in
`src/core/zdex_purchase_burn_receipt_preparation_v1.py` and
`_copy_verified_zdex_fee_allocation_fields_v1` in
`src/core/zdex_fee_allocation_receipt_verification_v1.py` were removed. Their
single internal callers now use `dataclasses.replace` after the existing
exact-type, scalar and digest checks.

These particular records have no custom methods, initialization hooks or
non-init fields, and carry exact scalar/enum values. The proposed replacement
removes 33 positional field arguments and their synchronization burden while
constructing a distinct object. It relies on dataclass metadata; it is not a
general deep-copy operation and must not be extended to nested state without
separate ownership evidence. No performance improvement is claimed.

Independent root review compared eight scalar vectors, including nondefault
root fields, and checked that mutation of the original record did not affect
either copy. An in-memory substitution of the two helpers passed the 164
purchase/burn and fee-allocation boundary tests. Source-structure tests still
read the unchanged files during that experiment. That initial in-memory
experiment did not qualify an applied source patch.

The subsequent source patch, based on `7a3fc5198`, removes the two helpers and
33 positional field arguments, a net reduction of 47 production lines. Both
records are exact frozen/slotted dataclasses with only scalar/enum fields, no
initialization hooks and no non-init fields. Instances cannot override the
dataclass metadata. Root checked that the syntax-tree changes are limited to
deleting the helpers and replacing their two calls; validation order is unchanged.

The retained boundary suites passed all 164 tests before and after the patch,
including existing negative, detachment and callback-mutation checks. Ruff and
focused MyPy passed. Existing unrelated formatting was preserved. The exact
candidate hashes, in the path order above, are
`a2b28e1a376f1aaa98e017d51e54ede0de1cf983f7cf058af414e71ad4464a70`
and `dfec6e0134939ee59a24c803671503eef339afbce19d8820f9c026f75bf5d29a`.
This is a scoped simplification with unchanged field values and snapshot
ownership. Full critical-quality, global typing-ratchet, guest and release
qualification gates were not rerun for this patch; no source pin or release
claim was promoted. Focused replay:

```bash
python3 -m pytest -q tests/integration/test_zdex_purchase_burn_verifier_boundary_v1.py tests/integration/test_zdex_fee_allocation_verifier_boundary_v1.py
```

### Removing the prepared Spot price-authority root

**Do not adopt as an equivalent refactor.** Opus proposed deriving
`PreparedZDEXBuybackSpotSafetyReceiptV2.price_authority_root` solely from its
nested witness. Internally prepared records already satisfy that equality, but
the prepared record is caller-constructible. Changing only its stored root
leaves the witness and journal comparisons intact and is currently rejected.
No hash collision is needed for this counterexample.

The retained `wrong_price_authority_root` case in
`test_prepared_record_requires_exact_types_and_request_to_marker_binding`
observes that rejection at the snapshot, marker factory and executor, with no
backend call. Removing the field changes the input representation and this
observable contract. A future representation redesign must account for every
constructor/decoder and retained negative obligation before changing that test.
This review changes neither the field nor the test.

### Generic cross-lane leaf snapshot adapter

**Retain the two typed adapters.** The reviewed untyped replacement for
`snapshot_zdex_spot_buyback_leaf_v2` and
`snapshot_zdex_tokenomics_buyback_leaf_v2` would need to reintroduce lane
selection, exact-type rejection and distinct journal snapshot behavior.
Deleting wrapper lines offers no demonstrated reduction in the contract.
The same-shaped records carry different lane identities, domains and effects.
Cross-lane and forged-handle rejection evidence remains necessary.

## Root disposition of the remaining Luna reviews

**Spot nested witness snapshots: retain.** Directly aliasing the price-authority
witness removes transitive ownership. The retained
`test_aliased_price_authority_mutant_is_killed_by_the_post_callback_completion_law`
shows the resulting failure after a successful callback. The unchanged test was
included in the 291-test baseline. Generic copying needs the same exact types,
roots, integer bounds and nested-witness validation; no replacement was qualified.

**Tokenomics field copies: retain the detachment obligation; queue the bounded
scalar-copy proposal above.** Luna's concern about shallow copies applies to
both the explicit constructor and `dataclasses.replace`. These current call
sites run the exact scalar validator without tuple exemptions, and explicitly
close the receipt-kind enum. The root trial supplies the execution evidence
missing from the read-only review. A future nested field, initialization hook
or different validator requires a new ownership assessment.

**Managed supply snapshots: reject the private-table shortcut; queue a narrower
candidate.** Passing `_policies`, `_balances` and `_supplies` directly into
`ManagedAssetLifecycleStateV2` changes validation order. An oversized table
with an invalid element produces an element error through the current owning
property and a ceiling error through the shortcut. Root found five different
outcomes across 14 explicit valid/malformed vectors.

The smaller candidate instead retains `state.policies`, `state.balances` and
`state.supplies` and removes only the extra copy around each already owned
property value in `_snapshot_state_v2`. Constructor copying, canonical checks,
table ceilings, zero-supply identities and property rejection order remain.
It removes one intermediate copy per table on this path; constructor and
canonicalization copies remain. This candidate matched all 14 vectors and kept
nested detachment. The managed lifecycle suite passed 27 tests on the baseline
and with an in-memory substitution. No source patch or performance claim is
qualified. Preserve these counterexamples and run the complete affected callers
before adopting a patch.

The zero-identity formal obligation stays open. A registered zero-supply asset
and an unregistered asset have the same empty numeric support but different
legal continuations. Reuse carried policy identities; do not add a duplicate
committed registry or infer registration from positive supply alone. The
partial review snapshot omitted consumers: the full checkout's V2 asset
coordinator does check policy-to-origin membership. That is snapshot-local
binding, and does not close cryptographic authentication or V2 runtime/formal
refinement. Absence from the review packet is not absence from the repository.

**Transfer projection: retain canonical replay insertion and owned state.**
Append-only insertion fails when the new replay ID sorts before an existing ID;
reusing the old tuple omits the occurrence. Existing capacity, continuity and
mutation tests retain these obligations. A faster ordered-insertion algorithm
would still need equivalent duplicate handling, rejection order and Python/Rust
results plus measurements. No such performance candidate was qualified here.
The apparent missing-asset-lane difference is constrained by Python's predecessor
snapshot, whose state constructor requires every ABI lane in canonical order.
It is not a demonstrated reachable cross-language counterexample.

## Qualification and remaining checks

The unchanged Spot core and the three affected receipt-boundary suites passed
291 tests on the pinned source. All callbacks in these suites are deterministic
test verifiers; the run does not establish cryptographic receipt validity or
publication authority. The in-memory copy experiment is supporting evidence
for one proposed implementation choice, not a qualified source refactor.

The simplification skill separately qualified its AST observer, restricted
source/body and decision comparers, exhaustive finite guard minimizer and Lean
table export with 227 tests. Its finite optimum is over the declared guard
deletion space and admitted table. Python translation and source/model
correspondence remain tested/reviewed dependencies, without a general
machine-checked refinement theorem. Existing Lean, ESSO, Kani, Tau and runtime
evidence must be selected for each actual ZenoDEX change.

No runtime code, proof statement, policy value, wire format, active graph,
publication capability or release status changes in this addendum. The next
correctness work takes precedence over applying an unqualified simplification.

Both V3 plan checkers passed. The broader claims-registry checker failed because
claim 123 names `tools/check_derivatives_authorization_matrix.py`, absent from
the pinned tree. That existing missing artifact is outside this documentation
change; no full claims-registry success or release qualification is reported.
