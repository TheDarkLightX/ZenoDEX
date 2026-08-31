# GlobalSettlementABI V2 O-008 bounded-core evidence

Subject: `1a1edeb569dc71aedbe0ea75bdc61758e6f583cc`

Manifest SHA-256: `5f376b7003ac05c6ea674c58c15df4b917239ab243d6d1273789ed91bcadda52`

Status: `BOUNDED_CORE_EVIDENCE_ONLY`. Promotion is false. Authority is
`NONE`. O-006, O-007C, and O-008A remain `OPEN_UNVERIFIED`; zero of the 12
whole-value-movement gates pass.

The JSON manifest is the normative packet. Its normalized field registry gives
every implemented global and asset-slice record a field owner, producer, value
profile, unit, width, rejection boundary, projection order, and canonical
collection key. Records with an implemented encoder also list their exact
lexically sorted canonical wire-key order. Observable-only records are marked
`GAP_NO_CANONICAL_ENCODER` and assert no wire order. Array order remains the
semantic or owning-type key order.

Collection cardinality is not fully closed by this packet. Global and asset
collections mix explicit ceilings with fields that have no explicit item
bound. The registry therefore asserts no universal item ceiling and records
`collection_bound_completeness` as a gap.

The global refiner checks aggregate per-asset owned/supply conservation,
independent issue and burn projections, liability backing, claimant terminal
bounds, fee allocation/residue mirrors, exact lane-write coverage, occurrence
consumption, and typed reject-as-no-op. This is structural coverage over all 12
registered lanes. It does not establish the missing lane-semantic transitions.
Only the asset slice has bounded leaf semantics here; Rust has the transfer leaf
but no V2 managed-lifecycle or asset-lane coordinator counterpart.

The transfer leaf locally conserves sender, recipient, and fee-owner deltas,
including same-key alias aggregation. A sender who is also fee owner can still
fail the global fee-allocation mirror because the aggregated state-bearing row
is a net debit. Local conservation therefore does not imply global acceptance.

The cited Lean files prove bounded mathematical models for global refinement,
asset transfer, managed issue/burn authorization, reject no-op, widths,
conservation, coordinator projection, a stateful issue-transfer-burn trace, and
explicit negative examples. They do not prove hash/codec equivalence, runtime
mounting, profile or release authentication, settlement, RISC0, Tau,
publisher behavior, migration/recovery closure, or production authority.

Replay:

```bash
python3 tools/check_global_settlement_abi_v2_o008_evidence.py
```

A successful replay validates this historical, source-pinned bounded packet.
The report separately states whether current checked-out pinned source bytes
still match; descendants may preserve the historical packet without implying
current applicability after source drift.
