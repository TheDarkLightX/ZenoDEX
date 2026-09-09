# Simplification review: completing the existing contracts

Status: independent proposal reviews complete; runtime changes unimplemented.
Subject: `3a20d7aa9884a662b3f7cf79f11f6f9562c8a7d0`.

Fable 5.1 Max used the assurance-preserving-simplification skill and inspected
selected committed source. Astra Max and Daybreak Max independently reviewed
the same report and checked omitted callers in the repository. Root reviewed
their conclusions and reproduced the context/replacement observations.
The report identity is
`96db523a2a40e6b9fc3d47085446e76f5cb844dba47561e3249a6043df3b8cbb`.
Both independent reviews verified the 95-file packet against its pinned source.
The AST observer parsed 41 Python files in two batches; its syntax findings
were advisory. An initial over-limit batch returned INCOMPLETE and was retained.

## Why substantial code still leaves substantial work

The [progress assessment](ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.md) estimates
partial obligation completion. It supplies no multiplier for remaining code or
time. Its formal-core denominator includes semantics, preservation proofs and
implementation refinement for all 103 capabilities, plus composition obligations.
An implementation or finite theorem can advance a row while other parts remain
open. The twelve lanes have different semantics and cannot be extrapolated as
eleven more copies of the transfer leaf.

There is a concrete integration split. The inspected publisher calls the V1
isolated receipt pipeline and allocation checker; the current module and
coordinator guests depend on the V1 ABI. The new V2 asset leaves and their finite
outcome proofs have no direct consumer under `src/integration`. Connecting the
same semantics through runtime, proof, receipt and publication is therefore a
material completion target. This does not make V1 code or proofs obsolete:
V2 already reuses V1 mathematical results, and V1 carries required custody work.

Python, Rust, Lean and wire representations also repeat field lists and checks.
Some repetition can be reduced. Other repetition separates input types, error
contracts, receipt domains or authorities. Removing those distinctions changes
the contract even when successful values serialize identically. Completion also
requires recovery, finality, authenticated history and genuine-receipt evidence;
those obligations cannot be inferred from a smaller functional core.

## Root dispositions

| Fable proposal | Disposition | Smallest supported direction |
| --- | --- | --- |
| C1: shared leaf journal/receipt constructor | Narrow before implementation | Consider a private journal field assembler; keep each leaf's typed receipt body, fixed hash domain, fallible order and caller binding. |
| C2: one Python V2 decoder | Revise | Share identical lexical machinery while preserving each public decoder's limits, error class, labels and first-failure order. |
| C3: one accepted-result predicate | Revise | Share only identically ordered facts. Keep coordinator validation and its outbox, policy and source-binding checks independent. |
| C4: alias the two context types | Reject as a refactor | Preserve nominal types and cross-type rejection. Equal canonical bytes do not establish equal input contracts. |
| C5: remove private constructor keywords | Reject as proposed | Preserve supported `dataclasses.replace` reconstruction, explicit public overrides and nested ownership. |
| A1: make V2 the sole forward producer | Prepare a migration comparison | Preserve all seven ASSET_TRANSFER capabilities, including custody, before selecting and qualifying the successor guest/publisher path. |
| A2: replace the allocation chain with derivation | Investigate sufficiency | Reuse existing derivation; retain independently authenticated producer and ownership provenance until a sufficient replacement is established. |

These dispositions authorize no release and certify no unimplemented patch.
C1 is optional to specifying the concrete constructor relation. It should be
implemented only if the actual patch reduces field-maintenance or proof burden
without adding a generic receipt framework. It does not halve the complete
constructor/refinement obligation.

## Concrete reasons for the revisions

- **C1 remains fallible.** A zero digest only during receipt construction raises
  `ValueError("derived root must be nonzero")` in both leaves. This is a
  controlled fault case, not a discovered SHA-256 preimage. Receipt hashing
  precedes journal construction. Preserve the two leaf-owned receipt domains;
  an arbitrary domain/type pairing is an unnecessary new invalid combination.
- **C2 has different first errors.** With 65 consumed IDs and a non-text last
  element, the ABI decoder reports that element; the wire decoder reports its
  64-item ceiling. Daybreak independently observed a similar distinction with
  an invalid chain ID. Adopting the earlier ceiling in both changes behavior.
- **C3 has different check order.** With both an invalid release and post root,
  the coordinator reports the post root first; the proposed shared predicate
  reports the release first. Moving its outbox or policy checks also changes
  invariant ownership. Keep the retained forged-context/outbox cases.
- **C4 rejects equal-valued foreign contexts.** Both leaf transitions reject
  the other exact context type. Root also observed a valid transfer succeed,
  reject a managed context with the same fields, and succeed when those fields
  are deliberately reconstructed as the proper transfer context.
- **C5 supports intentional overrides.** Existing tests require replacement of
  states, contexts and hostile candidates. In particular,
  `replace(context, occurrence=None)` supplies stored `_occurrence` together
  with the new public override. Root rejects Daybreak's suggested exactly-one-
  spelling repair because it would break this supported update. Public-over-
  private precedence alone does not establish an invalid economic state.

## Larger architectural savings require a complete replacement contract

The existing [custody semantic bundle](../specifications/asset-transfer-custody-semantic-bundle-v1.json)
assigns nonzero custody and claimant liabilities to ASSET_TRANSFER. That scope
cannot be moved into a disabled EXTERNAL_CUSTODY lane to simplify the successor.
V2 leaf balances permit only the accounts domain, and its aggregate requires
account totals to equal supply. A V1 state with accounts B and positive custody C
backing supply B+C therefore has no demonstrated lossless mapping to that V2
aggregate. Preserve its custody frame, historical verification, replay identity,
writer fencing and all four publication outcome classes before a cutover.

Allocation derivation already exists in `_derived_global_entitlements_v1` and
the epoch allocation checker. Avoid porting redundant commitments mechanically.
However, equal tables or totals do not establish that those tables came from
the producer bound to the lane root. The retained Alice/Mallory claimant
substitution case behind one opaque lane root demonstrates this provenance gap.
It is not an identical-full-input counterexample to every possible V2 derivation.
Different complete liability tables are different retained inputs.

Define the exact allocation queries and subsequent operations. Prove that the
retained authenticated state and pinned ownership policy determine their
answers, then preserve the smallest independent witness for information that
cannot be derived. Source authentication and commit-time revalidation remain
separate obligations. The reviews establish no 2,500-line saving or replacement
for every lane's ownership contract. Old unresolved-policy records and an absent
proposed filename also do not establish that later policy decisions are absent.

## Next substantive formal-core action

Specify the transfer constructor's relation to its actual owned prepared input,
actual post-state/effects, exact receipt preimage and emitted journal, including
rejection and hash/constructor faults. Reuse existing finite accounting and
encoding results. Introduce only missing metadata and explicit projections.

Correct Fable's proposed Lean setup: `AssetTransferRefinementV2.Context` has no
writer epoch. Its occurrence and `GlobalEconomicStateRefinementV2.CommandOccurrence`
are different projections; neither alone represents the full runtime occurrence.
An admitted journal, supplied successful POST or successful constructor cannot
serve as a premise that substitutes for the relation being proved.

Extend the retained independent consumer to check all journal fields and exact
receipt preimage bytes, with wrong-field, wrong-domain and zero-root controls.
Keep the managed and coordinator instantiations explicit. A finite corpus can
support that scoped relation; it cannot close the first open W09 checklist item,
which also requires universal parser and execution refinement. No new wrapper
theorem or tracker gate should be counted as that closure.

## Evidence and limits

Astra checked ten deterministic observations and ran this unchanged baseline:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/core/test_asset_transfer_module_v2.py \
  tests/core/test_managed_asset_lifecycle_module_v2.py \
  tests/core/test_asset_lane_coordinator_v2.py \
  tests/core/test_global_settlement_abi_v2_codec.py \
  tests/core/test_global_settlement_abi_v2_wire_records.py \
  tests/core/test_global_settlement_abi_v2_managed_asset_golden.py \
  tests/core/test_global_settlement_abi_v2_asset_lane_coordinator_golden.py
```

Result: **114 passed in 3.37 seconds**. Daybreak executed independent decoder,
nominal-context and replacement controls. Root reproduced the context and
replacement observations. These results characterize the existing contracts;
they do not qualify candidate implementations.

No runtime code was changed by this review. No Lean/Rust/Kani build, ESSO run,
guest proving, migration, deployment or full release gate was performed. The
formal functional core and V3 remain incomplete. The reviewed scope, explicit
counterexamples and revised next action are the result of this review cycle.
