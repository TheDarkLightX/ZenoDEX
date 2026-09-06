# Completed transfer annotation refinement

This W09 increment extends `991d7a6fb547722deb38584bf50239144b73e36d`.
It proves the existing global `AnnotationMirrors` relation for the actual
completed ASSET_TRANSFER V1 mathematical transition. Runtime economics, fee
policy and publication authority are unchanged.

## Derived contract

`AssetTransferAnnotationMirrorsV1.complete_annotation_mirrors_iff` starts from
quantitative pre-state admission, command constructor bounds and actual
acceptance by `AssetTransferPolicySelectionV1.step`. It derives:

```text
AnnotationMirrors (complete fields input).plan
  iff
there exists a policy selected from input.pre for input.command.asset
  with fee = 0 or feeOwner != sender
```

The theorem derives the selected policy, accepted leaf and structural plan
admission. It takes no caller-selected policy, desired post-state, admitted
output, row shape or aggregate-width conclusion as a premise. A separate
selected-policy theorem exposes the reduction for downstream proofs.

The full relation contains five clauses:

| Clause | Derived reason |
| --- | --- |
| Every ordered state-bearing subtotal fits i128 | Each contribution fits, and at most one row contributes nonzero at each owner/asset/accounting-location key. |
| Positive fee allocations have matching state-bearing credit | Actual alias aggregation yields `-amount`, `amount + fee`, or `fee` at the selected fee owner. |
| Reward and slash annotations are mirrored | The transfer emits neither kind. |
| Fee-conservation rows charge a positive amount | Zero fee omits the row; the admitted nonzero fee is positive. |
| Designated and carried fee residues agree | Both quantities are zero in the constructed transfer. |

The prefix proof uses unique complete effect keys and the actual emitted kinds
to derive the single-contribution property after canonical sorting. Its generic
list lemma proves every intermediate subtotal from that property. It makes no
general claim that reordering preserves overflow safety.

The four clauses independent of fee-owner aliasing hold for every accepted
completion from an admitted pre-state. A positive fee credited to the sender
fails the fee-credit clause because that owner's net movement is negative.
Rejection returns the exact empty plan, which satisfies all five clauses.

## Evidence and replay

The final independent integration replay passed **5 tests in 71.43 seconds**, with
identical semantic source hashes before and after execution. Ruff and
single-file MyPy passed. The proof bytes remain those supplied by the
implementation worker; integration adds registration and strengthens the
test's distinction between the standalone fee checker and the full runtime.
Independent test review confirmed the registration, declaration-order,
reward-label and exact maximum-amount boundary adjustments.

The harness rebuilds a fresh Std-only dependency closure with pinned Lean
4.27.0. It independently restates all eight public theorem signatures, checks
registration exactly once, scans for unproved declarations, and checks
transitive axioms against `propext`, `Classical.choice` and `Quot.sound`.
Nonempty admitted witnesses apply the actual front-door, sender-refusal and
rejection theorems. The sender witness also proves that only the fee-credit
clause fails.

Eighteen public Python transition vectors cover fee-owner aliases, zero and
positive fees, different asset policies and i128 boundary neighbors. Expected
movements and eligibility come from submitted commands and policies. Rejected
vectors check exact codes, unchanged owned inputs, equal pre/post roots and
all six empty effect fields.

Fourteen constructed plans exercise intermediate overflow with a representable
final sum, independent key coordinates, insufficient or misattributed credit,
zero fee rows and residue mapping. Lean proves the intermediate-overflow
counterexample against the actual `StateBearingAggregatesFitI128` relation.
Two deliberately wrong executable models are refuted: final-total-only bounds
and unconditional fee-mirror eligibility. These are model-level counterfactuals;
they are not source mutations of the production checker or the new theorem.

The standalone `_require_fee_mirror_v1` observer accepts an orphan reward
label. The full runtime's `_require_supported_effects_v1` rejects that same
plan with the exact unsupported-label error, without changing the plan. Lean
also refutes its `RewardSlashMirrored` and full `AnnotationMirrors` relations.
This control prevents the executable observer from being mistaken for the
complete global contract on arbitrary plans.

The executable residue observer uses lists while Python uses mappings. These
comparisons cover plans with unique residue and fee keys, as enforced by the
runtime constructors. They establish no general equivalence for malformed
duplicate-key inputs.

```bash
python3 -B -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_annotation_mirrors_v1.py
python3 -m ruff check \
  tests/formal/test_lean_asset_transfer_annotation_mirrors_v1.py \
  experiments/v3_transfer_annotation_mirrors_v1/render_evidence.py
python3 -m mypy tests/formal/test_lean_asset_transfer_annotation_mirrors_v1.py
python3 tools/scan_lean_proof_placeholders_v1.py --json \
  lean-mathlib/Proofs/AssetTransferAnnotationMirrorsV1.lean
python3 -B -m experiments.v3_transfer_annotation_mirrors_v1.render_evidence
```

The proof SHA-256 is
`81e0fae0addd597b509f7890e4fa8cb1206f6b650414a5db948fcb75633afc30`.
The renderer pins the declared sources and tests in
`THV1-20260906-transfer-annotation-mirrors-v1.json`. Rendering executes no test
and grants no authority.

## Remaining obligations

This closes the annotation relation for this constructed mathematical transfer
family under its explicit input premises. It does not close the full global
`Verified` construction. Global custody conservation, lane-root updates,
replay/height progression, lifecycle composition, canonical bytes and decoder
outcomes retain their separate obligations. Opaque commitment strings remain
unauthenticated; pre-state policy selection does not establish governed
profile membership or command-signature authority.

Finite Python comparisons and executable observer agreement do not establish
universal Python, Rust or compiler refinement. Cryptographic receipts, actual
store provenance, publisher mediation, recovery and deployment qualification
remain separate. Full Lake/Mathlib, Cargo, guest, GPU and release gates were
not run for this increment. The formal core and whole V3 plan remain open.
