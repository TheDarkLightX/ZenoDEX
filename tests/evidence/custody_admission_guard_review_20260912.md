# Custody constructor admission and conservation binding review

Reviewed implementation: `0f14e8dc294df181c9ffc40de7136449f118d452`,
including runtime repair `f0b11b5578c52b7fb0b39fd690d2207278d2a9d9`.
Baseline: `5e1e5a9e84b162ebfa3c0e00fcf78aef6968d38a`.
This is a curated review record, not a private reasoning transcript.

## Subjects and independent review

| Subject | SHA-256 |
| --- | --- |
| `lean-mathlib/Proofs/AssetLaneCustodyAdmissionV2.lean` | `8d3b78d134bbb00e566a73d47c132af571875afae8871d7c13e6c75c242cad64` |
| `tests/formal/asset_lane_custody_admission_v2_controls.lean` | `f215f353aaa18c6de3ed3c5f6c686f13ee5983f627561dfb89a1b01e5f78f32f` |
| `tests/formal/asset_lane_custody_admission_v2_witness.lean` | `e0415851508dfa5d2abdd9e476675ba29b8b041b604262b4ee89df7b1908f234` |
| `tests/formal/test_lean_asset_lane_custody_admission_v2.py` | `5fa0bf7aad3d1384169b014083c4a3430c0d45b7cb1eed3413e21375831ec4d9` |

The native GPT-6 reviewer checked constructor correspondence and theorem premises,
then constructed and compiled the three accepted-action witnesses. Its exact
provider model identifier was unavailable. Daybreak (`gpt-daybreak-blue-latest`)
independently reviewed the final source/test pair and accepted its scoped claims
with no remaining blocker. Daybreak ran Ruff and repository-config MyPy and
inspected the fresh parent test receipt: four passed in 188.49 seconds, no skips.
It did not rerun that whole dependency build concurrently.

Constructor admission reuses the existing complete structural and resource
predicates. Added metadata covers registry validity and release, exact managed
policy coverage, optional identity agreement, record/policy syntax and custody
order. Policy-origin binding remains a separate phase. Its membership relation
needs constructor-supplied registry uniqueness for runtime lookup correspondence.
Post resources remain an explicit general-theorem premise.

The witnesses establish all premises for actual finite transfer, issue and burn.
Each derives its actual leaf acceptance and modeled post resources before using
the preservation theorem. The runtime test binds exact initial state, contexts,
commands and resulting balance/supply rows. The two commitment expectations are
computed from actual policy contents. No arbitrary successor or registry-derived
expected commitment supplies the conclusion. Twenty-two axiom audits transitively
cover helper proofs; only standard axioms occur.

## Repaired findings and falsifiers

- A coherent internally injected USD transfer leaf could report conservation
  for unchanged EUR. Python and Rust now require the command asset. Retained
  baseline/mutant runs accept the bad candidate; repaired runs return exact
  coordinator projection rejection, unchanged roots and empty effects.
- The candidate constructor predicate omitted custody order. A reversed-only
  state remains structurally balanced and within resources but fails complete
  constructor admission. A compiling guard-removal mutant admits it.
- The candidate incorrectly rejected the legal zero issue-policy-root sentinel.
  Unmanaged/native positive controls fail under the compiling nonzero-only mutant.
- The draft test used registry values to predict their own policy commitments.
  Final tests independently hash complete policy values and reject transfer-root
  and managed-root drift separately. Full-policy matching replaces an earlier
  asset-only witness lookup.

The [delivery record](custody_admission_guard_v2_20260912.json) retains the full
commands, source pins, failed attempts, mutations and limits. Four archived Python
runtime mutants, a compiled Rust guard mutant and two compiling Lean predicate
mutants are distinct evidence campaigns; hash-pin failures are not semantic kills.

## Fixed-rubric assessment

After the frozen four-test gate passed, the independent GPT-6 reviewer recommended
only `generic_transfer.prf`, `managed_issue.prf` and `managed_burn.prf` change from
0.75 to 0.76. The inhabited preservation result supports this small partial proof
increment. All other capability components, workstreams, uncertainty labels,
weights and release flags remain inherited unchanged.

The increment is `3 * 0.4 * 0.01 = 0.012` formal units out of 140, about 0.00857
percentage points. The unchanged calculator validates the frozen
[before](v3_custody_admission_assessment_before_20260912.json) and
[after](v3_custody_admission_assessment_after_20260912.json) inputs: formal central
21.094% to 21.103%; V3 central remains 23.869%. Rounded lane fields yield the
reported delta. This is an advisory narrow amendment, not a new whole-checkout
assessment. No complete lane, route or value-safety gate closes.

## Limits and next integrated condition

These are three independent one-step actions from one fixture. The new runtime
comparison covers balances/supplies; other existing tests own their broader
complete-state scope. Root syntax is bounded, namespace syntax is permissive,
digest is opaque, and sampled Python policy hashes are not universal Lean hashing.
The wrong-asset/source tests model faulty internal leaves, not an exposed runtime
callback or demonstrated remote exploit.

The next coherent bundle is the complete ordered coordinator outcome plus source
journal/effect relation, aggregate resources/reprojection and runtime correspondence.
Reuse the admitted FullState and current leaf/effect proofs. Universal codec,
root, authentication, genuine guest/receipt and publication qualification remain
separate unmet obligations. No production or full formal-core completion is claimed.
