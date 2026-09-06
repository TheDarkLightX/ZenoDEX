# Custody-complete transfer conservation

This W09 increment extends `694ddd82ae6672e76cf165a0aab6789be4c4e7bc`.
`AssetTransferCustodyEffectPlanV1` constructs the custody-complete successor of
the existing mathematical transfer plan and derives its global conservation
relations. Runtime economics, policy, wire values and authority are unchanged.

## Constructed contract

The constructor evaluates `AssetTransferEffectPlanV1.complete`, then replaces
only the two physical-total fields in each accepted conservation row. Each
value comes from the actual pre-state or constructed post-state:

```text
physical(asset) = balance atoms(asset) + custody atoms(asset)
```

For example, 57 balance atoms plus 43 custody atoms produce a physical total
of 100. A claimant liability records a claim on physical custody; adding that
liability again would double-count the assets.

The broader global model also counts reserves. The restricted custody runtime
port has no reserve table, and its global binding rejects reserve-bearing state.
Empty initial reserves is therefore an explicit premise where this proof relates
the private total to global `ownedFor`. The actual transfer preserves custody
and reserves; no caller-supplied post-custody total is needed.

| Derived result | Initial premises beyond actual acceptance |
| --- | --- |
| Structural `EffectPlanAdmitted` for every outcome | Selected-policy state admission and global quantity admission; acceptance is not required. |
| Exact table and supply effects | Selected-policy state admission. |
| Exact conservation coverage and rows matching global state | State admission, unsigned command constructor bounds, empty reserves. |
| Post-state owned-supply equality for every asset | State admission and initial owned-supply equality. |
| Full annotation eligibility iff zero fee or fee owner differs from sender | State admission and unsigned command constructor bounds. |
| Exact rejected result and six empty plan fields | Actual front-door rejection; no admitted output premise. |

The structural result derives u128 physical bounds from initial quantity
admission. Balance and custody totals are nonnegative and cannot exceed the
already bounded global physical total, even when reserves are present. The
selected sparse transition preserves the account total, and its frame preserves
custody. Both new physical fields consequently remain bounded and conserved.

For exact coverage, policy selection is derived from the actual front door.
Every emitted effect and fee row refers to the commanded asset. Command bounds
and accepted guards imply a nonzero sender movement. The actual sparse update
then proves that this asset is physically touched and that every other asset
is unchanged. The completed conservation row covers precisely that asset.

The runtime conservation guard separately checks owned-supply equality for
every state asset before checking coverage and individual rows. The preservation
theorem supplies the post equality from the initial equality; row correspondence
alone would not rule out an initial supply mismatch in an untouched asset.

Annotations observe the unchanged effect and fee rows. Their existing
five-clause characterization transfers directly. A positive sender fee retains
the existing global fee-mirror refusal. Verdict, post-state, the other five plan
fields, and each conservation row's asset/supply/issue/burn fields remain exact
mathematical values. Rejection retains the entire original rejected result.

## Evidence and replay

The frozen proof passed a pinned Lean 4.27 warnings-as-errors compile and root
mathematical review. Independent root replay passed all 11 focused tests in
56.74 seconds with the proof and test hashes unchanged. Ruff and single-file
MyPy checks passed for the test and evidence renderer.

The harness rebuilds the Std-only source closure, independently restates all
public theorem signatures, checks registration, and limits transitive axioms to
`propext`, `Classical.choice` and `Quot.sound`. Nonempty witnesses establish the
input premises and apply the actual front-door results for multiple assets,
physical custody and separate claimant liabilities.

Expected runtime balances, physical totals and covered assets come from the
input tables and command. Direct economic delta/conservation observations use
synthetic metadata; they do not represent authenticated adjacent global
snapshots, normalized coordinator roots or a publication. Rejection controls
check exact codes, unchanged canonical input, equal roots and all six empty
effect fields. Invalid constructor exceptions remain a separate outcome class.
The actual conservation guard rejects omitted custody, double-counted claimant
liabilities, missing or unrelated conservation rows, and an untouched-asset
supply mismatch. The row controls also preserve the observed states and plan.

A command-premise control examines the mathematical input domain. An admitted
state can accept a negative amount equal to minus the fee when the fee owner
is the recipient, leaving every physical delta zero. Lean proves that this
command violates `CommandWellFormed`. The runtime constructor excludes it.
This control prevents acceptance alone from being used to infer physical
movement. A separate reserve example shows why the global correspondence needs
the reserve restriction.

The source mutation removes custody from the actual `physicalFor` definition
in a private definitions-only copy. Paired witnesses distinguish the original
100-atom projection from the mutant's 57-atom projection against the same
global conservation-row obligation. This is a bounded projection mutation
check; it is not a complete mutated upstream proof or a production mutation
score. Model and runtime guard controls retain their separate scopes.

```bash
python3 -B -m pytest -q -p no:cacheprovider \
  tests/formal/test_lean_asset_transfer_custody_effect_plan_v1.py
python3 -m ruff check \
  tests/formal/test_lean_asset_transfer_custody_effect_plan_v1.py \
  experiments/v3_transfer_custody_effect_plan_v1/render_evidence.py
python3 -m mypy tests/formal/test_lean_asset_transfer_custody_effect_plan_v1.py
python3 tools/scan_lean_proof_placeholders_v1.py --json \
  lean-mathlib/Proofs/AssetTransferCustodyEffectPlanV1.lean
python3 -B -m experiments.v3_transfer_custody_effect_plan_v1.render_evidence
```

The proof SHA-256 is
`77364c36dbd2f8730ec9683167915b914e2ad9a4aa5a7d9c726e69bf89f8fa23`.
The renderer pins the declared sources and tests in
`THV1-20260906-transfer-custody-effect-plan-v1.json`. Rendering executes no
proof or test and grants no authority.

## Remaining obligations

The next construction must derive the restricted global post-state, including
normalized lane roots, height and replay, before assembling the full global
`Verified` witness. Positive movement alone does not mathematically establish
unequal cryptographic hashes. Module state, private-port state, global state,
journal and receipt roots retain distinct meanings.

These mathematical and finite runtime results do not establish canonical
decoding/encoding, universal Python/Rust/compiler refinement, command-signature
or governed-policy authority, receipt validity, store provenance, publisher
mediation, recovery or deployment qualification. The formal and runtime general
touched-asset definitions differ; correspondence here is restricted to the
constructed well-formed transfer family. Nonempty terminal-domain mapping also
remains a separate cross-runtime obligation.

Full Lake/Mathlib, Cargo, guest, GPU and deployment gates were not run for this
increment. Other lane lifecycles, the formal core and whole V3 remain open.
