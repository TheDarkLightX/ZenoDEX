# Checked finite question-identifiability theorems

Status: `PROVED` for the abstract Lean statements below. The checked source is
[ZenoLacuna.lean](../../../lean-mathlib/Proofs/ZenoLacuna.lean). This result adds
formal evidence for exact filtering and finite-language identification. It does
not establish a refinement between Lean and the Python implementation.

## Model and assumptions

`C` is a type of already-identified semantic classes. `V : Finset C` is the
finite initial candidate set, and `answer : Q → C → A` supplies a total,
deterministic answer for each question and class. Filtering requires decidable
answer equality. A transcript is a finite list of question/answer pairs.

`filterAnswers` actually executes one finite-set filter per transcript entry.
`filterQuestions` constructs the faithful transcript for a fixed intended class
`truth`. Its question sequence may be empty, repeated, or reordered. The
complete signature is the list of answers to the whole supplied question list.
`Separates` requires a differing answer for every distinct pair initially in V.

Truth retention and singleton recovery require `truth ∈ V`. The theorem does
not establish that real human intent belongs to V, or that an actual owner gives
faithful answers. The semantic quotient and answer congruence are premises of
this model: the proof starts with classes and a function on those classes.

## Exact checked statements

All names below are in namespace `ZenoLacuna`.

| Theorem | Checked conclusion |
| --- | --- |
| `mem_filterAnswers` | Induction over operational filtering: a class survives exactly when it was initially present and agrees with every transcript entry. |
| `separates_iff_signature_unique` | Pair separation is equivalent to injectivity of complete answer signatures on V. |
| `mem_filterQuestions` | Faithful filtering returns exactly the signature-equivalence class of the truth intersected with V. |
| `faithful_truth_survives` | A truth initially in V survives every faithful finite question sequence. |
| `complete_faithful_filter_singleton` | Separation and initial truth membership imply that asking the full question list returns exactly `{truth}`. |
| `separates_iff_complete_filter_singleton` | Separation holds if and only if every initially present truth is recovered as a singleton by complete faithful filtering. |
| `indistinguishable_pair_survives` | Two initial classes with equal language signatures both survive any finite sequence drawn from that language, answered faithfully for the first class. |
| `indistinguishable_pair_prevents_singleton` | If that pair is distinct, the result of every such sequence differs from every singleton. |
| `demo_two_questions_separate` | For `Fin 3`, Boolean questions qA=(0,1,1) and qB=(0,0,1) separate all three classes. |
| `demo_complete_filter_recovers_each_class` | Asking qA and qB faithfully recovers each of the three concrete classes. |
| `demo_sole_question_does_not_separate` | The sole question qA fails pair separation on the same three-class set. |
| `demo_sole_question_never_identifies` | For truth 1, every finite sequence containing only qA retains the ambiguity between classes 1 and 2 and therefore cannot return any singleton. |

The concrete examples use Lean's kernel-checked `decide`, without native
evaluation or additional decision-procedure axioms. The general sequential
filter theorem uses list induction. The singleton results derive from that
operational invariant and the signature-separation equivalence.

## Replay receipt

Checked on 2026-09-08 with the existing pinned environment:

```text
leanprover/lean4:v4.27.0
Lean 4.27.0, x86_64-unknown-linux-gnu, Release
Lean commit db93fe1608548721853390a10cd40580fe7d22ae
```

From `lean-mathlib/`, run:

```bash
lake env lean Proofs/ZenoLacuna.lean
```

The command passed with exit code 0 and no warnings. It also prints the axiom
dependencies of all twelve theorems. Their union is the standard Lean axioms
`propext`, `Quot.sound`, and `Classical.choice`. There are no custom axioms or
unfinished proof placeholders. The repository proof-placeholder scanner passed.

| Artifact | SHA-256 |
| --- | --- |
| `lean-mathlib/Proofs/ZenoLacuna.lean` | `d84b1ed792196ee9a73e68b0b8d2294063e1c9307f19401ae02d998bc0669690` |
| `lean-mathlib/lean-toolchain` | `d55ca0039a5479db5b38919d005b2c427b89b3be4f0184a20f2f4eae931f5bdb` |
| `lean-mathlib/lake-manifest.json` | `98ac9d887f935c4e0a87859b00511866f4e9b816e5e1246f428779fa4c8ec046` |

The only import is `Mathlib.Data.Finset.Basic`. The check reused existing local
dependency artifacts. No dependency download, project rebuild, aggregator edit,
or downstream import build was performed. No dedicated Python formal-test twin
exists for this new file.

## Claim boundary and next proof target

The proof does not cover Python execution, canonical encodings, quotient
construction, source hashes, authentication, resource budgets, graph adapters,
runtime correspondence, or the closure checker. It does not prove the Bellman
recurrence, worst-case cost 2, stable tie-breaking, or the implementation's
`EXACT_MINIMAX` label. The sole-question result proves permanent finite-sequence
ambiguity; no numeric infinity or policy cost model is defined here.

The next formal target is a finite decision-tree cost semantics connected to
the implemented Bellman recurrence. A separate refinement obligation must bind
the concrete Python class/answer tables and filtering operations to this Lean
model before claiming that the implementation inherits these theorems.
