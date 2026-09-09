# ZenoLacuna acceptance contract

Status: `PLANNED`. These are future tool acceptance cases. No case in this
document or in `scenarios.json` is a passing implementation result.

The first milestone is finite and local. The acceptance subject is one frozen
`Scope = (source_root, semantics_root, D, A, O, K, H, Q, M, limits)`. A case
may produce an evidence receipt, a typed rejection, a classification, or an
inconclusive result. A model, swarm, solver, or heuristic can propose a
candidate; an independent oracle decides the case.

For rejection cases, the exact no-semantic-effect observation is:

```text
state_root, effect_plan, outbox, current_revision, semantic_history,
question_bindings, and protected K are byte-for-byte unchanged; the result is
the named typed rejection. A diagnostic rejection receipt may be appended
outside semantic_history.
```

The `persona` field identifies the primary actor: `human`, `swarm`, or
`human+swarm`. The JSON catalog has a closed top-level shape, schema
`zenolacuna/acceptance-v1`, and closed scenario fields:
`id`, `obligation_ids`, `persona`, `given`, `when`, `then`, `oracle`,
`mutant`, `scope`, and `status`. Every catalog status is `PLANNED`.

## Obligation map

| ID | Acceptance coverage |
| --- | --- |
| ZL-01 | S01, S02: premises and distinguishing behavior are independently checked |
| ZL-02 | S03, S04, S29: complete observations, intentional nondeterminism, and trace-union closure |
| ZL-03 | S05, S06, S07, S19, S26: exact filtering, conflicts, language limits, and quotient questions |
| ZL-04 | S08, S09, S10, S28: protected requirements, positive witnesses, and assumption narrowing |
| ZL-05 | S11, S12, S21, S29, S30: code/spec/model classifications and runtime scope |
| ZL-06 | S06, S09, S13, S18, S19, S27, S28, S32: fail-closed closure and inconclusive evidence |
| ZL-07 | S02, S14, S15, S16, S17, S24, S32: authority, freshness, duplicates, and no-effect behavior |
| ZL-08 | S11, S12, S13, S21, S30: source-bound runtime correspondence |
| ZL-09 | S19, S20, S26, S27, S31: truthful question selection and exact-DP limits |
| ZL-10 | S15, S17, S22, S23, S24: stale decisions, cancellation, crash, and restart |

## Planned BDD scenarios

Each case below is represented verbatim by its stable ID in the machine catalog.
`MUT-*` names a semantic mutant and the text after `killer=` names the
independent observation that must kill it.

### ZL-S01 accepted distinguishing witness

- Given a finite witness whose assumptions hold, whose two candidate outcomes both satisfy the current declared contract, and whose complete projections under `O` differ.
- When a human submits it and the independent finite evaluator replays both outcomes.
- Then the result is `ACCEPTED`; the receipt binds the premise digest, differing observation, source revision, and scope.
- Oracle: an evaluator enumerates every premise and every field of `O` without calling the candidate relation helper.
- Mutant: `MUT-ZL01-PREMISE-DROP; killer=flip one premise and require REJECTED:WITNESS_PREMISE_FAILED`.
- Scope: `FINITE_RELATION`; persona: `human`.

### ZL-S02 invalid witness is an exact no-op

- Given a witness with one false premise and a proposed semantic disagreement.
- When the swarm submits it for admission.
- Then the result is `REJECTED:WITNESS_PREMISE_FAILED` and the exact no-semantic-effect observation holds.
- Oracle: an independent premise evaluator recomputes the false predicate and snapshots state, effects, outbox, revision, and semantic history.
- Mutant: `MUT-ZL01-PREMISE-DROP; killer=the false premise is independently observed and all semantic snapshots remain equal`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S03 semantic classes use the complete observable relation

- Given two interpretations with different source text but equal allowed relations over every context and every `O` outcome, plus a near pair differing only in rejection or terminal effect.
- When the quotient operation groups interpretations into semantic classes.
- Then the equal pair shares one class, while the near pair remains separate because rejection, effects, or terminal state is observable.
- Oracle: an exhaustive relation comparator constructs fresh tuples for all `D × O`; it never compares source strings.
- Mutant: `MUT-ZL02-DROP-REJECTION-OBSERVATION; killer=the near pair must compare unequal`.
- Scope: `FINITE_RELATION`; persona: `human+swarm`.

### ZL-S04 intentional nondeterminism remains an allowed set

- Given an interpretation that intentionally allows exactly outcomes `{o1,o2}` for one context and rejects `o3`.
- When the evaluator replays the context with each outcome in different order.
- Then both allowed outcomes remain in the relation, `o3` is rejected, and no representative outcome is silently selected.
- Oracle: an independent set-valued evaluator compares the complete allowed set and reports membership for each replay.
- Mutant: `MUT-ZL02-COLLAPSE-ND-SET; killer=permuting replay order still requires `{o1,o2}` and rejects `o3`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S05 a question retains exactly compatible interpretations

- Given a nonempty interpretation set `V`, a total question `q`, and answer `a` whose independently computed compatible subset is `{h1,h3}`.
- When the human records answer `a` for the frozen parent revision.
- Then the result retains exactly `{h1,h3}`, binds `q`, `a`, witness, parent revision, owner decision, and expected revision, and changes no unrelated interpretation.
- Oracle: an independent filter recomputes `answer(q,h)` for every member of `V`.
- Mutant: `MUT-ZL03-FILTER-SUBSET; killer=the omitted compatible member h3 is required in the resulting set`.
- Scope: `FINITE_RELATION`; persona: `human`.

### ZL-S06 an empty H is a conflict, never completion

- Given a frozen scope whose declared interpretation family `H` is empty after checked constraints.
- When the swarm requests closure.
- Then the result is `REJECTED:EMPTY_H_CONFLICT`, workflow remains `INCONCLUSIVE`, and the exact no-semantic-effect observation holds.
- Oracle: an independent cardinality check verifies `|H| = 0` and rejects any completion transition.
- Mutant: `MUT-ZL03-EMPTY-H-COMPLETE; killer=empty H must prevent COMPLETE_FOR_SCOPE`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S07 an outside-language answer preserves the prior revision

- Given a pending question whose answer language excludes the submitted answer token.
- When a human answers with a concrete interpretation outside `Q`.
- Then the result is `NEEDS_MODEL_REVISION`; the prior revision remains current and the exact no-semantic-effect observation holds.
- Oracle: an independent closed-enum decoder checks the answer language and compares the current pointer and parent revision.
- Mutant: `MUT-ZL03-OUTSIDE-ANSWER-AS-DEFAULT; killer=an unknown answer must not select the first interpretation`.
- Scope: `FINITE_RELATION`; persona: `human`.

### ZL-S08 protected K and required positive behavior survive repair

- Given a previous approved scope with protected `K` and a repair proposal that changes a disputed behavior while claiming preservation across every protected applicability class.
- When the swarm submits the repair for preservation checking.
- Then the result is accepted only if every protected clause, every applicable input class, and every required positive witness remains reachable and implies the previous obligations.
- Oracle: an independent implication and reachability checker evaluates old and new relations over all declared `D`.
- Mutant: `MUT-ZL04-DROP-PROTECTED-K; killer=remove one K clause and require REJECTED:PROTECTED_REQUIREMENT_LOST`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S09 vacuity cannot supply a positive witness

- Given assumptions and guards that make every required success path unreachable, while all rejection checks pass.
- When the human requests `COMPLETE_FOR_SCOPE` without a positive witness.
- Then the result is `REJECTED:MISSING_POSITIVE_WITNESS` and the exact no-semantic-effect observation holds.
- Oracle: an independent reachability evaluator searches the finite domain for each required positive behavior and records none.
- Mutant: `MUT-ZL04-VACUOUS-POSITIVE; killer=an inconsistent or overstrong A cannot satisfy the positive-witness requirement`.
- Scope: `FINITE_RELATION`; persona: `human`.

### ZL-S10 a disagreement that both implementations satisfy is a missing requirement

- Given two runtime implementations that both satisfy the current written specification on `D`, yet differ on an unmentioned compatibility outcome and a human owner has not selected an interpretation.
- When the swarm presents the checked disagreement.
- Then the classification is `MISSING_REQUIREMENT`, workflow is `NEEDS_DECISION`, and no code repair or completion is authorized.
- Oracle: independent spec parity plus the witness evaluator confirms both implementations refine current K and the observed outcomes differ.
- Mutant: `MUT-ZL05-MISCLASSIFY-MISSING-AS-CODE; killer=both parity checks must remain true while code-repair authorization stays absent`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S11 a current-spec violation is a code bug

- Given one candidate that violates an approved requirement on a declared input and a second candidate that satisfies it.
- When a human reviews the independently replayed witness.
- Then the classification is `CODE_BUG`, the failing candidate is named, and the requirement revision remains unchanged.
- Oracle: an independent runtime/model parity oracle evaluates the approved predicate and exact output for the input.
- Mutant: `MUT-ZL05-CODE-BUG-AS-REQUIREMENT; killer=approved K remains fixed and the violating candidate is identified`.
- Scope: `FINITE_RELATION`; persona: `human`.

### ZL-S12 an unmodeled runtime trace is a model omission

- Given a runtime adapter trace containing an authenticated or freshness-relevant event that is absent from `D` or `O`.
- When the swarm attempts to promote model evidence.
- Then the classification is `MODEL_OMISSION`, dependent evidence becomes `UNKNOWN`, and no repair or completion is issued.
- Oracle: a source-bound trace schema comparison finds the runtime field outside the frozen model observation projection.
- Mutant: `MUT-ZL05-MODEL-OMISSION-SILENCE; killer=the missing field must force MODEL_REVISION_REQUIRED`.
- Scope: `FINITE_STATE_GRAPH`; persona: `swarm`.

### ZL-S13 source drift invalidates dependent evidence

- Given a witness and runtime receipt bound to source hash `s0`, followed by a source change producing hash `s1` before closure.
- When the human requests replay from the old receipt.
- Then the result is `REJECTED:SOURCE_DRIFT` and the exact no-semantic-effect observation holds.
- Oracle: an independent byte reader recomputes source hashes and compares them with every receipt binding.
- Mutant: `MUT-ZL06-SOURCE-DRIFT-BYPASS; killer=s0 != s1 must block closure before semantic promotion`.
- Scope: `FINITE_RELATION`; persona: `human`.

### ZL-S14 an unauthorized command is rejected without semantic effect

- Given a valid scope and a command signed by an actor outside the declared owner or capability set.
- When the swarm submits a repair or answer command.
- Then the result is `REJECTED:UNAUTHORIZED` and the exact no-semantic-effect observation holds.
- Oracle: an independent capability and owner lookup checks the command against the frozen scope.
- Mutant: `MUT-ZL07-AUTH-BYPASS; killer=replace the actor with an unlisted principal and require the same exact rejection`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S15 a stale answer cannot apply to a new scope

- Given answer `a` bound to parent revision `r0`, followed by a new scope revision `r1` that changes `H`, `A`, `O`, or `K`.
- When a human retries answer `a` against `r1`.
- Then the result is `REJECTED:STALE_ANSWER` and the exact no-semantic-effect observation holds.
- Oracle: an independent revision and dependency-binding comparison checks parent and expected revision IDs.
- Mutant: `MUT-ZL07-STALE-ANSWER-APPLY; killer=the old answer must leave current revision and bindings unchanged`.
- Scope: `BOUNDED_HISTORY`; persona: `human`.

### ZL-S16 an identical duplicate answer is idempotent

- Given one authorized answer already committed for `(scope, question, parent revision)`.
- When the swarm submits the byte-identical answer again.
- Then the result is `ACCEPTED:IDEMPOTENT_DUPLICATE`; the semantic revision, effect plan, outbox, and decision history each remain byte-for-byte unchanged.
- Oracle: a fresh journal reader compares canonical records and verifies one decision binding.
- Mutant: `MUT-ZL07-DUP-IDEMPOTENCE; killer=the second submission must not add a second semantic decision or effect`.
- Scope: `BOUNDED_HISTORY`; persona: `swarm`.

### ZL-S17 a conflicting duplicate answer is rejected

- Given an authorized answer already committed for a question and parent revision, followed by a different answer for the same key.
- When a human submits the conflicting duplicate.
- Then the result is `REJECTED:DUPLICATE_CONFLICT` and the exact no-semantic-effect observation holds; the first answer remains authoritative.
- Oracle: an independent canonical-key index detects the collision and compares both answer digests.
- Mutant: `MUT-ZL07-DUP-CONFLICT-OVERWRITE; killer=the original answer and current pointer must survive unchanged`.
- Scope: `BOUNDED_HISTORY`; persona: `human`.

### ZL-S18 solver UNKNOWN remains inconclusive

- Given a declared solver query that times out, returns unsupported residual quantifiers, or disagrees with its required output shape.
- When the swarm submits the solver result as evidence.
- Then the result is `INCONCLUSIVE:SOLVER_UNKNOWN`; no repair, promotion, or completion transition occurs and the exact no-semantic-effect observation holds.
- Oracle: an independent process-result classifier checks timeout, support, and output closure without trusting the solver's truth claim.
- Mutant: `MUT-ZL06-SOLVER-UNKNOWN-ALLOW; killer=replace a solver timeout with the same accepted repair and require rejection`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S19 no question separator is explicit

- Given surviving semantic classes in `V` and a question language `Q` whose every question gives the same answer to every class.
- When the human requests the next question or closure.
- Then the result is `UNSEPARABLE_IN_LANGUAGE`; no class is discarded and no completion claim is emitted.
- Oracle: an independent partition evaluator checks every question for a strict nonempty split.
- Mutant: `MUT-ZL09-NO-SEPARATOR-COMPLETE; killer=all partitions equal must return the typed unseparable result`.
- Scope: `FINITE_RELATION`; persona: `human`.

### ZL-S20 a DP cap cannot claim optimality

- Given more DP states or question branches than the declared exact budget, with a partial search result that found a candidate schedule.
- When the swarm requests a question-selection receipt.
- Then the result is `INCONCLUSIVE:DP_BUDGET_EXCEEDED` or `HEURISTIC`; it never carries `EXACT_MINIMAX`.
- Oracle: an independent budget counter checks all required states and the label against the declared cap.
- Mutant: `MUT-ZL09-DP-CAP-OPTIMALITY; killer=force early termination and require the optimality label to remain absent`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S21 full finite relation and bounded history have separate claim ceilings

- Given a complete enumeration of one-step inputs but only histories of length at most `k` for retry and crash behavior.
- When a human asks for a promotion label.
- Then one-step claims may be `EXHAUSTIVE_FINITE`, while history claims are `BOUNDED_SEARCH` with bound `k`; the latter cannot become an unbounded liveness claim.
- Oracle: an independent scope checker compares evidence domains and rejects labels outside the enumerated domain.
- Mutant: `MUT-ZL08-BOUNDED-AS-FULL; killer=length k evidence must fail a requested length k+1 promotion`.
- Scope: `BOUNDED_HISTORY`; persona: `human`.

### ZL-S22 a crash during persistence cannot promote a partial revision

- Given an atomic current pointer at `r0` and an interrupted write after a partial record for `r1`.
- When the swarm restarts and runs recovery.
- Then recovery returns `RECOVERED:PREVIOUS_REVISION` or quarantines the incomplete record; `r1` is not current and no partial effect or outbox is visible.
- Oracle: a fresh process parses checksummed records and compares the pointer, state root, effects, outbox, and semantic history.
- Mutant: `MUT-ZL10-CRASH-PROMOTE; killer=truncate every record prefix and require r0 or quarantine, never r1 promotion`.
- Scope: `BOUNDED_HISTORY`; persona: `swarm`.

### ZL-S23 cancellation and restart cannot revive an obsolete decision

- Given an in-flight repair or question decision cancelled before commit, followed by a process restart and a late completion message.
- When a human reopens the workbench.
- Then the workflow is `CANCELLED`; the late message is `REJECTED:STALE_ANSWER`, and the exact no-semantic-effect observation holds.
- Oracle: an independent lifecycle replay checks cancellation generation and late-message parent binding.
- Mutant: `MUT-ZL10-CANCEL-RESUME; killer=late completion must not move the current pointer or revive the cancelled generation`.
- Scope: `BOUNDED_HISTORY`; persona: `human`.

### ZL-S24 retries and reordering preserve one semantic effect

- Given a finite queue containing one valid command, its byte-identical retry, and a different command already stale before either delivery order; rejected diagnostics are outside semantic history.
- When the swarm replays both histories through the same scoped shell.
- Then accepted semantic effects occur once, the already-stale command produces its exact code in either order, and final state, outbox, and decision history are equal across both replays.
- Oracle: an independent state-machine interpreter compares canonical final snapshots and every rejection/no-effect observation.
- Mutant: `MUT-ZL07-RETRY-DUP-EFFECT; killer=duplicate delivery must not duplicate the effect plan or outbox entry`.
- Scope: `BOUNDED_HISTORY`; persona: `swarm`.

### ZL-S25 unallowlisted candidate code cannot execute

- Given a candidate source path outside the explicit adapter allowlist, including an import with a side effect.
- When the human and swarm prepare a replay request.
- Then the result is `REJECTED:UNALLOWLISTED_SOURCE`; no candidate code runs, no source is promoted, and the exact no-semantic-effect observation holds.
- Oracle: an isolated launcher checks canonical path membership before execution and records process effects independently.
- Mutant: `MUT-ZL08-ARBITRARY-IMPORT; killer=an unlisted path must be rejected before import or filesystem effect`.
- Scope: `FINITE_RELATION`; persona: `human+swarm`.

### ZL-S26 questions are total and congruent on the semantic quotient

- Given `h1 ~ h2` in the semantic quotient and a question `q` whose answer relation is defined for every interpretation.
- When the swarm constructs the question partition.
- Then `q` returns an answer for every `h`, and `answer(q,h1) = answer(q,h2)`; a question that distinguishes equivalent source representatives is rejected as non-congruent.
- Oracle: an independent totality check enumerates all interpretations and compares answers within each complete-relation class.
- Mutant: `MUT-ZL03-QUOTIENT-ANSWER-SPLIT; killer=equivalent h1 and h2 must receive identical answers or REJECTED:NON_CONGRUENT_QUESTION`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S27 an unseparable DP child propagates infinity

- Given `V={h0,h1,h2}` and a sole question `q=(0,1,1)` whose child `{h1,h2}` has no separating question.
- When the human requests exact minimax selection.
- Then the child has cost `INFINITY`, the root also has cost `INFINITY`, and the result is `UNSEPARABLE_IN_LANGUAGE`; a useful first split is not reported complete or optimal.
- Oracle: an independent dynamic program returns `INFINITY` for the child and recomputes the parent recurrence from all strict splits.
- Mutant: `MUT-ZL09-DP-INFINITY-DROP; killer=the useful first split must remain incomplete when its only nonsingleton child is unseparable`.
- Scope: `FINITE_RELATION`; persona: `human`.

### ZL-S28 narrowing A cannot erase a protected input

- Given protected behavior for `x=1` under assumptions `A={0,1}`, followed by a proposed scope narrowing to `A={0}` while the positive behavior for `x=0` still survives.
- When the swarm requests preservation of `K`.
- Then the result is `REJECTED:PROTECTED_REQUIREMENT_LOST`; an owner retirement or revision must create a new scope and can never count as preservation of the old `K`, so surviving `x=0` is insufficient.
- Oracle: an independent obligation-domain check compares old and new applicability sets and requires an explicit owner decision for removed inputs.
- Mutant: `MUT-ZL04-ASSUMPTION-NARROWING; killer=the x=1 obligation must remain open despite the x=0 witness`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S29 a union of complete traces does not admit a cross-product trace

- Given two complete allowed trace families `{00}` and `{11}` for one finite context, represented as an approved union.
- When the evaluator computes the combined allowed relation.
- Then exactly `00` and `11` are allowed; `01` is rejected and cannot be introduced by independently unioning positions.
- Oracle: an independent trace-set evaluator compares whole traces, including order and length, rather than taking a per-position product.
- Mutant: `MUT-ZL02-TRACE-CROSS-PRODUCT; killer=01 must return REJECTED:TRACE_NOT_ALLOWED`.
- Scope: `FINITE_STATE_GRAPH`; persona: `swarm`.

### ZL-S30 selected runtime fixtures cannot certify unenumerated inputs

- Given three selected runtime fixtures that all match the model, a broader claimed input domain containing a fourth concrete input, and no enumeration or checked symbolic encoding for that fourth input.
- When a human asks for runtime/model promotion over the broader domain.
- Then the result remains `MODEL_ONLY` or `INCONCLUSIVE:UNENUMERATED_INPUT`; the fixtures may retain evidence under their explicitly smaller scope, while they cannot produce `EXHAUSTIVE_FINITE` or `COMPLETE_FOR_SCOPE` for the broader target.
- Oracle: an independent coverage checker compares the claimed domain with the enumerated concrete inputs and symbolic coverage certificate.
- Mutant: `MUT-ZL08-FIXTURE-COVERAGE-AS-PROOF; killer=the unenumerated fourth input blocks broader promotion while smaller-scope evidence remains scoped`.
- Scope: `FINITE_RELATION`; persona: `human`.

### ZL-S31 exact DP chooses the stable root tie-break

- Given three semantic classes and two unit-cost questions with answer vectors `qA=(0,1,1)` and `qB=(0,0,1)`, where each question separates the child left by the other.
- When the swarm requests exact minimax selection within the full state and work budget.
- Then the result is `EXACT_MINIMAX` with worst-case cost `2`, and stable question-ID ordering chooses `qA` at the root among equal-cost choices.
- Oracle: a separate dynamic program enumerates both roots and all child states, including the second question in each non-singleton child.
- Mutant: `MUT-ZL09-DP-TIEBREAK; killer=reverse input order and require qA, cost 2, with no heuristic label`.
- Scope: `FINITE_RELATION`; persona: `swarm`.

### ZL-S32 authorization profiles are scope-bound

- Given an M0 simulated answer receipt allowed under profile `SIMULATED`, while a real-owner run selects `REAL_OWNER` from trusted host configuration and binds that profile in the semantics root, decision receipt, and accepted revision.
- When a caller substitutes the simulated receipt or requests a caller-selected downgrade during the real-owner run.
- Then the result is `REJECTED:AUTHORIZATION_PROFILE_MISMATCH` and the exact no-semantic-effect observation holds.
- Oracle: an independent host-config and receipt-binding checker compares the trusted profile at every scope and revision boundary.
- Mutant: `MUT-ZL07-PROFILE-DOWNGRADE; killer=replace REAL_OWNER with SIMULATED or a caller-selected profile and require the exact rejection`.
- Scope: `FINITE_RELATION`; persona: `human+swarm`.

## Review boundary

The catalog and this contract describe acceptance targets only. They do not
claim that the workbench, its oracles, its persistence shell, or its runtime
adapters exist. The codec example is an independent illustration of a missing
compatibility requirement; it does not report a current defect in the adapter.
The implementation must freeze typed rejection codes, canonical snapshots,
source-binding rules, and evidence labels before converting these cases into
executable tests.
