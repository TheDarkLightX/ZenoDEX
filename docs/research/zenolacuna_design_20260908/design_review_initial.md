# Initial independent design review

Subject: README v0.1, 2026-09-08. Scope: formal contract, question policy,
closure, and tool boundaries. This is advisory design review; no theorem or
implementation correctness has been established. Exclusive write ownership:
this file. Existing unrelated work was preserved.

Reviewed README SHA-256:
`4f4e2dd8f5d6fd684486cf79036306c2e613b90ff654eb56d41d5e7af726c271`.

## Required corrections before implementation

1. **Questions must descend to the semantic quotient.** Let `h1 ~ h2`, while
   `h3` denotes another relation. Define `q(h1)=0`, `q(h2)=q(h3)=1`.
   Choosing `h1` as class representative and receiving the faithful answer of
   `h2` discards the true class. Require total deterministic answers and
   `h ~ h' => answer(q,h)=answer(q,h')`, checked before scheduling. Reject a
   malformed question without changing interpretations, revision, or effects.
   Proposed negative test: `test_question_rejects_noncongruent_answers`.

2. **Unseparable continuations need an explicit DP value.** For three distinct
   classes, suppose every question distinguishes only `{a}` from `{b,c}`.
   One split exists, yet no finite identification strategy exists. Define
   `C(empty)=CONFLICT`, and `C(V)=infinity` when no complete strategy exists;
   propagate infinity through worst-case branches. A numeric optimum cannot be
   reported for the root. Specify that fixed Q, costs, and answer meanings are
   history-independent. Test `test_dp_propagates_unseparable_child` using a
   hand-enumerated decision-tree oracle.

3. **Nonvacuity needs protected applicability coverage.** Initially require
   successful behavior for `x=0` and `x=1`. A repair narrows A to `x=0` and
   preserves its positive witness. A remains satisfiable and all implications
   pass, but one promised behavior disappeared. Freeze each protected
   obligation's applicability independently of candidate A; check every such
   class retains its required witness. An authorized scope reduction must
   explicitly supersede the old obligation and cannot close it as satisfied.
   Test `test_assumption_strengthening_cannot_erase_required_context`.

4. **Allowed families need compositional semantics.** Contracts permitting
   complete traces `00` and `11` do not jointly authorize `01`. A pointwise
   union can introduce that trace. Specify complete-trace union, or a fixed
   per-execution interpretation choice encoded in state, and replay the resulting
   contract against K. Test `test_family_union_preserves_history_correlation`.

5. **The runtime arrow needs a declared coverage mechanism.** Finite V1/V2
   fixtures alone cannot establish correspondence for arbitrary decoder inputs,
   hidden state, or reachable histories. Require either complete enumeration of
   the declared runtime domain or a checked abstraction/simulation obligation.
   An unmatched runtime trace or omitted effect must invalidate closure and
   return `NEEDS_MODEL_REVISION`; sampled parity remains bounded evidence.
   Test `test_unmodeled_runtime_effect_blocks_closure`, observing the complete
   revision, history, and effect plan before and after rejection.

## High-return simplifications and retained boundaries

Use one canonical Boolean relation table as the M0 semantic representation.
Keep all original interpretation IDs alongside quotient classes; ranking may
change search order only. A single observed execution cannot certify equality
of nondeterministic allowed sets. Hidden predicates, pruning, changed O, and
new hypotheses must create an explicitly revised scope.

Use the exhaustive reference core without requiring native adapters for M0.
Tau is a candidate Boolean/temporal query backend under its supported subset;
ESSO is a candidate finite-transition refinement/invariant backend for M1.
Neither establishes human intent, runtime coverage, causal synthesis, or
crash/retry liveness automatically. Existing UNKNOWN boundaries are appropriate.

Evidence: manual finite counterexamples above; oracle grades 2 by decision
tables, with executable grade-3 oracles required in implementation. Style
classifier completed. No builds, proof jobs, solver calls, production gates,
or implementation tests were run. Filtering and DP remain theorem targets.
