# ZenoLacuna implementation packets

**Status:** candidate implementation handoff, 2026-09-08.
The [design contract](README.md) is normative for these packets. Assignment here
does not mean the engine has been implemented or that a worker is running.

## Who implements what

| Work | Owner and reasoning | Why this assignment | Required independent check |
| --- | --- | --- | --- |
| Formal semantics, protected applicability, complete-trace interpretation | Astra, high; use max for unresolved proof obstacles | An apparently small error can make the tool certify a hole | Separate theorem/decision-table author and critical review |
| Finite reference evaluator, question quotient and DP, closure constructor | Astra, high | These functions define what acceptance means | Exhaustive small oracles, mutation controls, Lean theorem targets |
| Frozen JSON decoding, CLI rendering, fixture loaders, deterministic report formatting | Luna Max after interfaces are frozen | Work is bounded by exact input/output cases | Astra reviews boundary/error semantics and integration |
| Tau/ESSO process adapters and real migration harness | Terra Max, with Astra specifying semantics and reviewing integration | Several known modules and external failure modes must agree | Fault injection, source-bound replay, runtime/model parity |
| BDD scenario implementation and exact fixtures | Luna Max | Precise scenarios can be implemented efficiently | An independent reviewer owns expected tables and held-out mutants |
| Critical independent review and alternative formalization | Available Opus 5 at maximum exposed reasoning, otherwise fresh Astra high | A separately reasoned interpretation may expose shared assumptions | Deterministic evidence remains mandatory regardless of model |
| Final integration and evidence assessment | Astra | Includes ambiguity, scope, authority, and cross-module behavior | Re-run the combined frozen candidate and independent replay |

This session exposes Astra, Luna, and Terra settings. It does not expose an
Opus 5 model through the available agent API. There is no claim that Opus was
called, nor a fabricated Opus model ID. Opus is optional; its absence does not
block the available independent review. Routing is a risk-based engineering
decision, not a measured ranking of model accuracy, speed, or price.

Luna may implement a high-impact boundary only when Astra has frozen its exact
acceptance and rejection contract. A new semantic question returns to Astra;
the worker does not invent policy to finish its packet. Use exclusive file
ownership and fresh context. Limit concurrency to the active harness capacity.

## ATDD sequence

1. The user-story owner and reviewer approve the externally visible outcome
   and protected applicability, with human/agent decision ownership explicit.
2. A reviewer authors an independent finite table or model for the obligation.
3. Luna implements its readable pytest Given/When/Then scenario. The test must
   fail because the required behavior is absent or wrong, not merely because
   a module cannot be imported. A minimal interface can raise a typed
   `NOT_IMPLEMENTED` result while the behavioral acceptance gate stays red.
4. The assigned owner implements the smallest behavior satisfying that contract.
5. Astra checks the diff and runs the independent oracle, boundary cases, and
   a named semantic mutant. A test that only mirrors the implementation cannot
   close the obligation.
6. Final replay combines the owned modules on one frozen source snapshot.
   Only then may an implemented obligation change from PLANNED to its actual
   evidence status. A green catalog/schema check leaves scenario status PLANNED.

BDD supplies the shared behavior vocabulary. ESSO, exhaustive checking, solver
replay, and proofs supply additional evidence according to the failure shape.
No new Cucumber framework is required. The [scenario catalog](scenarios.json)
is development material; hidden acceptance cases are maintained separately by
the reviewer, with expected answers withheld from the implementer.

## Packet A: semantics before parallel implementation

**Owner:** Astra high. **Reviewer:** fresh Astra high or available Opus 5.
**Proposed files:** `src/zenolacuna/model.py`, `relations.py`, `check.py`.
**Prerequisite:** resolve every consequential ambiguity in the relevant design
slice through existing context or its authorized owner. Unresolved decisions
must remain explicit and cannot be treated as approval.

Implement only the finite relational profile first. Define immutable owned
types, closed variants, exact decode boundaries, finite allowed relations,
protected applicability predicates, and source-independent reference semantics.
Represent infinity/unseparability by a tagged value. Keep side effects out.
Pin both the trusted observation projection and the complete concrete input
domain for every claimed exhaustive check.

Before discarding a distinction through O, establish that every protected
requirement is preserved by that projection. If two raw states have the same
observation but different K verdicts, retain the distinction or report an
inadequate model. Equality of projected behavior alone cannot justify that
quotient. Include this check in the simulation or finite enumeration oracle.

Acceptance requires ZL-01, ZL-02, ZL-04, ZL-06, and the finite portion of ZL-08.
Include the reviewed counterexamples in `design_review_initial.md`. Draft the
closure theorem statement before constructing a verified-result type. The
constructor remains private to the checker, and forged JSON cannot instantiate
it. A persisted verified result is revalidated on reload.

**Exit:** approved core interface plus independent finite evaluator and negative
controls. No proposed UI or tool adapter may change these semantics.

## Packet B: question policy

**Owner:** Astra high. **Proposed file:** `src/zenolacuna/questions.py`.
**Prerequisite:** Packet A's interpretation and relation types are frozen.

Check totality and quotient congruence of questions. Implement exact minimax DP
for <=12 semantic classes and <=32 questions, with explicit work limits,
positive integer costs, stable tie-breaks, and infinity propagation. Preserve
the distinction between a useful first split and a policy that can finish all
branches. An answer file has no intrinsic authority.

The independent oracle uses a separate exhaustive decision-tree enumerator on
small families, for example <=5 classes and <=6 questions. Its representation
and recursion must not call the production DP. Compare cost, reachable leaves,
and survivor sets; tie-break correctness has its own exact fixtures.

Proof targets: faithful filtering, class-decrease termination under separating
answers, and Bellman optimality over the declared question language. These do
not assert that the true intended requirement is present in H. If a larger
heuristic is added, it must retain all interpretations and clearly report its
own optimality status.

**Exit:** ZL-03 and ZL-09 pass their independent oracles; reviewed proof statements
and actual proof status are recorded separately.

## Packet C: bounded shell and CLI

**Owner:** Luna Max for codec/rendering; Terra Max for persistence and process
integration. **Acceptance owner:** Astra.
**Proposed files:** `codec.py`, `shell.py`, and `tools/zenolacuna.py`.
**Prerequisite:** A/B interfaces and exact error/result schema are frozen.

Planned commands, not currently installed:

```text
zenolacuna describe
zenolacuna analyze --task task.json --out run-directory
zenolacuna answer --run run-directory --decision decision.json
zenolacuna assess-repair --run run-directory --candidate candidate.json
zenolacuna replay --run run-directory
zenolacuna status --run run-directory
zenolacuna cancel --run run-directory
```

Every command supports stable JSON. `describe` derives capabilities from the
same parser and typed variant registry as execution. A strict decoder rejects
duplicates, unknown fields, bad scalar types, excess sizes, and invalid variants.
Finite relations use canonical sorted encodings. Diagnostic rendering cannot
change a decision or suppress an unresolved obligation.

Decisions bind parent revision, question, witness, scope, and the authenticated
local owner or an existing delegated policy. The shell checks authority; a JSON
field saying `approved: true` has none. M0 uses an explicitly simulated decision
oracle and cannot claim human authorization. A real deployment must receive
decision authority from a trusted host approval port or a credential boundary
the proposal agents cannot forge. A shared OS user and a writable answer file
do not distinguish a human from their agents. If the configured host cannot
establish this boundary, retain `NEEDS_DECISION`; do not infer consent from a
filesystem artifact. Existing delegated policy binds that policy's exact scope
and version. The implementation and its tests must declare which authorization
profile they exercise.

Bind the authorization profile into the frozen scope's semantics root, each
decision receipt, and the accepted revision. The trusted host configuration
selects that profile; a proposal or answer payload cannot downgrade it. A run
requiring real owner authorization rejects simulated receipts with no semantic
effect. A locally callable endpoint alone does not establish the trusted-host
boundary. Test both receipt substitution and attempted profile downgrade.

Same-revision replay is idempotent; a
conflicting duplicate rejects. Use compare-and-swap against the expected parent
revision and atomic record/pointer updates. Rejection leaves semantic state,
accepted history, effects, and current pointer unchanged; a separate diagnostic
log may record the failure. Cancellation preserves evidence and requires a new
explicit lifecycle transition to resume. Restart discards no complete record
and never promotes an incomplete one.

Acceptance covers ZL-07 and ZL-10, including response loss, stale answers,
interrupted persistence, corrupt records, unauthorized commands, and repair
after a typed rejection. Public error codes and their precedence must be frozen
before the worker starts; do not infer them from exception messages.

## Packet D: Tau, ESSO, and the migration adapter

**Owner:** Terra Max. **Architecture/reviewer:** Astra.
**Proposed files:** narrow `src/zenolacuna/ports/` modules and
`tests/integration/test_zenolacuna_signal_migration.py`.
**Prerequisite:** the baseline relational loop is already independently checked.

Reuse Tau composition/workbench APIs for the supported finite fragment. Specify
each query's input semantics, output decoder, and independent replay relation.
Process nonzero exits, timeouts, residual quantifiers, malformed output, and
source drift must be distinguishable inconclusive or rejected results. A
logically positive-looking output after a failed process cannot pass.

For ESSO, start from the installed recommender:

```bash
python3 -m ESSO guide --input <finite-model.yaml> --goal verify --profile audit
```

This is a future command template; the model does not yet exist. Follow the
selected profile's validation/refinement commands and retain their artifacts.
Freeze state variables, action parameters, observables, alpha map, and bounds.
Use CGS only to synthesize inside an approved hole grammar. Never let synthesis
silently weaken protected assumptions or delete a required successful behavior.

The actual AutoTrader migration harness covers known V1/V2 fixtures, their
guard/rejection semantics, and queued version interactions within the declared
finite state machine. One-step ESSO refinement is only one obligation; history
properties require complete graph or bounded-history evidence as labeled.

**Exit:** each backend matches the independent finite oracle; real runtime
fixtures and exact rejection/effect observations agree with their model; no
broader runtime or liveness claim is inferred from fixture coverage.

## Packet E: hostile acceptance and review

**Owner:** independent Astra high or available Opus 5, plus deterministic tools.
**Forbidden:** changing the normative contract, expected vectors, or hidden
answers to make a candidate pass.

Build held-out omission combinations and representation mutants after the
development corpus is frozen. Try quotient-inconsistent answers, narrowed
applicability, noncausal Tau witnesses, selected-fixture completeness, missing
queued state, source/report substitution, and history correlations lost through
union. Independently replay each witness against the original source profile.
Document survivors and UNKNOWN results as open obligations.

Compare the same frozen tasks with ordinary exhaustive/SMT checking and fixed
questions. Do not promote the Tau/LLM lane for overhead alone: it must recover a
new validated omission, reduce verified question cost, or provide a measured
end-to-end benefit while preserving all hard gates. No numerical speedup or
question-reduction threshold has been asserted as achieved.

## Gates and handoff

Future implementation commands must be instantiated for the owned files and
confirmed against the repository's actual configuration:

```text
Ruff and mypy on the changed package and tests
pytest on the selected acceptance, property, and integration cases
independent small-state relation and decision-tree oracle
named mutation controls and stateful restart/cancellation histories
native Tau replay for the exact supported profile
ESSO profile checks for the actual finite transition model
Lean build for the selected theorem targets when proofs are implemented
final combined replay on a frozen isolated candidate
```

A checker conflict stops promotion and is investigated. Missing proof or backend
support stays visible. Documentation and a scenario file cannot satisfy an
implementation gate. The next concrete implementation is Packet A, followed by
Packet B; C and the development scenario harness can then proceed in parallel
against frozen interfaces. D follows the deterministic baseline. E overlaps
critical design and reviews the final candidate independently.
