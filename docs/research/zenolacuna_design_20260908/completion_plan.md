# ZenoLacuna first-release finish line

Date: 2026-09-09. Status: implementation and local qualification complete for
the supported first release. See [release_evidence.md](release_evidence.md)
for the frozen subject, native replay, benchmark and remaining claim limits.
This closes the work recorded in the historical [coverage inventory](implementation_coverage.md)
and retains the original [M0/M1 scope and obligations](README.md).

## Definition of finished

A developer and their swarm can take a real supported finite ZenoDEX adapter
change through this repeatable workflow:

```text
load source and requirements -> discover and replay a gap -> owner decision
-> new requirement revision -> proposed code repair -> independent verification
-> saved evidence -> clean restart and independent replay
```

The tool must also handle rejection, disagreement, cancellation, rollback,
stale work and interrupted persistence without changing accepted requirements
or promoting incomplete evidence. A user should not need to write additional
orchestration Python to complete the supported workflow through the CLI.

The first release supports explicitly declared finite relations and the
bounded real adapter migration profile. General Python verification, unlimited
histories, arbitrary human-intent completeness and Tau Net deployment remain
later capabilities. A successful first release does not complete that wider
vision or confer production settlement authority.

## Five completed work packages

| Package | Deliverable | Exit evidence |
| --- | --- | --- |
| 1. Complete the developer/swarm workflow | Project/task input, witness admission, actionable question and defect reports, data-only agent proposals, and a repeatable command sequence through repair. Known adapter selection stays explicit. | A fresh CLI run on real repository source completes the supported happy and rejection paths without private helper scripts; false witnesses, unsupported source and out-of-model observations reject with the declared results. |
| 2. Implement real decisions and specification revision | A trusted host approval or scoped-delegation boundary; owner-controlled revisions of assumptions, observations, protected requirements and interpretations. Distinguish preserving an existing contract from explicitly changing it. | Unauthorized actors, profile downgrade, stale answers, replayed decisions and silent removal of protected behavior all fail with no accepted-state change. Approved revisions preserve provenance and invalidate dependent obsolete evidence. |
| 3. Finish runtime evidence and replay | Persist and independently recheck runtime evidence bound to the exact source, specification, approval, candidate, checker and supported adapter. Mount required Tau/ESSO checks in that workflow. | A clean process replays the saved result; tampered or stale bindings, incomplete concrete domains, missing observations, solver failure and incomplete graph evidence cannot produce completion. Runtime correspondence is checked, not inferred from matching hashes. |
| 4. Complete real migration and failure recovery | The actual finite old/new adapter profile with explicit schema and authentication/freshness observations; queued messages, retries, cancellation and rollback. Complete the persistence failure histories. | Runtime/model parity across the declared domain and complete finite graph; old-reader support, consumer-first migration and recovery paths tested; partial writes, torn pointers, failed sync, duplicate workers and cancellation/restart cannot revive obsolete work. |
| 5. Qualify and ship | A usable package and documented CLI, pinned/explicit external tool setup, independent review, source-bound benchmarks and clean-checkout replay. | All first-release acceptance cases implemented and checked; no unresolved correctness or authority blocker, no false completion on the declared hostile corpus, and an honest comparison with ordinary checking. Commit/push only the verified completed release slice. |

Packages 1 and 2 define the interfaces and decision semantics that package 3
must bind. Recovery tests and independent migration oracles can be developed
alongside them. Package 5 evaluates the combined frozen candidate.

The architecture/integration owner retains approval semantics, revision rules,
runtime correspondence and final acceptance. Bounded CLI, serialization,
packaging and test implementation can be delegated after their interfaces and
rejection contracts are explicit. An independent reviewer checks the critical
paths and the combined candidate; model opinions do not close obligations.

## Acceptance discipline

The existing 32 scenarios remain the acceptance inventory. The completed
[release ledger](release_coverage.md) maps them to the executed supported
workflow, including the independently reviewed S22/S29/S32 amendments. The
2026-09-08 prototype checkpoint had 14 `TESTED`, 16 `PARTIAL`, 2 `UNMOUNTED`
and 142 passing focused tests. That historical count did not establish the
signed workflow. The final isolated release run has 277 passing tests and
separate required Tau/ESSO CLI qualification.

Resolve each scenario's remaining obligation with executable evidence. Where
implementation and planned public result codes differ, repair the implementation
or record and independently review an explicit contract change. Do not silently
rename a gap as passing or delete a difficult case to meet the finish line.

Every advertised guarantee must name its domain, assumptions, observations,
protected requirements, runtime correspondence and evidence grade. Incomplete
search remains inconclusive. The twelve current Lean theorems cover abstract
finite filtering and identifiability; additional proof or independently checked
evidence is needed for any stronger advertised claim.

Measure recovered and missed omissions, spurious witnesses, false completion,
owner question burden, end-to-end runtime and model-call costs on the same
frozen cases. Compare against existing tests/workbench and ordinary finite or
SMT checking. The current tiny example does not establish a Tau speed advantage.

The release work is primarily integration, lifecycle implementation and
adversarial verification. The greatest uncertainty is the trusted approval
boundary and the connection between real adapter histories and the finite
model. No calendar or compute estimate has been measured for these packages.

The owner decision/revision contract, negative cases, persisted runtime replay,
real migration and crash recovery are implemented and qualified. The existing
demo remains regression material. The next research candidate in
[implementation_lessons.md](implementation_lessons.md) concerns checked
observation synthesis; it is not part of this release's completed claim.
