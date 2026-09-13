# ZenoDEX attack-surface reduction plan

Approved scope: implement the September 13 security recommendations within
[whole-program V3](ZENODEX_COMPLETION_PLAN.md). This work does not replace V3,
change economic policy, authorize live activation, or reduce its required
103 capabilities, four routes and four exclusions. A disabled required workflow
remains incomplete. The goal is a reviewable isolated release candidate with
fewer independent authority paths and explicit remaining deployment premises.

## Subject and safety contract

Starting subject: `be7dcd00639b08996d8c282d1360b72d0509d732`, branch
`codex/whole-program-v3-20260904`. Preserve unrelated dirty files and historical
wire/receipt verification. The existing
[authority discovery](research/ZENODEX_WHOLE_PROGRAM_V3_AUTHORITY_DISCOVERY.md),
[acceptance index](research/ZENODEX_V3_ACCEPTANCE.json),
[continuity contract](ZENODEX_SESSION_CONTINUITY.md), and
[productivity account](research/ZENODEX_V3_PRODUCTIVITY.md) remain the trackers.
Do not create a second scoring system or count documentation as lane delivery.

Every authoritative value effect must descend from an authorized command,
the exact valid economic transition, the current qualified finality context,
and one committed occurrence. Delivery must retain that ancestry and enforce
destination-specific idempotency. An attacker must not obtain an alternative
balance writer by compromising a proposer, prover, observer or transport.

This target is conditional on the selected cryptography, finality fault model,
independent enforcement and destination assumptions. A Python private method,
caller-created witness, local file lock, subprocess verifier or source inventory
does not establish protection from a compromised publisher or host.

Preserve all required successful and rejection outcomes, ownership, canonical
bytes, rounding, replay, cancellation, withdrawal, recovery and terminal paths.
Precommit rejection adds no economic state, history, replay consumption or
outbox effect. Committed retry and indeterminate client knowledge are distinct.

## Execution and acceptance

Statuses describe this exact plan's exit conditions. Existing narrower evidence
is reusable; it does not close a wider condition. Each row remains OPEN until
its executable acceptance and independent review are recorded below.

| ID / V3 owner | Dependencies | Implementation and owned boundary | Exit condition |
| --- | --- | --- | --- |
| AS01 / W01,W11 | None | Extend the existing authority discovery from actual launchers, writers, signing and effect destinations. Astra owns integration; Daybreak reviews authority bypasses. | Every deployed value writer and upgrade path has an enforcing consumer and adversarial bypass test; unknown or new writers block qualification. A static inventory alone is insufficient. |
| AS02 / W03,W09,W10 | Fixed margin V2 contract | Complete the existing Rust margin guest/host path and reuse the measured verifier protocol. Preserve the exact two-root journal. | Rebuilt guest identity and genuine receipts qualify through the current-store publisher; fake, foreign-image/journal/context, malformed and unavailable outcomes reject before effects. |
| AS03 / W06,W11 | AS01,AS02 | Reuse one economic acceptance relation and the existing atomic store. Independent ledger acceptance consumes untrusted proposals; proposer/prover/observer ports have no independent write or signing power. | Compromising a proposer cannot produce accepted unauthorized state under the declared finality fault model. Authorization, complete predecessor, effect and current-authority checks are enforced outside its trust domain. |
| AS04 / W08,W11 | AS03 | Connect committed effects to the existing destination/delivery interfaces; retain complete state, replay, history, receipt and required outbox atomically. | Delivery requires finalized committed ancestry; duplicate, substituted, stale and conflicting deliveries reject or return the original outcome. Crash/retry histories resolve to complete PRE, complete POST, or fail-closed recovery. |
| AS05 / W02,W11 | AS01,AS03 | Version-pin finality adapters, upgrades and authority epochs. Reuse existing migration/fencing contracts; do not invent a second consensus protocol. | Transitions preserve finalized history, reject dual authority and exclude retired writers after restart. Missing adapter data cannot silently select a conflicting chain. |
| AS06 / W04,W07,W09 | Lane contracts | Remove redundant facts or interpretation paths only with preservation evidence; close canonical parsing, checked arithmetic, complete claim ownership and next-state resource closure. | Each accepted state retains its required exit/terminal paths; unauthorized conserving transfers, omitted/duplicated claims, overflow and unencodable successors have retained negative evidence. Python/Rust and model/runtime relations retain their bounds. |
| AS07 / W05,W11,W13 | Relevant mounted path | Restrict verifier/prover/observer process capabilities, dependencies, data exposure and resources. Keep SHADOW diagnostics separate. | Malformed/oversized input, output flood, timeout, failed observation and interrupted execution cannot alter economic commitments or retain unauthorized effects. Resource limits preserve required recovery capacity. |
| AS08 / W09,W12 | AS01-AS07 | Replay the selected release's proofs, runtime cases and deployment checks; conduct independent security and simplification review. | One exact release subject meets every applicable condition above with explicit fault/cryptographic/destination assumptions. No remaining bypass, unknown writer or missing required workflow is labeled qualified. |

First integrated acceptance is AS02: qualify the real margin V2 receipt through
the existing joint publisher. AS01 investigation and concrete AS07 repairs may
run alongside it. Finish a confirmed counterexample repair before creating
adjacent infrastructure. Bounded workers own disjoint files; Astra owns shared
contracts, final integration and review of their evidence.

## Implementation rules

- Keep economic decisions pure: explicit immutable pre-state, typed command,
  authenticated evidence values, typed rejection or a complete candidate plan.
- Give each invariant a named owner. Compose shared assets and claims at the
  existing global boundary; do not let lane-local acceptance independently
  publish partial economics.
- Snapshot before external execution. Check exact types before reading foreign
  object attributes. Execute the measured verifier bytes with bounded framing,
  output and lifetime. Missing evidence or unsupported solver outcomes reject.
- Revalidate current authority and complete predecessor at the single commit
  point. No public generic commit callback or caller-selected admission profile.
- Treat finality adapters and proof backends as versioned contracts whose
  implementation and assumptions must be qualified. Availability alone grants
  no authority. Keep old verification separate from new publication permission.
- Keep research, synthesis, UI, optimizers and diagnostics outside acceptance
  wherever complete checking can replace trust. No runtime dependency on an LLM.
- Prefer deletion or derivation over another wrapper, registry or stored field.
  Preserve independent checks across trust boundaries. A shorter implementation
  is accepted only with preserved success, error, byte, effect and recovery
  contracts; a source-shape score is advisory.

## Evidence and effectiveness

Use the smallest existing evidence lane that answers the obligation: Lean for
general preservation/refinement, ESSO/SMT for declared state-machine histories,
Kani for bounded actual Rust, independent differential references for language
boundaries, genuine RISC0 receipts for exact guest execution, and fault-injected
store/delivery tests for shell outcomes. Tau claims require a pinned supported
runtime. No new universal security checker is part of this plan.

Each repair first retains a failing counterexample and a successful neighbor.
Exercise relevant authorization, boundary, recovery and terminal behavior.
Identify the semantic mutant the evidence detects. Translation/model evidence
must name omitted state, bounds and trusted steps; a model proof does not prove
that the deployed authority graph is complete.

Record baseline/candidate source identities, commands, results, independent
review, categorized line changes, affected existing score rows and the next
unmet acceptance in the existing productivity/assessment files. Record failed
agent attempts and unscored support work. Do not credit the same delivery twice.

Track removed unmediated writers, eliminated authority/configuration paths,
reduced privileged dependencies, preserved required exits and discharged attack
cases. Targets include zero *unmediated* value writers and zero accepting
ambiguous authority contexts. Counts do not prove deployment completeness or an
absolute minimum attack surface. Overall and formal scores change only after
evidence review under the existing fixed rubric.

## Initial evidence and remaining resources

The starting isolated margin publisher has retained same-store lifecycle,
concurrency, crash, retry, capacity and hostile-object tests. Its
[September 13 evidence](../tests/evidence/perps_margin_publication_v2_20260913.json)
uses protocol fixtures for verifier exchanges; it does not qualify a new genuine
margin receipt, independent finality or a live effect destination. All AS rows
are initially OPEN. Last reviewed planning estimates are V3 24.268%, formal core
21.440%, with 0/12 value-safety gates closed; these are not a new rescore.

Runpod is unavailable and initial local free space is about 3.3 GiB. Inspect
existing artifacts before builds; avoid heavy local proof builds and new large
worktrees. Preserve live work and unique receipts during any authorized cleanup.
If exact-image proving needs compute, record the precise command/resource need
and continue independent authorized work. Live deployment, balance migration
and authority activation remain outside this isolated integration.
