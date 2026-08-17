# ZenoDEX Typed Settlement Microkernel V2 Candidate

Status: `STRUCTURALLY_SPECIFIED_RESEARCH_ONLY`

Architecture selected: `false`

Production promotion: `false`

## Claim scope

This candidate closes a structural design question: how independently
versioned economic modules can share one global accounting, replay, release,
publication, and effect boundary without gaining durable write authority.

```text
ZenoLedger authenticated request
-> settlement kernel
-> route and release resolution
-> policy verification
-> governance authorization for governed control items
-> ordered module evaluations over root-bound views
-> central checked intent fold and derived value delta
-> global reconciliation
-> expected-head atomic ZenoLedger publication
-> committed outbox dispatch
```

Nine economic modules own only their local lifecycle semantics. The settlement
kernel owns the economic ledger and derives the authoritative pre/post delta.
ZenoLedger is the only durable writer. The outbox shell receives only committed
effect envelopes and submits acknowledgments as later commands.

## Structural contract

- Exact command coverage: 33 routes with one primary semantic owner each.
- Exact module surface: 20 economic and infrastructure components.
- Exact state surface: 13 domains with one semantic owner and one durable
  writer.
- Exact port surface: 25 bidirectional request/response contracts using closed
  V2 types and checker-owned assumption/guarantee atoms.
- Exact intent authority surface: 56 module/intent capability rows bind asset
  scope, account-role scope, authority profile, and mandatory settlement
  recheck. Route steps own their required and optional intents explicitly.
- Forty-six boundary types declare closed field names, field types, cardinalities,
  and units. The 33 economic command payload schemas remain explicitly
  `REQUIRED_NOT_SELECTED_G1`; domain-object and delta-entry internals remain
  implementation blockers.
- Every declared sum type has an exact discriminator and per-variant required
  and forbidden field set. ZRPF admission therefore requires a verified
  journal, direct execution forbids one, and native-backup mode requires both
  governance authorization and an equivalence receipt.
- Runtime dependencies are declared by typed port participation. Domain modules
  receive immutable root-bound views instead of reading another module's state.
- Batch order is command index first. Each command then uses route-DAG
  topological order, module-ID tie breaking, and intent index.
- Occurrences bind the promotion subject, profile, module registry, complete
  module release set, route, command, context, parent state, sender, nonce,
  command index, and writer epoch.
- The authoritative input sum is closed over 33 economic commands, three
  governed-control variants, and one ZRPF batch-proof variant. Release and
  policy changes use separate `Authorized*ControlRequestV2` ports that carry
  the opaque governance authorization value, and all accepted variants publish
  through `ZENO_LEDGER_SUBMIT_V2`.
- Tau fallback and rejoin can change only Tau connectivity mode. Tau value
  routes consume a policy-resolved `ResolvedTauRepresentationV2` and cannot
  mutate software releases or policy profiles.
- ZRPF roots enter through ZenoLedger, use a release-selected RISC0 verifier,
  bind exact `ZRPFRootJournalV2` bytes, recheck the current head, and share the
  direct publication capability. This remains a declared interface contract.
- Direct and ZRPF paths produce one `ExecutionAdmissionV2`. One canonical
  `ExecutionCommitmentsV2` carries parent, state, delta, effect, history,
  nullifier, outbox, release, policy, subject, and epoch commitments. The ZRPF
  journal embeds that type, and proof verification returns a typed
  `VerifiedZRPFJournalV2`. Checker-derived schema paths equate every declared
  journal, witness, proof, and commitment field before the writer recomputes
  one candidate root. Publication embeds the candidate once and adds finality.
- Tau representation binds integer scaling, rounding, dust, external network,
  ingress verifier, destination adapter, migration, recovery, and permanence
  roots. Tau-primary/native-backup operation requires a governed mode switch
  and a same-profile equivalence receipt. `VerifierExecutionProfileV2` binds
  the active mode and epoch into policy queries, backend receipts, and verified
  admissions; silent per-query fallback is closed.
- Protocol buy-and-burn has three ordered steps: finance authorizes eligible
  surplus, spot/LP proposes ZDEX acquisition, and finance authorizes the burn.
  Its route binds the finance, spot, and oracle releases.

## Formal evidence contract

The structural token checks are grade-2 evidence only. They do not establish
semantic implication.

Required ESSO lane:

```text
producer guarantee AND NOT consumer assumption
-> Z3 UNSAT
-> CVC5 UNSAT
-> identical canonical model bytes and solver agreement
```

`SAT`, `UNKNOWN`, timeout, or disagreement leaves the obligation open. ESSO
must also model bounded route composition, release/drain behavior, migration,
effect ancestry, and reject-no-commit.

Required Lean lane: global sequential-fold invariant preservation,
conservation/liability arithmetic, batch-fold preservation, and runtime
refinement. Both formal lanes are `REQUIRED_NOT_IMPLEMENTED` in this slice.

## Evidence and replay

```bash
python3 tools/render_production_readiness_architecture_candidate_v2.py --check
python3 tools/check_production_readiness_architecture_tournament_v1.py --json
python3 tools/check_production_readiness_architecture_candidate_v2.py --json
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q -p no:cacheprovider \
  tests/test_check_production_readiness_architecture_tournament_v1.py \
  tests/test_check_production_readiness_architecture_candidate_v2.py
```

The candidate checker owns the exact registries and keeps every evidence gate
unverified. The test suite includes the earlier self-attested-selection exploit
and 54 candidate mutants covering routing, authority, asset/account scope,
control atomicity, proof admission, port typing, ordering,
migration, verifier binding, effects, release control, and direct/guest parity.
The checker reads every pinned source into one immutable byte snapshot, parses
those same bytes, rejects symlinks, and rechecks the snapshot before returning.
It executes the contract bytes captured at startup and rejects any later
contract-source split. The already-running checker and Python interpreter form
an explicit trusted bootstrap premise. An external authenticated executable
identity receipt is required for any promotion use and remains absent.

## Nonclaims and residual risks

- No Rust transition, node, RISC0 guest, migration, verifier registry, or
  outbox adapter is implemented here.
- No economic parameter or unfinished profile policy is selected.
- Exact boundary field schemas do not close the still-unselected 33 command
  payload schemas, nested domain-object schemas, delta-entry schemas, or codec
  parity.
- Runtime code may still violate a declared access or port manifest until
  build-derived inventories and differential execution establish refinement.
- ESSO, Z3, CVC5, Lean, crash, CAS, destination-idempotency, no-bypass, and
  direct/ZRPF evidence remain open.
- The checker does not authenticate its own already-running executable bytes;
  `verifier_bootstrap.identity_status` remains
  `REQUIRED_EXTERNAL_AUTHENTICATED_RECEIPT`.

## Next frontier

Implement the closed Rust ABI and one thin vertical slice through router,
policy, one economic module, settlement fold, and ZenoLedger publication. In
parallel, create the source-pinned ESSO composition model and make dual-solver
agreement a deterministic evidence receipt. Architecture selection stays
closed until the authenticated evidence resolver derives gate grades from
replayable receipts.
