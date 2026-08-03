# FCIS M6 PR #509 bounded-assurance repair v2

## Exact source identity

```text
reviewed PR head:
2fe4ee7e142d842554fe8c5937c786b893224ac0

reviewed source archive SHA-256:
12340f10639ffc00ceb4fedf029251579094d65b5e0101b8799ae3d0d414d842
```

This repair was prepared in an isolated copy of the exact PR source. It does not include a remote commit, merge, mount, deployment, authority switch, or value movement.

## Result

```text
READY_FOR_INDEPENDENT_REVIEW_AS_UNMOUNTED_BOUNDED_REPAIR
```

The repair closes the packet defects found during review:

1. Fresh bounded replay now has one canonical compact byte representation.
2. The default checker compares fresh replay with committed evidence instead of rewriting the evidence tree.
3. A deterministic closed source-manifest builder replaces hand-maintained hashes.
4. A dedicated hosted public workflow runs the bounded gate while preserving the missing private ESSO receipt as an explicit Grade F gap.
5. The matrix now closes and checks its runtime-projection obligation registry while labeling all 32 projections `DECLARED_ONLY_NO_RUNTIME_IMPLEMENTATION`.
6. ZenoLedger is fixed as the canonical economic ledger. Tau is an optional authenticated integration and SQLite remains an unmounted conformance adapter.
7. A thirteenth bounded model covers Tau unavailability, censorship, ZenoLedger-native continuity, authenticated checkpoint rejoin, and forbidden Tau-driven ledger rewrites.

## Repaired bounded evidence

```text
models:                 13
formal actions:         104
formal invariants:      76
reachable states:       1031
enabled transitions:    7496
mutants killed:         83 / 83
projection obligations: 32 declared, 0 implemented
source manifest:        26 entries
focused tests:          5 passed
```

The ZenoLedger/Tau model contributes:

```text
reachable states: 49
transitions:      160
invariants:       7
mutants killed:   7 / 7
```

All four ZenoLedger publication cases are reachable while Tau is available, unavailable, censoring, or rejoining. `tau_rewrite_ledger_head` has zero enabled transitions. Tau-dependent authority is removed during disruption and can return only after authentication and anchoring of the current ZenoLedger checkpoint.

## Executed gates

```text
ruff check: PASS
ruff format --check: PASS
py_compile: PASS
focused mypy: PASS
source manifest builder --check: PASS
sha256sum -c source manifest: PASS
bounded independent replay: PASS
formal/runtime matrix: MATCH
pytest focused packet tests: 5 passed
public bounded assurance gate: PASS
FCIS_REQUIRE_ESSO=1 with missing ESSO: expected fail-closed exit 2
```

## Open assurance obligations

The following remain open and are not promoted by this repair:

- pinned ESSO Z3/CVC5 dual-solver receipt over all thirteen models;
- a compiled Lean or Tau composition theorem that connects the independent lanes without hiding inventory, cryptography, ZenoLedger durability, or Tau checkpoint authentication as axioms;
- total canonical runtime-to-formal projection implementations;
- executable BDD step definitions against mounted ZenoLedger entrypoints;
- concrete ZenoLedger crash, concurrency, finality, reopen, and rejoin refinement;
- complete mounted no-bypass inventory and credential audit;
- same-promotion-subject Grade F, Grade R, and Grade M evidence.

The bounded models remain specification and falsification evidence. They do not establish M6 completion or authorize production value movement.
