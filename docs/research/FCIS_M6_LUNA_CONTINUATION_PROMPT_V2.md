# Luna M6 Continuation Prompt V2

Continue the ZenoDEX FCIS M6 program from this exact functional baseline:

```text
repository: TheDarkLightX/ZenoDEX
branch: agent/fcis-m6-r05-r11-durable-retraction-20260731
implementation target: ecf26f987c3d6393501fec66ddfc3429fb8634c7
implementation tree: fdf154ac143a9f9a9e840fbbf49761190d138920
posture: RESEARCH_ONLY_EXECUTABLE_UNMOUNTED
```

Read these files completely before changing code:

```text
AGENTS.md and every closer overlay
docs/research/FCIS_M6_LUNA_TASK_GRAPH_V1.json
docs/research/FCIS_M6_LUNA_IMPLEMENTATION_TASKBOOK_V1.md
docs/research/FCIS_M6_LUNA_REPAIR_REPORT_20260731.md
docs/research/FCIS_M6_LUNA_NONCLAIMS_V1.md
```

## Execution rule

Select only tasks whose dependencies have exact completion receipts. Execute a
small reviewable slice. Preserve every task ID and emit the taskbook's required
evidence. All 105 production tasks start as `PLANNED`; the current reference
model is prerequisite evidence rather than proof that a production task is
complete.

Do not require private ESSO. The mandatory public bounded-model gate is:

```bash
python3 tools/check_fcis_durable_retraction_model.py --self-test
```

If private ESSO is available, record it as optional corroborating evidence. If
it is unavailable, continue with public gates and retain the nonclaim. Never
weaken a task's acceptance gate because a private tool is unavailable.

## Authority boundary

Do not reintroduce module tokens, caller-mintable grants, or accepting verifier
implementations in production source. Core authority-bearing operations must
freshly invoke a shell-selected verifier against the exact current subject.
The shell must select a pinned production adapter; untrusted API input must
never choose the adapter. Test-only accepting adapters must stay in tests and
must be named as test-only premises.

## Immediate next slice

Prioritize the earliest dependency-closed production slice from Waves E through
H:

1. preserve complete commit identity, sequence, authority epoch, command root,
   nonce identity, and expected pre-state root in the production schema;
2. implement the concrete expected-root CAS transaction with exact conflict and
   retry classifications;
3. add two-connection concurrency tests and deterministic fault injection;
4. prove canonical reopen rejects missing, surplus, duplicate, crossed, or
   misordered durable rows;
5. show recovery exposes exact PRE or exact POST;
6. keep the code unmounted until the corresponding no-bypass tasks pass.

For every behavior change, add the minimized failing witness first. Use
immutable exact values and deterministic functions in the core. Keep IO,
cryptographic verification, database transactions, and delivery in narrow
shell adapters. Report `PROVED`, `IMPLEMENTED`, `MOUNTED`, and `TESTED`
separately.

## Required completion report

```text
Result:
- Task IDs attempted:
- Task IDs completed:
- Changed:
- Invariant/authority impact:
- Exact commit and tree:
- Evidence and exact commands:
- Commands not run:
- Failed or blocked tasks:
- Residual risk:
- Explicit nonclaims:
- Next dependency-closed tasks:
```

Do not merge, deploy, mount, switch authority, or move value. Open a draft PR
only after the exact-head packet and all claimed focused gates pass.
