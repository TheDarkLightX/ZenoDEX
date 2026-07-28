# FCIS M5-P4B4 review checklist

## Automatic NO-GO

- [ ] Exact ancestor is `99da842b6606e6f10ce8ab6b2c94c2d36f2e169f`.
- [ ] Every protected path is byte-identical to the ancestor.
- [ ] Mounted authority behavior is unchanged.
- [ ] The mixed validator remains the unchanged differential oracle.
- [ ] New exact source imports no legacy command, settlement, state, route, or
      snapshot module.
- [ ] New authority fields contain no `Any`, `object`, raw mapping, or raw list.
- [ ] No coercive admission, generic copy/freeze, mutable inheritance, seal
      flag, JSON reconstruction, or broad exception catch exists.
- [ ] All exact inputs are recursively revalidated before reads.
- [ ] Route binding is rederived from the original command.
- [ ] Direct result, rejection, and read-trace parity passes.
- [ ] Required resource bounds are source-owned and tested.
- [ ] All structural mutants are killed by the intended rule.
- [ ] Four pre-mount profiles pass.
- [ ] `final-mount` remains exactly 64 violations.

Any unchecked item above blocks completion.

## Architecture grade

Score 0 to 5 for each:

| Area | Score | Evidence |
| --- | ---: | --- |
| Exact value closure | | |
| Single admission and recursive revalidation | | |
| Domain-machine composition | | |
| Rejection precedence | | |
| Route command binding | | |
| Read-trace fidelity | | |
| Resource determinism | | |
| Differential completeness | | |
| Mechanism-conformance checker | | |
| Mount isolation and evidence honesty | | |

Grade:

```text
A   46-50 and no automatic NO-GO
B   40-45 and no automatic NO-GO
C   34-39 and no automatic NO-GO
NO-GO otherwise
```

## Required code-reading attacks

- [ ] Trace every public exact input to the first state read.
- [ ] Trace every candidate field to one replay state and one patch derivation.
- [ ] Trace every rejection path to absence of candidate authority.
- [ ] Confirm all intent and fill variants are exhaustive.
- [ ] Confirm no default masks a missing exact field.
- [ ] Confirm no result/read comparison normalizes either side.
- [ ] Confirm local scratch does not enter committed read evidence.
- [ ] Confirm accepted replay state equals final atomic spot application.
- [ ] Confirm checker tests recompute outer hashes before semantic mutations.
- [ ] Confirm private sinks have exact importer allowlists.

## Review outcome

Use one:

```text
M5_P4B4_COMPLETE_UNMOUNTED
M5_P4B4_BLOCKED_PARITY
M5_P4B4_BLOCKED_STRUCTURE
M5_P4B4_BLOCKED_RESOURCE_BOUND
```

No outcome authorizes P4B5 or a mounted switch without a new reviewed
checkpoint.
