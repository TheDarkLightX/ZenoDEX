# Tau policy values: ZenoDEX utility assessment

Status: research design, bounded replay and an offline reporter-capacity preflight.
Baseline repository subject: `8a99c42344de742ecceb4459711170563aa3784f`.
The preflight is implemented at `2863bde5ff100b2bd1aa091706d30af805dce3f1`;
it grants no economic or publication authority.

Source: [values_without_places.tau](https://github.com/taumorrow/tau-lang-demos/blob/3c9829afe45aeca81ec23dd379e0d9b9d1d71aba/values_without_places.tau),
SHA-256 `99d1838235b91f8beaecdc7e1662d47b5ee07be5ada6bac800b6f1003a80febe`.
The source was inspected; its Tau execution was not replayed in this assessment.
Here, values denote logical specifications. Financial quantities and transaction
occurrences require their existing accounting and provenance contracts.

## Utility and existing implementation

| Priority | Application | Assessment and existing seam |
|---|---|---|
| 1 | Governance upgrade preflight | High potential utility: detect newly permitted unsafe behavior and removed required permissions. `autonomous_governance_policy_pin.py` already checks exact policy identity, lineage, quorum and timelock; its rotation path does not compare old/new behavior sets. A semantic check would be additional evidence. |
| 2 | Assurance-preserving simplification | High utility for bounded predicates: compare all observable outputs before removing redundant rules. `experiments/tau_economic_qualification_v1/conservation_equivalence.py` already implements this for one transfer guard. Reuse that workflow. |
| 3 | Reviewable policy deltas | Moderate utility: show concrete witnesses to added/removed permissions. `experiments/tau_adt/tau_experiments/exp6_audit_diff_table.tau` already explores the algebra; its temporal-encoding limitations must be retained. |
| 4 | Ledger replacement or transaction throughput | No demonstrated benefit here. This research does not discharge custody completeness, receipt verification, publication, recovery or no-bypass obligations. |

The existing [oracle query-policy checker](../../tools/zenodex_oracle_query_policy.py)
already rejects weaker freshness/deviation bounds, weaker evidence/source/reporter
requirements, schema changes, broken lineage and incorrect consumer bindings.
Keep these direct checks for scalar revisions. A generic solver is useful when
relationships become more expressive than the existing numeric comparisons.

The new `preflight TRACE CONTEXT` subcommand checks one additional necessary
condition: a candidate's reporter quorum cannot exceed the number of supplied
eligible reporters. The context has exactly `schema`, `query_id`,
`current_policy_id`, `candidate_policy_id` and `eligible_reporter_ids` fields.
Its schema is `zenodex.oracle.query_policy_preflight_context.v1`; IDs use
canonical `sha256:` values, and the reporter list must be sorted and unique.
Current and candidate identify the last two published policies in the validated
trace. `sample_preflight_context` provides a matching example alongside the
existing sample trace. Run:

```sh
python3 tools/zenodex_oracle_query_policy.py preflight trace.json context.json
```

Trace rejection precedes context loading. Both preflight inputs reject duplicate
JSON keys and use bounded reads. The context's 65,536-byte and 64-reporter
ceilings are tool limits: exhaustion is inconclusive, not an economic rule
against larger registries. Exit codes are 0 for passing this necessary check,
2 for rejection, and 3 for inconclusive input or bounds. The existing `verify`
command retains its prior behavior. The context is an unauthenticated research
premise; success establishes neither source quorum, actual availability,
liveness, preserved withdrawal rights nor governance authority. This prototype
does not execute Tau. See the [sprint evidence](ZENODEX_FABLE_SPRINT_20260912.md).

The autonomous trajectory's `_validate_safety_envelope` checks declared observation
controls such as pause, freshness, divergence, volatility, cooldown and liquidity.
That function does not encode protected withdrawal rights or the complete economic
transition relation. The proposed contract below must not be inferred from its name.

## Proposed semantic contract

Fix an explicit input domain and interpretation. For admission analysis, a behavior
is a state/command case, including the ownership, amounts, versions and preconditions
needed for the obligation. Let `R` be required permissions, `S` the maximum permitted
behavior set, and `P` the proposed policy's admitted cases. First establish `R <= S`.

```text
Acceptable policy:       R <= P <= S
Unsafe permissions:     P & S'
Lost required rights:   R & P'
Added versus old O:     P & O'
Removed versus old O:   O & P'
```

Each offending set must be empty. A witness gives a concrete case for review and
regression evidence. Required permissions come from approved lane contracts with
their preconditions; an empty or arbitrarily weakened `R` cannot establish workflow
preservation. Unknown semantics or an inconclusive checker leave the obligation open.

Example: Alice has a valid, authorized withdrawal under the pinned lane contract.
Mallory proposes a policy that still permits swaps but blocks that withdrawal.
The proposal is nonempty and can be a tightening of the old policy. Both tests pass,
yet `R & P'` exposes the lost permission. A proposal admitting an unauthorized debit
is exposed by `P & S'`, even if the debit conserves total token supply.

For this Boolean admission model, a repair suggestion has a simple construction:

```text
Suggested(P) = R | (P & S), provided R <= S
```

It includes `R`, is contained in `S`, is idempotent, and preserves any proposal
already within those bounds. These follow directly from Boolean order laws. This
is established algebra, not a new economic optimization theorem. A suggestion has
different content from the original proposal and must receive its own exact-content
review and authorization. Never silently repair a signed or committed policy.

Admission permission does not prove eventual execution. Withdrawal progress also
needs the appropriate temporal/strategy claim and explicit liquidity, scheduling,
data-availability and finality assumptions. Even `R <= S` alone does not establish
that a temporal controller is realizable. A candidate safety envelope covers only
its stated properties; the mapping to actual runtime behavior remains an obligation.

## Boundaries learned from the existing experiments

- Admission requires entailment: `spend & policy' = 0`. Mere nonempty overlap proves
  only that some interpretation is permitted. The existing repaired admission
  experiment addresses this failure; see F2 in the [ADT findings](../../experiments/tau_adt/README.md).
- In the linked demo, `keeps = (new & old')'` is algebra-valued. Tightening requires
  `keeps == TOP`; nonzero or host-language truthiness is insufficient.
- The retained F5 counterexample distinguishes `{A} | {B}` from `{A || B}` for
  time-varying streams. Boolean difference is mathematically sound, but the wrong
  temporal encoding misrepresents row membership. This historical finding was
  not rerun on a newer engine here. Do not mount generic table differences as a
  balance audit based on the original positive examples.
- Set union is idempotent. Two equal deposits remain distinct occurrences with
  distinct provenance; semantic deduplication must not collapse them. Semantic
  equality also does not replace policy hashes, authenticated predecessors,
  release identities, current-head checks, replay state or destination ancestry.
- A financial refactor must preserve full observable transition behavior: amounts,
  rounding, ownership, outputs/effects, rejection precedence, retries and recovery.
  Equality of allow/deny sets alone is insufficient. Version migration may require
  a proved refinement relation rather than textual or state-schema equality.

## Evidence and replay

A read-only Luna Max review mapped the governance seams. Its findings were checked
against the source; the review itself grants no assurance status.

The following independent finite model checks all 256 old/new pairs and all 1,296
feasible `(required, safe, proposal)` triples over four abstract admission cases.
It also retains total-freeze, nonempty-freeze, truthiness and overlap counterexamples.
These are finite algebra checks, not a Tau-engine or economic runtime proof.

```python
from itertools import product

top = 15
def subset(a, b):
    return a & (top ^ b) == 0

pairs = repairs = 0
for old, new in product(range(16), repeat=2):
    added, removed = new & (top ^ old), old & (top ^ new)
    assert subset(new, old) == ((top ^ added) == top)
    assert (subset(new, old) and subset(old, new)) == (old == new)
    assert new == ((old & (top ^ removed)) | added)
    if subset(new, old):
        assert new | removed == old
    pairs += 1
for required, safe, proposal in product(range(16), repeat=3):
    if not subset(required, safe):
        continue
    repair = required | (proposal & safe)
    assert subset(required, repair) and subset(repair, safe)
    assert required | (repair & safe) == repair
    if subset(required, proposal) and subset(proposal, safe):
        assert repair == proposal
    repairs += 1
# Bits: valid withdrawal, valid cancellation, valid swap, unauthorized debit.
assert subset(0, 7) and (3 & (top ^ 0)) != 0
assert 4 != 0 and subset(4, 7) and (3 & (top ^ 4)) != 0
assert (top ^ (12 & (top ^ 4))) != 0 and not subset(12, 4)
assert 12 & 7 != 0 and not subset(12, 7)
assert (pairs, repairs) == (256, 1296)
print(pairs, repairs)
```

Run the block with ordinary `python3` (without `-O`): output `256 1296`.
The existing source-bound simplification was also replayed with:

```sh
python3 -B -m experiments.tau_economic_qualification_v1.conservation_equivalence
```

All five obligations matched under Z3 4.15.4: equal-delta conservation and all four
output-predicate equivalence queries were UNSAT; the one-atom positive case and two
independent guard controls were SAT. The command still reports
`runtime_qualified=false` and `performance_qualified=false`. Its translation to
QF_BV32 is manual and source-bound; it does not qualify the Tau compiler.

`python3 -B tools/zenodex_oracle_query_policy_chaos.py` also passed: accepted
baseline, 19/19 rejected input mutations, zero failed cases. Documentation replay,
fence balance, local links and the external source digest passed. The general
`python3 -B tools/check_claims_registry.py` check failed on an existing reference
to missing `tools/check_derivatives_authorization_matrix.py` at claim index 123;
that file is also absent from the base commit. The registry was left unchanged.

## Next bounded deliverable

Specify one offline old/new policy comparison against an existing typed oracle or
governance contract. Reuse direct numeric checks where sufficient; qualify a Tau
or SMT encoding only where it adds coverage. Include a valid successor and concrete
unsafe-permission, lost-permission, context-mismatch and inconclusive-check controls.
If it succeeds, integrate evidence with the existing policy-pin review path while
preserving exact-content authorization and current-head admission.

This supports V3 W02, W07 and W09. It creates no new registry, wire format, runtime
dependency or authority. Broader deployment, temporal liveness, implementation
refinement and production value-safety qualification remain open obligations.
No V3 completion credit is assigned to this assessment.
