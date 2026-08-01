# FCIS M6 Task D10 Plan

TASK_ID: D10
TITLE: Prove the abstract ANF composition theorem

## Scope

D10 adds a machine-checked abstract composition theorem for the R04 ANF
boundary. The theorem composes four lineage-preservation witnesses:

1. horizontal semantic/artifact coherence;
2. global path/gate coherence;
3. vertical durable retraction with a partial `Except Reject A` reopen;
4. external effect ancestry.

Authentication and complete inventory are explicit predicates and proof fields.
The theorem does not construct either property from roots or caller data.

## Required outputs

- `lean-mathlib/Proofs/FCISANFComposition.lean`
- `lean-mathlib/lakefile.lean` root registration
- this plan, report, evidence, and source manifest

## Fail-closed acceptance

```text
cd lean-mathlib && lake env lean Proofs/FCISANFComposition.lean
cd lean-mathlib && lake build
python3 -m json.tool docs/research/m6_tasks/TASK_D10_EVIDENCE.json
python3 docs/research/m6_tasks/validate_task_packet.py docs/research/m6_tasks D10
sha256sum --check --strict docs/research/m6_tasks/TASK_D10_SOURCE_MANIFEST.sha256
git diff --check
```

The focused Lean file must compile with no `sorry`, `admit`, or user axioms.
The theorem remains abstract and unmounted. Its premises are contract inputs,
not evidence that the production caller, datastore, proof context, or effect
worker currently supplies them.

## Theorem contract

For every accepted durable effect, if authentication, complete inventory,
horizontal coherence, global path/gate coherence, vertical partial durable
retraction, and external effect ancestry are supplied, then there exists one
source lineage equal to the effect lineage. The result retains the
authentication and inventory witnesses in its conclusion.

## Nonclaims

D10 does not prove production authentication, TCG inventory completeness,
proof soundness, datastore publication or recovery, destination idempotency,
runtime no-bypass coverage, migration authority, whole-system conservation,
liability, backing, ZUSD safety, or value movement. It does not instantiate the
abstract premises with a mounted runtime path.
