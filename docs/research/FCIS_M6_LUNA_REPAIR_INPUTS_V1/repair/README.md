# FCIS M6 Durable Retraction Luna Repair Handoff

This handoff converts the independent review verdict
`REVISE_M6_DURABLE_RETRACTION_RESEARCH_PACKET_V1` into an implementation
contract for Luna.

Files:

```text
REVIEW_AND_REPAIR_SPEC.md
  Normative findings, authority boundaries, repair obligations, evidence, and
  terminal condition.

REPAIR_TASKS.json
  Machine-readable dependency order L00-L08.

LUNA_PROMPT.md
  Copy-ready prompt for the implementation agent.
```

Use:

1. Give Luna all three files.
2. Use `LUNA_PROMPT.md` as the execution prompt.
3. Require Luna to start from the exact base and verify the supplied archive
   hashes before editing.
4. Require a remote draft PR with an implementation target and one
   documentation-only packet child.
5. Keep the result unmounted until a new independent exact-head review.

The prompt authorizes implementation and draft review delivery only. It does
not authorize merge, deployment, migration authority switch, datastore mount,
or value movement.
