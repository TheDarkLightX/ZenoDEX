# M5-P4B0 Review Checklist

Automatic `NO-GO` applies if any item below fails.

## Contract coverage

- [ ] Requirement inventory is exact:
      `P4B0-001`, `P4B0-002`, `P4B0-003`, `P4B0-004`, `P4B0-005`,
      `P4B0-006`, `P4B0-007`, `P4B0-008`, `P4B0-009`, `P4B0-010`,
      `P4B0-011`, `P4B0-012`, `P4B0-013`, `P4B0-014`, `P4B0-015`,
      `P4B0-016`, `P4B0-017`, `P4B0-018`, `P4B0-019`, and `P4B0-020`.
- [ ] `P4B0-001` through `P4B0-020` each bind at least one executable test.
- [ ] All test IDs in `requirements.json` exist in `TEST_MATRIX.md` and pytest collection.
- [ ] The implementor ran `check_packet.py` before editing and at the final head.

## Boundary fidelity

- [ ] Ingress starts from exact canonical bytes.
- [ ] Duplicate keys are rejected before conversion to a mapping.
- [ ] Structural admission calls the declared closed combinator schema.
- [ ] No hand-written second admission system exists beside the combinator.
- [ ] Policy and registries are source-owned and unavailable to input selection.
- [ ] Owned values are exact, final, frozen, slotted, and recursively owned.
- [ ] Forbidden mechanisms scan is clean on every new module.

## Semantic fidelity

- [ ] Same command, state, and context bytes are established before comparison.
- [ ] Result kind agrees.
- [ ] Rejection mapping is explicit and injective where distinctions matter.
- [ ] Accepted projection covers all eight committed state fields.
- [ ] Economic projection covers ordering, fees, dust, nonces, and effects.
- [ ] Patch application reproduces the exact successor.
- [ ] Receipt, replay, outbox, and bundle recompute from one decision.
- [ ] Version differences use only the fixed policy registry.

## Evidence fidelity

- [ ] Artifact is canonical, source-pinned, policy-hash-bound, and deterministic.
- [ ] Every P4A fixture has exactly one result row.
- [ ] Mismatches are preserved with a stable first path.
- [ ] At least 20 rehashed semantic mutants are killed.
- [ ] All 12 independent reviewer attacks fail closed.
- [ ] Normal validation and `--require-all-refine` have distinct exit semantics.

## No-mount boundary

- [ ] Required ancestor `fd1ef9f1` is present.
- [ ] `src/core/dex.py` is byte-identical to the required ancestor.
- [ ] No deployment, verifier policy, proof guest, Rust authority, or Tau authority changed.
- [ ] New refinement modules are unreachable from mounted dispatch.
- [ ] P4A remains structurally valid and `BLOCKED`.

## Grade

| Area | Weight |
| --- | ---: |
| Frozen contract and admission design | 20 |
| Shared semantic refinement | 25 |
| Exact-only consistency obligations | 20 |
| Provenance, determinism, and budgets | 15 |
| Mutation and independent attacks | 15 |
| No-mount discipline and reporting | 5 |

A score below 90, any automatic no-go, or any unexplained mismatch prohibits
the next mount checkpoint.
