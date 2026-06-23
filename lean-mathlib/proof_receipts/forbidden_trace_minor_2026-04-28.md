# Forbidden Trace Minor Proof Receipt

Date: 2026-04-28

Integrated module:

- `Proofs.ForbiddenTraceMinor`

Aristotle run:

- `fcdbe37a-7196-4b13-a9bf-c3e855c4e24b`

Accepted theorem layer:

- `motif_rejection_lifts_to_all_bad`
- `list_motif_rejection_lifts_to_all_bad`
- `forbidden_motifs_exclude_accepted_bad`
- `guard_hitting_set_rejects_all_bad`
- `antichain_motif_basis_rejection_lifts`

Local acceptance checks:

```text
cd lean-mathlib && lake env lean Proofs/ForbiddenTraceMinor.lean
cd lean-mathlib && lake build Proofs.ForbiddenTraceMinor
python3 tools/check_formal_proof_hygiene.py
pytest -q tests/integration/test_disaster_assurance_ratchets.py
```

Result:

- promoted module checked locally
- targeted Lake build completed successfully
- formal proof hygiene ratchet includes the promoted module
- default hygiene report was clean:
  - `proof_file_count = 20`
  - `active_placeholder_count = 0`

Scope:

- This is a generic disaster-trace compression theorem schema.
- It does not prove any concrete runtime disaster state unreachable by itself.
- Concrete promotion requires an instantiation of:
  - trace type
  - motif embedding relation
  - motif coverage proof
  - motif rejection or guard-soundness proof
  - accepted/rejected disjointness where accepted-bad exclusion is claimed
