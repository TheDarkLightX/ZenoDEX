# FCIS M5-P4B0 Legacy-to-FCIS Refinement Packet

This packet authorizes one bounded, unmounted checkpoint. It converts the 24
raw legacy-versus-FCIS divergences from P4A into a directional, versioned
refinement decision.

The required reviewed ancestor is `fd1ef9f1`. The implementation agent must
create its implementation branch directly from that commit and record the
exact start SHA. The packet lives in a later documentation commit supplied by
the reviewer. Read it with `git show`; do not cherry-pick the packet commit
into the implementation branch.

The allowed result is:

```text
M5_P4B0_REFINEMENT_EVIDENCE_ONLY
```

This packet does not authorize a change to mounted DEX authority, production
configuration, verifier policy, Rust authority, proof guest authority, or
legacy deletion.

Read in this order:

1. `CONTRACT.md`
2. `TEST_MATRIX.md`
3. `REVIEW_CHECKLIST.md`
4. `IMPLEMENTOR_PROMPT.md`
5. `requirements.json`

The reviewer validates the packet at its documentation commit with:

```bash
python3 docs/specs/fcis_m5_p4b0_legacy_refinement_v1/check_packet.py
```

The implementor validates the P4A prerequisite at `fd1ef9f1`, before making
changes, with:

```bash
python3 tools/check_fcis_m5_p4a_readiness.py --check
```

P4A must remain a structurally valid `BLOCKED` checkpoint throughout this
task. P4B0 may reduce the count of unexplained semantic mismatches in a new
artifact. It may not rewrite the P4A artifact to claim byte parity.
