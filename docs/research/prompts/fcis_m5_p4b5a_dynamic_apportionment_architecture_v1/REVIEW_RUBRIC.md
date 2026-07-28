# P4B5A dynamic apportionment review rubric

## Automatic no-go

Any item below makes a proposed architecture `NO_GO`:

- Per-step destination credits do not sum exactly to the provisional fee.
- An allocation, residue, or state loses asset or stable domain identity.
- Monetary dust, an IOU, or a future keyholder debit remains.
- A policy operator can make cumulative discrepancy unbounded under the
  proposed policy lifecycle.
- Ordinary account, destination, or policy rotation creates fresh state.
- The state key is controlled by a keyholder or command.
- The algorithm uses work proportional to a U256 amount.
- Python and Rust integer, remainder, overflow, or tie-break semantics differ.
- Same-batch V1/V2 acceptance changes are hidden.
- A provisional fee lacks replacement replay conservation lineage.
- A reject exposes a successor, patch, distribution, or partial state.
- Distribution evidence can be executed again by the shell.
- V1 nonzero scalar dust is assigned an invented asset or owner.
- A sampled or bounded result is presented as an unbounded proof.
- Runtime implementation or mount changes are proposed as part of this
  review-only checkpoint.

## Required candidate coverage

- [ ] Fixed-weight cycle-closed cursor.
- [ ] Dynamic deficit or entitlement vector.
- [ ] Bounded jump-ahead sequential scheduler.
- [ ] One additional family or a justified reduction.
- [ ] Direct small-domain oracle.
- [ ] Existing adaptive-policy witnesses.
- [ ] Stable-domain rotation and migration.
- [ ] Same-batch spending semantics.
- [ ] Replacement provisional lineage.
- [ ] U256 maximum and every denominator boundary.
- [ ] Tie, zero-weight, concentrated-weight, and alias cases.
- [ ] Same-key fragmentation counterexample.

## Scoring

Score each area from 0 to 5 after automatic no-go review.

| Area | Score | Evidence |
| --- | ---: | --- |
| Per-step conservation and nonnegative output | | |
| Adaptive-policy theorem or construction closure | | |
| Stable-domain identity and migration | | |
| V2 accepted-language honesty | | |
| Provisional replay lineage | | |
| U256 and cross-language determinism | | |
| Resource bounds | | |
| Canonical encoding and commit bindings | | |
| Counterexample and mutation quality | | |
| State/proof simplicity and auditability | | |

Grade:

```text
A: 46-50, no automatic no-go, decisive proof/evidence
B: 40-45, no automatic no-go, bounded open proof work
C: 34-39, architecture remains blocked
NO_GO: any automatic no-go or score below 34
```

An A report may justify a packet amendment review. It does not authorize
runtime implementation or mounting.

## Cross-agent synthesis

When comparing agent reports:

1. Normalize each proposal to the laws in `PROBLEM_CONTRACT.md`.
2. Run all proposals against the same counterexample corpus.
3. Separate theorem validity from whether the theorem captures the desired
   protocol.
4. Prefer independently replayed counterexamples over prose confidence.
5. Merge equivalent proposals by observable state, allocation, and migration.
6. Preserve every losing candidate and its smallest falsifier.
7. Request a focused second review of the leading proposal before amending the
   packet.
