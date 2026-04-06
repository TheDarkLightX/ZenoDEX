## Assurance Release Snapshot

<!-- Generated from docs/assurance_release_snapshot.json and docs/claims_registry.yaml. -->

Pinned release snapshot for this tree (as of 2026-03-22):

- acceptance TCB: `341 passed`, `100%` branch coverage
- critical gate: `1311 passed`, `100%` branch coverage
- release gate: `passed end to end`
- mutation gate: `7/7 killed`
- fuzz gate: `11 passed`
- snapshot recovery: `16 passed`
- Tau syntax: `58/58`
- Tau traces: `1/1`

### Derivatives Formal Note

- The published v1.1 funding-rate formal claim is now the decomposed one:
  `funding_rate_market_v1` for phase/state transitions plus
  `funding_rate_settlement_witness_v1_1` for settlement arithmetic.
- The monolithic `funding_rate_market_v1_1` kernel remains useful as a parity/reference artifact, but it is not part of the published formal release claim.
- `funding_rate_market_v1` and `curve_selection_market_v1` remain `disputed` in the claims registry for settlement authorization semantics and should not be treated as authorization-complete public settlement guarantees.
- The disputed authorization status above is sourced from `smt:funding_rate_market_v1:inductive_z3_cvc5`, `smt:curve_selection_market_v1:inductive_z3_cvc5` in the claims registry.

### Vocabulary

- `release-backed` means included in the current published formal/public assurance claim.
- `public replay` means reproducible from a fresh clone via the shipped replay/checker surface.
- `authorization-complete` means safe to treat as a public settlement-authorizing guarantee without extra trusted environment inputs.
- `disputed` means intentionally excluded from stronger public authorization claims until the witness/auth lane is trust-complete.

### Replay

Use the repo-local replay lanes:

```bash
bash tools/run_derivatives_evidence.sh
bash tools/run_release_gate.sh
```

### Temporal Surface

- The bounded TLC/TLA+ claim surface is summarized in [docs/TLA_CLAIM_SUMMARY.md](TLA_CLAIM_SUMMARY.md).
- The release gate fail-closes on `python3 tools/render_tla_claim_summary.py --check` and `python3 tools/run_tla_models.py --json`.
