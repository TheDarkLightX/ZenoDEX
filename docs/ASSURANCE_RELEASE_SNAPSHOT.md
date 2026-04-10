## Assurance Release Snapshot

<!-- Generated from docs/assurance_release_snapshot.json and docs/claims_registry.yaml. -->

Pinned release snapshot for this tree (as of 2026-04-10):

- acceptance TCB: `361 passed`, `99.4%` branch coverage
- critical gate: `735 passed, 1 skipped`, `99%` branch coverage
- release gate: `passed end to end`
- mutation gate: `7 killed, 0 survived, 0 inconclusive`
- fuzz gate: `11 passed`
- snapshot recovery: `19 passed`
- Tau syntax: `62/62`
- Tau traces: `1/1`

This is historical release evidence for the pinned release tree. It is not a live status board for the current checkout.
For live checkout status, use `python3 tools/permissionless_assurance.py status`.

### Derivatives Formal Note

- The published v1.1 funding-rate formal claim is now the decomposed one:
  `funding_rate_market_v1` for phase/state transitions plus
  `funding_rate_settlement_witness_v1_1` for settlement arithmetic.
- The monolithic `funding_rate_market_v1_1` kernel remains useful as a parity/reference artifact, but it is not part of the published formal release claim.
- `funding_rate_market_v1` and `curve_selection_market_v1` remain `disputed` in the claims registry for settlement authorization semantics and should not be treated as authorization-complete public settlement guarantees.
- The disputed authorization status above is sourced from `smt:funding_rate_market_v1:inductive_z3_cvc5`, `smt:curve_selection_market_v1:inductive_z3_cvc5` in the claims registry.

### Vocabulary

- `release-backed` means included in the current published formal/public assurance claim.
- `public replay` means reproducible from a clean checkout plus the documented external toolchains via the shipped replay/checker surface.
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
