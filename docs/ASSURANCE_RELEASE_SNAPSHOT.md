## Assurance Release Snapshot

Pinned snapshot for the current release-backed tree:

- acceptance TCB: `341 passed`, `100%` branch coverage
- critical gate: `1311 passed`, `100%` branch coverage
- release gate: passed end to end
- mutation gate: `7/7` killed
- fuzz gate: `11 passed`
- snapshot recovery: `16 passed`
- Tau syntax: `58/58`
- Tau traces: `1/1`

### Derivatives Formal Note

The published v1.1 funding-rate formal claim is now the decomposed one:

- `funding_rate_market_v1` for phase and state-transition logic
- `funding_rate_settlement_witness_v1_1` for settlement arithmetic

The monolithic `funding_rate_market_v1_1` kernel remains useful as a parity and reference artifact, but it is not part of the published formal release claim.

### Replay

Use the repo-local replay lanes:

```bash
bash tools/run_derivatives_evidence.sh
bash tools/run_release_gate.sh
```
