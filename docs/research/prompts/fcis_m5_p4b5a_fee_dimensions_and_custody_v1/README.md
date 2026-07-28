# FCIS M5-P4B5A fee dimensions and protocol custody

Status: frozen implementation checkpoint

Contract version:

```text
zenodex/fcis-m5-p4b5a-fee-dimensions-and-custody/v1
```

Reviewed start:

```text
6c4e7c6be89f76605e86c5532a4841d5e271611b
```

This packet defines one unmounted M5 checkpoint. It removes scalar,
cross-asset fee authority and derives every distributable amount from exact
protocol-custody credits produced by validated swap replay.

Read in this order:

1. `IMPLEMENTATION_PROMPT.md`
2. `REVIEW_CHECKLIST.md`
3. `docs/research/FCIS_M5_P4B5A_PREFLIGHT_20260728.md`
4. `docs/research/FCIS_M5_DOWNSTREAM_BLOCKERS_20260727.md`
5. `docs/research/FCIS_M5_P4B4_IMPLEMENTOR_REPORT_20260727.md`

Permitted outcome:

```text
M5_P4B5A_COMPLETE_UNMOUNTED
```

Fail-closed outcomes:

```text
M5_P4B5A_BLOCKED_LINEAGE
M5_P4B5A_BLOCKED_CUSTODY
M5_P4B5A_BLOCKED_CODEC
M5_P4B5A_BLOCKED_PARITY
```

No P4B5A outcome authorizes a mounted authority switch.
