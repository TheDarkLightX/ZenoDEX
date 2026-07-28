# FCIS M5-P4B5A review checklist

## Automatic NO-GO

- [ ] Exact ancestor is `6c4e7c6be89f76605e86c5532a4841d5e271611b`.
- [ ] Mounted authority paths remain byte-identical.
- [ ] No V1 accepted language is silently changed.
- [ ] Every authoritative amount carries asset and custody owner.
- [ ] No authoritative sum combines distinct custody keys.
- [ ] Distribution uses only exact replay `protocol_fee_paid`.
- [ ] `fee_paid` and routed aggregate fees cannot fund distribution.
- [ ] Destination custody is exact and receipt-bound.
- [ ] Accepted distributions are applied to the returned balance candidate.
- [ ] Residual dust stays in source custody and is keyed by source plus asset.
- [ ] Reject carries no successor, patch, distribution, or accumulator.
- [ ] V1 nonzero-dust migration fails closed.
- [ ] Exact values use controlled construction and the closed combinator.
- [ ] Canonical codecs, roots, patches, receipts, and bundles bind V2.
- [ ] Python/Rust exact-byte parity is source-pinned.
- [ ] All mechanism-conformance mutants are killed by the intended rule.
- [ ] Four pre-mount structural profiles pass.
- [ ] `final-mount` does not improve through suppression or allowlist widening.

Any unchecked item blocks `M5_P4B5A_COMPLETE_UNMOUNTED`.

## Required code-reading attacks

- [ ] Trace each protocol fee from quote to protocol-recipient balance credit.
- [ ] Trace each distribution debit to the exact same source, asset, and
      credited amount.
- [ ] Confirm LP-retained fees remain in pool reserves.
- [ ] Confirm route replay cannot synthesize a protocol credit from total fees.
- [ ] Confirm policy recipients cannot come from the command or settlement.
- [ ] Confirm aliases aggregate through canonical balance deltas.
- [ ] Confirm old dust cannot be assigned an asset through a default.
- [ ] Confirm fresh and retained dust never count twice.
- [ ] Confirm distribution records cannot be executed again by the shell.
- [ ] Confirm mutation tests recompute outer hashes before semantic checking.

## Architecture grade

Score 0 to 5:

| Area | Score | Evidence |
| --- | ---: | --- |
| Denomination closure | | |
| Custody closure | | |
| Exact replay lineage | | |
| State-applied conservation | | |
| Dust and migration semantics | | |
| Canonical order and bounds | | |
| Versioned admission and encoding | | |
| Effects, receipts, and roots | | |
| Cross-language parity | | |
| Mount isolation and evidence honesty | | |

Grade:

```text
A   46-50 and no automatic NO-GO
B   40-45 and no automatic NO-GO
C   34-39 and no automatic NO-GO
NO-GO otherwise
```

## Review outcome

Use one:

```text
M5_P4B5A_COMPLETE_UNMOUNTED
M5_P4B5A_BLOCKED_LINEAGE
M5_P4B5A_BLOCKED_CUSTODY
M5_P4B5A_BLOCKED_CODEC
M5_P4B5A_BLOCKED_PARITY
```

No outcome authorizes a mounted switch.
