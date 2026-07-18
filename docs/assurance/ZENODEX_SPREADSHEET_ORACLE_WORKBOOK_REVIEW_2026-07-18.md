# ZenoDEX Spreadsheet Oracle Workbook Review

**Date:** 2026-07-18

**Source artifact:** `zenodex_spreadsheet_oracle_audit_workbook.xlsx`

**SHA-256:**
`85c1b54988f91821247fb19c657d5288734f9dcfb011bc4c72f9e09b185c1e2e`

**Disposition:** fail closed; no release credit

## Result

The workbook is a useful bounded differential-oracle inventory. It contains 15
visible sheets and 42 intended cases across eight value-moving surfaces. A
LibreOffice recalculation of a temporary copy produced no spreadsheet formula
errors. No external-link or macro dependency was present.

Every case currently has status `MISSING_ACTUAL`:

| Surface | Cases | Passing actuals | Missing actuals |
| --- | ---: | ---: | ---: |
| CPMM exact-in | 5 | 0 | 5 |
| CPMM exact-out | 4 | 0 | 4 |
| Fee carry | 6 | 0 | 6 |
| Perps risk | 5 | 0 | 5 |
| Perps lifecycle | 6 | 0 | 6 |
| zUSD fee liability | 4 | 0 | 4 |
| zUSD redemption guards | 5 | 0 | 5 |
| Immutability aliasing | 7 | 0 | 7 |
| **Total** | **42** | **0** | **42** |

The dashboard's release recommendation is therefore:

```text
BLOCKED: actual outputs missing
```

## Promotion contract

The workbook may receive release credit only when a same-commit deterministic
harness:

1. loads the exact named case and canonical inputs;
2. executes the mounted implementation and any claimed formal/reference lane;
3. writes actual outputs without manual spreadsheet editing;
4. compares units, rounding, reject class, state/effect output, and no-op
   behavior exactly;
5. records source commit, toolchain identities, command, and artifact hashes;
6. treats a missing, malformed, stale, or manually entered actual as failure;
7. runs in the required hosted CI and release gate.

Until then, the workbook is an open BVA and differential-test specification.
It is not evidence that any listed behavior passes.

## Explicit limits

- Finite workbook rows do not prove unbounded arithmetic or state-machine
  properties.
- Expected outputs can share a specification defect with the implementation.
- Spreadsheet recalculation does not authenticate runtime state, Oracle
  provenance, consensus context, signatures, custody, or effect application.
- The workbook does not replace property, stateful, mutation, parity, proof,
  or mounted integration evidence.

```text
WorkbookOracleCases = 42
WorkbookActualOutputsPresent = 0
WorkbookPromotionReady = false
ProductionReleaseAllowed = false
```
