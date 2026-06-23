# Verification Report

**Model**: `perp_epoch_isolated_v3`  
**IR Hash**: `23a9b8ec0233f351`  
**Timestamp**: 2026-05-31T13:33:49.066325+00:00

> [!NOTE]
> ✅ **VERIFIED** - All invariants proven inductive

## Scope

- **Badge**: `Inductive(k=1)`
- **Time**: `unbounded`

## Environment Model

- **Scheduler**: `sequential`
- **Adversary**: may choose any declared command each step with any in-domain parameters

## Toolchain

- **ESSO code hash**: `1145cf77668b6d86cda83d79820b13a65fbde12f`
- **Python**: `3.12.3 (main, Mar 23 2026, 19:04:32) [GCC 13.3.0]`
- **Platform**: `Linux-6.17.0-29-generic-x86_64-with-glibc2.39`
- **Z3**: `4.15.4`
- **CVC5**: `This is cvc5 version 1.1.2`
- **Cargo**: `cargo 1.87.0 (99624be96 2025-05-06)`

## Summary

| Metric | Value |
|--------|-------|
| Total Queries | 11 |
| Passed (UNSAT) | 11 |
| Failed (SAT) | 0 |
| Inconclusive | 0 |

## Solver Cross-Check

| Solver | Status |
|--------|--------|
| Z3 | ✅ Pass |
| CVC5 | ✅ Pass |
| **Agreement** | ✅ Yes |

## Verification Artifacts


## Notes

- Cross-verified by Z3 and CVC5

