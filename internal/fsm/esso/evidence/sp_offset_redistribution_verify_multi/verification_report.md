# Verification Report

**Model**: `liquity_v1_sp_offset_redistribution_bounded`
**IR Hash**: `7b505df182da9fbf`
**Timestamp**: 2026-07-16T09:47:25.200644+00:00

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
- **Python**: `3.12.3 (main, Jun 19 2026, 12:46:00) [GCC 13.3.0]`
- **Platform**: `Linux-6.17.0-35-generic-x86_64-with-glibc2.39`
- **Z3**: `4.15.4`
- **CVC5**: `This is cvc5 version 1.1.2`
- **Cargo**: `cargo 1.87.0 (99624be96 2025-05-06)`

## Summary

| Metric | Value |
|--------|-------|
| Total Queries | 2 |
| Passed (UNSAT) | 2 |
| Failed (SAT) | 0 |
| Inconclusive | 0 |

## Solver Cross-Check

| Solver | Status |
|--------|--------|
| Z3 | ✅ Pass |
| CVC5 | ✅ Pass |
| **Agreement** | ✅ Yes |

## Verification Artifacts

- **SMT-LIB2**: `internal/fsm/esso/evidence/sp_offset_redistribution_verify_multi/smtlib`

## Notes

- Cross-verified by Z3 and CVC5
