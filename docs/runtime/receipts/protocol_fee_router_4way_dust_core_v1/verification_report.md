# Verification Report

**Model**: `protocol_fee_router_4way_dust_core_v1`  
**IR Hash**: `84de72755e172239`  
**Timestamp**: 2026-05-31T06:52:26.033261+00:00

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

- **SMT-LIB2**: `/tmp/esso_fee4/smtlib`

## Notes

- Cross-verified by Z3 and CVC5

