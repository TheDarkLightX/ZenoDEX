# ZenoDEX Tau Solver Portfolio Breakthrough - 2026-06-28

## Executive Result

Tau now gates a combined AB/CoW solver-upgrade decision with host-computed parity, capacity-scope, performance, fallback, rollback, negative replay, and no-authority facts.

Tau admits the portfolio certificate only. Host/kernel verifiers remain authoritative for settlement and state transitions.

## Tau Specification

- Spec: `src/tau_specs/recommended/solver_portfolio_upgrade_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau cases: `8`
- Invalid accepts: `0`

## Portfolio Facts

- `certificate_active` = `1`
- `ab_solver_candidate_present` = `1`
- `cow_solver_candidate_present` = `1`
- `ab_bruteforce_oracle_parity_ok` = `1`
- `cow_bruteforce_oracle_parity_ok` = `1`
- `ab_full_state_scope_ok` = `1`
- `cow_uncoupled_or_bounded_capacity_scope_ok` = `1`
- `negative_replay_ok` = `1`
- `deterministic_tie_ok` = `1`
- `performance_floor_ok` = `1`
- `resource_budget_ok` = `1`
- `fallback_paths_ok` = `1`
- `rollback_available` = `1`
- `advisory_model_only` = `1`
- `no_authority_effect` = `1`

## Work Items

### 1. AB Ordering

bounded full-state subset DP with brute-force parity and explicit fallback after 12
The certificate does not claim a compressed Held-Karp state is sound for integer CPMM ordering.

### 2. CoW Matching

uncoupled Hungarian assignment plus bounded coupled-capacity DP evidence
The certificate does not claim arbitrary grouped-capacity CoW matching is polynomial.

## New Tau Specification Patterns

- `solver_portfolio_upgrade_certificate`: Promotes AB and CoW algorithm upgrades only when independent solver evidence and rollout rails agree.
- `negative_knowledge_gate`: Turns known failed simplifications into reject bits before they become public or production claims.
- `performance_floor_gate`: Lets host-computed complexity evidence participate in Tau admission without putting timing arithmetic inside Tau.
- `advisory_model_boundary_gate`: Keeps EBRM or research selectors in proposal/ranking mode while deterministic verifiers decide acceptance.

## Non-Claims

- The certificate is a research and rollout evidence gate, not a settlement verifier.
- All numeric complexity, matching, CPMM, and DP computations stay host-side.
- The performance floor is host-computed evidence over bounded reports, not a Tau timing measurement.
- Rollback availability is an external rollout fact supplied to Tau and must be backed by deployment evidence before production use.

## Replay

```bash
python3 tools/zenodex_tau_solver_portfolio_breakthrough_20260628.py
```
