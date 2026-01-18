# Tau Specs - Risk Profiles and Performance Budgets

Some DEX checks are cheap to express directly in Tau, while others are expensive (or impractical) under Tau's current execution strategy.

To make the tradeoffs explicit, this repo keeps multiple spec versions for the same logical component. Each version targets a different combination of:

- **Risk posture** (what is validated in Tau vs delegated elsewhere)
- **Performance** (how much time we budget per verification step)

The machine-readable mapping from component to spec file is in:

- `src/tau_specs/recommended/spec_profiles.json`

## Risk profiles (selection intent)

### fast_proof_gated

Use when you need predictable block verification time.

- Tau enforces a small structural gate.
- The heavy computation is performed externally (Python/Rust + verifier).
- Tau requires `proof_ok` and `binding_ok` to be `1:sbf` (fail-closed).

### tau_only_structural

Use for integration sanity checks, or as one layer in a deeper verification stack.

- Tau validates structural constraints and state transitions.
- The spec may not validate full pricing math.

### tau_only_strict

Use when you want Tau itself to validate stricter invariants.

- Tau validates more than just structure (example: k-monotonicity).
- Usually slower. May require tighter input bounds to avoid modular overflow.

### tau_only_full_settlement

Use for deep audits and "full spec" runs.

- Tau validates multiple components end-to-end (settlement + token + tokenomics).
- Usually the slowest option.

## Performance budgets (developer machine)

The repo uses these budgets for "time to verify one step" on a developer machine:

- fast: 10 seconds
- medium: 30 seconds
- slow: 60 seconds
- very_slow: 90 seconds

These numbers are not universal. Faster machines will usually reduce the wall-clock time, but you still need to measure worst-case specs on the target node hardware.

## DEX-critical components and available variants

### Swap validation

- **Exact-in**
  - fast_proof_gated: `src/tau_specs/recommended/swap_exact_in_proof_gate_v1.tau`
  - tau_only_structural: `src/tau_specs/recommended/swap_exact_in_v1.tau`
  - tau_only_strict: `src/tau_specs/swap_exact_in_v4.tau`

- **Exact-out**
  - fast_proof_gated: `src/tau_specs/recommended/swap_exact_out_proof_gate_v1.tau`
  - tau_only_structural: `src/tau_specs/recommended/swap_exact_out_v1.tau`
  - tau_only_strict: `src/tau_specs/swap_exact_out_v4.tau`

### Settlement gates

These specs add "rails" around swaps (ordering, sandwich checks, stability), then combine either:

- Proof-gated component checks (fast), or
- Full Tau-only validation (slow)

Variants:

- fast_proof_gated (v1): `src/tau_specs/recommended/settlement_v1_proof_gate.tau`
- fast_proof_gated (v2 buyback): `src/tau_specs/recommended/settlement_v2_buyback_proof_gate.tau`
- fast_proof_gated (v3 buyback + floor): `src/tau_specs/recommended/settlement_v3_buyback_floor_proof_gate.tau`
- fast_proof_gated (v4 buyback + floor + unit + rebate + lock-weight): `src/tau_specs/recommended/settlement_v4_buyback_floor_rebate_lock_proof_gate.tau`
- tau_only_full_settlement: `src/tau_specs/recommended/settlement_v4_buyback_floor_rebate_lock.tau`

### Intent safety (replay + expiry)

- Nonce replay: `src/tau_specs/recommended/nonce_replay_guard_v1.tau`
- Expiry window: `src/tau_specs/recommended/intent_expiry_guard_v1.tau`

### Policy modules (parameter registry + revision policy)

These can be run Tau-only, or proof-gated if you want more complex off-chain logic while keeping Tau cheap.

- Parameter registry
  - tau_only: `src/tau_specs/recommended/parameter_registry_v1.tau`
  - fast_proof_gated: `src/tau_specs/recommended/parameter_registry_v2.tau`

- Revision policy
  - tau_only: `src/tau_specs/recommended/revision_policy_v1.tau`
  - fast_proof_gated: `src/tau_specs/recommended/revision_policy_v2.tau`

## How to measure actual performance

The most reliable measurement is to run Tau on representative traces, not just parse the file.

Run the trace harness:

```bash
python3 -u tools/tau_trace_harness.py --severity error
```

It writes:

- `generated/tau_trace_harness_report.json` (includes per-case `elapsed_s`)

To summarize and join timings with the profile mapping:

```bash
python3 tools/tau_perf_report.py --out generated/tau_perf_report.md
```
