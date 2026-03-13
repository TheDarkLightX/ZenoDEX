---
title: README
type: note
permalink: autonomous-tau-dex-review/src/tau-specs/recommended/readme
---

# Recommended Tau Specs - Profiles (Risk and Performance)

This folder contains Tau specs intended for reuse and integration.

Because Tau execution time can vary widely based on the shape of a spec, we keep multiple versions of some modules (for example swap and settlement) with explicit tradeoffs:

- **Faster** and smaller Tau gates (usually "proof-gated") for production verification budgets.
- **More complete** Tau-only specs that may be slower but reduce trust assumptions.

Recent optimized additions from the experiment harness are intentionally decomposed:

- `batching_v1_5_compact_single_gate.tau` is the current fast batching candidate.
- `swap_bv32_safe_range_guard_v1.tau` is designed to supplement the proof-gated swap specs when you want the trace-backed `proof_gate + safe_range` posture.
- `settlement_price_rails_aligned_v1.tau`, `settlement_module_flag_bundle_v1.tau`, and `settlement_v5_aligned_compact_bundle.tau` expose the aligned-input settlement posture that was validated against curated execution traces.

The canonical mapping from component to "profile" lives in:

- `src/tau_specs/recommended/spec_profiles.json`

## Profiles

These are the main profiles we use when selecting a spec version:

- **fast_proof_gated**
  - Tau checks a small structural gate and requires `proof_ok` + `binding_ok` (fail-closed flags) from an external verifier.
  - Expected to be the most predictable under tight block verification budgets.
  - Some variants also declare `supplemental_spec_paths`; those extra Tau guards are part of the intended composed policy and should be executed fail-closed alongside the primary spec.

- **tau_only_structural**
  - Tau checks structural constraints and state transitions, but may not validate full pricing math.
  - Use only with additional verification (for example a proof gate, or a trusted execution environment).

- **tau_only_strict**
  - Tau enforces stricter invariants (example: k-monotonicity with explicit overflow guards).
  - More trust-minimized, but often slower.

- **tau_only_full_settlement**
  - Tau validates multiple components end-to-end (settlement, token, tokenomics).
  - Most complete, usually slowest.

## Performance budgets

As a rule of thumb for this repo, we treat these as the maximum acceptable per-step verification time on a developer machine:

- fast: 10s
- medium: 30s
- slow: 60s
- very_slow: 90s

On faster hardware these are often materially lower, but you should still test worst-case specs on the target node hardware.

## How to measure

The trace harness records real execution traces for a curated set of DEX-critical cases:

- `python3 -u tools/tau_trace_harness.py --severity error`

It writes a JSON report (including per-case `elapsed_s`) to:

- `generated/tau_trace_harness_report.json`

To summarize and join timings with the profile mapping:

- `python3 tools/tau_perf_report.py --out generated/tau_perf_report.md`