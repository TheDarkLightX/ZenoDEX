# ZenoDEX Tau Bitvector Frontier Decision - 2026-06-28

## Executive Result

No for the broad default. Yes for a small profile-gated bv16 sequence-check island.
Use direct Tau bitvectors only for small bounded kernels with replayed profile evidence; keep host projection as the default for broad receipt machinery.

## Decision Facts

- `small_direct_bv16_island_supported` = `True`
- `broad_host_projection_refuted` = `False`
- `host_projection_default_preserved` = `True`
- `profile_gate_required` = `True`
- `checked_tau_binaries` = `6`
- `invalid_accepts` = `0`
- `fast_direct_labels` = `workspace_latest, workspace_runtime, bitblasting, bitblasting_opt, bitblasting_cegqi_bv_default`
- `slow_or_worse_direct_labels` = `upstream_main`

## Probe Inputs

- Direct spec: `src/tau_specs/recommended/receipt_sequence_bv16_guard_v1.tau`
- Projected spec: `src/tau_specs/recommended/receipt_sequence_projected_guard_v1.tau`
- Checked Tau binaries: `6`
- Equivalent direct/projected runs: `6`

## Non-Claims

- This does not prove arbitrary direct Tau bitvector arithmetic is viable.
- This does not make direct bitvectors a production-required receipt gate.
- This does not replace host-side hash, signature, membership, history, or chain-binding verifiers.
- This does not claim upstream-main performance is acceptable for the direct bv16 island.

## Replay

```bash
python3 tools/zenodex_tau_bitvector_frontier_decision_20260628.py
```
