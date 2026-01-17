# DEX global conservation v1: checklist (context_key: `dex_global_conservation_v1`)

This checklist is a practical companion to the kernel spec:
- `src/kernels/dex/dex_global_conservation_v1.yaml`

## What must always hold (per asset)
- `totalA := u0A + u1A + poolA + feeA` is constant across transitions.
- `totalB := u0B + u1B + poolB + feeB` is constant across transitions.
- All components remain `>= 0`.

## Common failure modes (what to look for)
- **Fee not accounted (burn bug)**: subtract `amount_in` from user, add only `net_in` to pool, but forget to add `fee` to `feeA` → `totalA` decreases by `fee`.
- **Fee double-accounted (mint bug)**: subtract `amount_in` from user, add `net_in` to pool **and** also add `fee` to `feeA`, but mistakenly add `amount_in` (not `net_in`) to pool → `totalA` increases by `fee`.
- **Output not credited (burn bug)**: subtract `amount_out` from `poolB` but forget to add it to user `B` balance → `totalB` decreases by `amount_out`.
- **Output double-credited (mint bug)**: add `amount_out` to user but forget to subtract from pool → `totalB` increases by `amount_out`.
- **Underflow by missing guards**: allow `amount_in > userA` or `amount_out >= poolB` → negative components.
- **Rounding mismatch**:
  - Fee rounding: using `floor` instead of `ceil` changes `net_in` and can break fee accounting consistency checks.
  - Net input: allowing `net_in <= 0` (e.g., fee rounds up to the full amount) can lead to divide-by-zero / degenerate swaps.
- **Asset mixups**: using `feeA`/`feeB` or `poolA`/`poolB` in the wrong branch silently breaks conservation for one side.
- **Non-deterministic rounding**: any dependence on floating point or host rounding breaks determinism.

## Known falsifiers (for *broken* implementations)
These are minimal counterexamples that should break conservation if a specific bug is present.

### F1: fee burn (fee not credited)
If an implementation does not add `fee` into `feeA` (or elsewhere in asset A accounting), this 1-step trace violates `totalA`:
- Initial: `u0A=10, u1A=0, poolA=10, feeA=0` (so `totalA=20`)
- Initial: `u0B=0, u1B=0, poolB=10, feeB=0` (so `totalB=10`)
- Step: `swap_exact_in(trader=0, amount_in=10, min_amount_out=0, fee_bps=1000)`
  - Fee should be `ceil(10*1000/10000)=1`, net_in should be `9`.
  - If the fee is not credited to `feeA`, then post `totalA = 19` (burn).

### F2: output burn (pool debited but user not credited)
If an implementation subtracts `amount_out` from `poolB` but forgets to add it to the trader’s `B` balance:
- Any non-degenerate swap with `amount_out>0` yields `totalB` decreasing by `amount_out`.

## Context
- Context key: `dex_global_conservation_v1`
