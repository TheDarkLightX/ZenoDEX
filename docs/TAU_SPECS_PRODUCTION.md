# Tau Specs: Production Curation (DEX)

This repo contains many Tau specs (tokenomics, governance, safety modules). **Not all of them are required to operate the DEX.**

This document defines the **minimal production-posture spec set** needed for the DEX swap path, and the constraints under which those specs are intended to run.

## Production-ready (DEX-critical)

These are the specs the runtime integration can gate swaps with deterministically (trace-level executable under practical timeouts).

- **`src/tau_specs/recommended/nonce_replay_guard_v1.tau`**
  - **Purpose**: strict sequential nonces (replay protection for signed intents).
  - **Runtime**: enforced in Python via `DexState.nonces`; Tau spec is kept as an executable reference gate.

- **`src/tau_specs/recommended/intent_expiry_guard_v1.tau`**
  - **Purpose**: timestamp/validity window checks (stronger than `current < deadline` alone).
  - **Runtime**: can be enforced in Python; Tau spec is kept as an executable reference gate.

- **`src/tau_specs/swap_exact_in_v4.tau`**
  - **Purpose**: validates exact-in swap transitions (structural + reserve transition + \(k\) monotonicity).
  - **Input model**: native `bv[32]` streams.
  - **Critical constraint**: all inputs and post-state fields must satisfy `<= 0xFFFF` so that the internal multiplication used in the \(k\)-guard does **not overflow** under `bv[32]`.

- **`src/tau_specs/swap_exact_out_v4.tau`**
  - Same posture as v4 exact-in, for exact-out swaps.

- **`src/tau_specs/recommended/cpmm_v1.tau`**
  - **Purpose**: lightweight CPMM structural sanity checks (does *not* validate full pricing math).
  - **Use**: quick integration sanity / regression harness.

## Tokenomics (fees / rebates / buyback & burn)

Tokenomics is **optional** for a “DEX that swaps correctly”, but required if you want protocol-level fee routing (treasury/rewards) and buyback/burn behavior.

Current implementation status:
- **Fees**
  - Swap fees are computed in Python (`src/core/cpmm.py`, v8 semantics).
  - A deterministic fee split kernel exists (`src/core/fees.py`), but it is accounting-only unless you wire the split into balances/treasury/vault.
- **Tau-executable tokenomics primitives (recommended)**
  - `src/tau_specs/recommended/tokenomics_buyback_burn_v2.tau` (**PASS** in trace harness)
  - `src/tau_specs/tdex_fee_rebate_v1.tau` (**PASS** in trace harness)
- **Not recommended as direct Tau runtime checks**
  - `src/tau_specs/tokenomics_buyback_burn_v1.tau` (observed TIMEOUT under Tau’s BDD engine; superseded by v2)

## Not currently production-ready as runtime gates (timeouts)

These may be correct as specifications, but are not practical as direct Tau runtime checks under the BDD engine in this repo’s harness posture.

- `src/tau_specs/recommended/swap_exact_in_v1.tau`
- `src/tau_specs/recommended/swap_exact_out_v1.tau`
- `src/tau_specs/token_composite_v1.tau`
- `src/tau_specs/settlement_v1.tau`

## How to verify (trace-level)

Run the curated production suite:

```bash
python3 tools/tau_trace_harness.py --severity error --timeout-s 90 --only nonce_replay_guard_v1_pass --only intent_expiry_guard_v1_pass --only swap_exact_in_v4 --only swap_exact_out_v4 --only cpmm_v1
```

Artifacts are written to:

- `generated/tau_trace_harness/<spec_id>/stdout.txt`
- `generated/tau_trace_harness/<spec_id>/stderr.txt`
- `generated/tau_trace_harness/<spec_id>/repl_script.tau`
- `generated/tau_trace_harness/<spec_id>/outputs.json`

