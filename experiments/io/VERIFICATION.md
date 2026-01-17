# IO Experiment Verification

## How to run
Use REPL scripts piped into Tau:

```
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/26_xor_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/27_fee_calc_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/28_balance_transition_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/29_batch_clear_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/30_cpmm_step_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/45_oracle_nonce_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/46_auction_clear_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/47_twap3_guard_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/48_super_gate_from_outputs_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/49_super_lite_gate_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/51_auction_clear_aligned_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/52_twap_guard_aligned_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/53_cpmm_valid_aligned_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/54_risk_budget_aligned_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/50_oracle_nonce_aligned_io.tau
./external/tau-lang/build-Release/tau --severity error --charvar false < experiments/io/55_super_aligned_from_outputs_io.tau
```

## Results (recorded outputs)

- **26_xor_io** (`xor_out.out`): `0, 1, 0, 1, 1`.
- **27_fee_calc_io** (`fee.out`, `net.out`): fees `3, 0, 0`; nets `997, 2000, 5000`.
- **28_balance_transition_io** (`new_balance.out`, `is_safe.out`): balances `700, 65386, 0`; safe flags `1, 0, 1`.
- **29_batch_clear_io** (`matched.out`, `trade_qty.out`, `price_spread.out`): match flags `1, 0, 1`; trade qty `5, 4, 2`; spread `100, 65436, 20`.
- **30_cpmm_step_io** (`amount_out.out`, `new_x.out`, `new_y.out`): amount_out `0, 3`; new_x `10997, 5499`; new_y `10000, 19997`.

## Notes on Tau REPL behavior (current build)

- REPL scripts must be piped to Tau; file arguments are parsed as spec mode.
- Use `iN : type = in file("...")` / `oN : type = out file("...")` in REPL.
- Parenthesize `<->` equivalences inside `r` to avoid precedence surprises.
- `bv[16]` arithmetic is **mod 2^16**, so overflow/underflow explains `fee=0` for larger products and `spread` wrap.
- Defining functions that include division and then invoking them inside `r` caused REPL crashes in this build; division is inlined instead.

- **31_swap_pipeline_small_io** (`fee_small.out`, `net_in_small.out`, `amount_out_small.out`, `new_x_small.out`, `new_y_small.out`): fee `0, 0`; net_in `20, 10`; amount_out `18, 27`; new_x `220, 110`; new_y `182, 273`.
- **32_swap_validity_small_io** (`is_valid_small.out`): `1, 1`.

## Additional learnings

- Combining `sbf` outputs with `bv` outputs **and** division in a single `r` can crash the REPL; keep divisions in bv-only runs, or split into separate REPL steps.
- Mixed `sbf` + `bv` without division is stable.

- **33_temporal_state_io** (`holding.out`, `executing.out`, `buy_fire.out`, `sell_fire.out`, `cooldown_active.out`, `nonce_used.out`, `replay_block.out`):
  - holding: `0, 0, 1, 1, 1, 1, 0, 1`
  - executing: `0, 0, 1, 1, 1, 1, 0, 1`
  - buy_fire: `0, 0, 1, 0, 0, 0, 0, 1`
  - sell_fire: `0, 0, 0, 0, 0, 0, 1, 0`
  - cooldown_active: `0, 0, 0, 1, 1, 0, 0, 0`
  - nonce_used: `0, 0, 1, 1, 1, 0, 0, 1`
  - replay_block: `0, 0, 0, 0, 0, 1, 0, 0`

- **34_batch_auction_io** (`canonical_ok.out`, `no_sandwich.out`, `batch_ok.out`): `1, 0` / `1, 0` / `1, 0`.

## Additional learnings (continued)

- Temporal REPL runs with `t-1` can emit extra output rows beyond input length; treat the first and last rows as warmup/teardown artifacts for now.

- **35_hi_lo_compare_add_io** (`hl_gte.out`, `hl_eq.out`, `hl_safe_add.out`, `hl_sum_hi.out`, `hl_sum_lo.out`):
  - gte `1, 0`; eq `0, 0`; safe_add `1, 1`; sum_hi `1, 1`; sum_lo `3000, 1000`.

- **36_cpmm_valid_hilo_io** (`cpmm_hi_ok.out`, `cpmm_valid.out`): hi_ok `1, 1`; valid `1, 0`.
- **37_risk_budget_io** (`budget_b0.out`, `budget_b1.out`, `can_trade.out`, `trade_fire.out`, `cooldown1.out`, `cooldown2.out`, `cooldown_active_budget.out`):
  - b0 `1, 1, 0, 1, 1, 1, 0`
  - b1 `1, 1, 1, 0, 1, 1, 1`
  - can_trade `0, 0, 1, 1, 0, 0, 1`
  - trade_fire `0, 0, 1, 1, 0, 0, 1`
  - cooldown1 `0, 0, 1, 1, 0, 0, 1`
  - cooldown2 `0, 0, 0, 1, 0, 0, 0`
  - cooldown_active `0, 0, 0, 1, 0, 0, 0`
- **38_balance_hilo_io** (`sum_lo.out`, `sum_hi.out`, `new_hi.out`, `new_lo.out`, `underflow.out`):
  - sum_lo `1200, 744, 100`
  - sum_hi `0, 2, 0`
  - new_hi `0, 2, 65535`
  - new_lo `900, 244, 65436`
  - underflow `0, 0, 1`.

## Notes (REPL vs spec)

- `37_risk_budget_io` uses a 2-bit sbf budget for REPL stability; the bv[16] version is kept in `experiments/27_risk_budget_spec.tau` for spec-mode validation.

- **39_cpmm_valid_8bit_io** (`cpmm8_valid.out`): `1, 0`.
- **40_slippage_guard_io** (`price_stable.out`): `1, 1, 0, 0, 1` (REPL-only stable check; cooldown kept in spec mode).
- **41_batch_pipeline_io** (`batch_canonical.out`, `batch_no_sandwich.out`, `batch_cpmm_ok.out`, `batch_all_ok.out`): `1, 0` / `1, 0` / `1, 0` / `1, 0`.
- **44_twap_guard_io** (`twap_low_ok.out`, `twap_high_ok.out`, `twap_ok.out`): `1, 1` / `1, 0` / `1, 0`.
- **45_oracle_nonce_io** (`oracle_fire.out`, `oracle_nonce_used.out`, `oracle_cd1.out`, `oracle_cd2.out`, `oracle_cd_active.out`):
  - fire `0, 1, 0, 0, 0, 0, 1`
  - nonce_used `0, 1, 1, 1, 1, 0, 1`
  - cd1 `0, 1, 0, 0, 0, 0, 1`
  - cd2 `0, 0, 1, 0, 0, 0, 0`
  - cd_active `0, 0, 1, 1, 0, 0, 0`
- **46_auction_clear_io** (`auction_ok.out`): `1, 0`.
- **47_twap3_guard_io** (`twap3_low_ok.out`, `twap3_high_ok.out`, `twap3_ok.out`): `1, 1` / `1, 0` / `1, 0`.
- **48_super_gate_from_outputs_io** (`super_from_outputs.out`): `0, 0`.
- **49_super_lite_gate_io** (`super_lite_ok.out`): `1, 0, 0`.
- **51_auction_clear_aligned_io** (`aligned_auction_ok.out`): `1, 1, 1`.
- **52_twap_guard_aligned_io** (`aligned_twap_ok.out`): `1, 1, 1`.
- **53_cpmm_valid_aligned_io** (`aligned_cpmm_ok.out`): `1, 1, 1`.
- **54_risk_budget_aligned_io** (`aligned_can_trade.out`): `0, 1, 0, 0`.
- **50_oracle_nonce_aligned_io** (`aligned_oracle_fire.out`): `0, 1, 0, 0`.
- **55_super_aligned_from_outputs_io** (`aligned_super_ok.out`): `0, 1, 0`.

## Composed trace

- `experiments/io/compose_auction_twap_nonce.py` combines `auction_ok.out`, `twap_ok.out`, and `oracle_fire.out` into `auction_twap_nonce_super.out`.
- Current composed result: `0, 0`.
- `experiments/io/compose_auction_twap_nonce_cpmm.py` combines `auction_ok.out`, `twap_ok.out`, `oracle_fire.out`, and `cpmm8_valid.out` into `auction_twap_nonce_cpmm_super.out`.
- Current composed result: `0, 0`.
- `experiments/io/compose_auction_twap_nonce_cpmm_risk.py` combines `auction_ok.out`, `twap_ok.out`, `oracle_fire.out`, `cpmm8_valid.out`, and `can_trade.out` into `auction_twap_nonce_cpmm_risk_super.out`.
- Current composed result: `0, 0`.

## REPL stability notes (updated)

- Complex cooldown logic with multiple sbf outputs + subtraction triggered REPL segfaults; for REPL we use the stability check only, and keep cooldown logic in spec mode (`experiments/30_slippage_guard_spec.tau`).
- CPMM validity with extra bound checks (`small(...)`) caused REPL crashes; the REPL variant uses only the cross-multiply constraint and relies on bounded inputs.
- REPL predicate definitions are more reliable when statements omit trailing periods (`.`); use newline-terminated declarations.

## Composite REPL limitation

- A full super-composite REPL script (all gates in one `r`) consistently segfaulted; I removed it and kept the composite in **spec mode** (`experiments/31_super_composite_spec.tau`). For executable traces, we rely on the component REPL scripts: `41_batch_pipeline_io`, `40_slippage_guard_io` (stable-only), and `39_cpmm_valid_8bit_io`.

## Spec-mode checks added

- `experiments/29_batch_pipeline_spec.tau` parses in spec mode (composite gating).
- `experiments/30_slippage_guard_spec.tau` parses in spec mode (cooldown logic).
- `experiments/31_super_composite_spec.tau` parses in spec mode (full super gate).

## Composed trace (external join)

- `experiments/io/compose_super_trace.py` combines:
  - `batch_all_ok.out`
  - `price_stable.out`
  - `can_trade.out`
  into `super_all_ok.out`.
- Current composed result: `0, 0`.

- **43_supply_io** (`supply.out`, `supply_ok.out`):
  - supply `0, 10, 5, 65511`
  - ok `0, 1, 1, 0`.
