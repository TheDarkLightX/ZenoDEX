# Tau Spec Experiments

Working experiments demonstrating Tau Language syntax for DEX specifications.

## Key Findings

### What Works
1. **Single-line definitions** - Predicates must be defined on one line
2. **Typed parameters** - All predicate params need explicit types: `foo(x : bv[16]) := ...`
3. **Bitvector types** - `bv[16]`, `bv[64]` work for integer math
4. **Hex constants** - Use `{ #x0000 }:bv[16]` syntax
5. **Boolean output** - Use `sbf` type for true/false: `o1[t]:sbf = 1:sbf`

### Why Original Specs Failed
- **Unresolved symbols**: Predicates called without defined types
- **Incomplete specs**: Some ended with `T.` instead of proper `always` statements
- **Multi-line definitions**: Tau requires single-line predicate definitions

## Experiments (all pass)

| File | Purpose |
|------|---------|
| `01_basic_echo.tau` | Simplest spec - output mirrors input |
| `02_sbf_simple.tau` | Boolean function basics |
| `03_bitvector_basic.tau` | bv[16] type and hex constants |
| `04_bitvector_compare.tau` | Comparisons: `>`, `>=`, `<` |
| `05_multi_predicate.tau` | Combining predicates with `&&` |
| `06_32bit_pair.tau` | Using hi:lo pairs for 32-bit values |
| `07_cpmm_basic.tau` | CPMM swap validation |
| `08_console_io.tau` | Console I/O testing |
| `09_bv64_test.tau` | 64-bit bitvectors |
| `10_batching_canonical.tau` | 2-intent canonical ordering |
| `11_batching_4_intents.tau` | 4-intent strictly increasing check |
| `12_balance_safety.tau` | Balance non-negativity checks |
| `13_dex_complete.tau` | Full DEX CPMM spec |
| `26_cpmm_valid_hilo_spec.tau` | CPMM validity (hi:lo, hi=0 guard) |
| `27_risk_budget_spec.tau` | Risk budget state machine (bv[16]) |
| `28_balance_hilo_spec.tau` | 32-bit balance update using hi:lo carry/borrow |
| `29_batch_pipeline_spec.tau` | Composite: canonical + no-sandwich + stable + CPMM |
| `30_slippage_guard_spec.tau` | Slippage guard with cooldown (temporal) |
| `31_super_composite_spec.tau` | Full composite gate incl. risk and CPMM |
| `32_oracle_nonce_spec.tau` | Oracle freshness + nonce replay guard |
| `33_supply_invariant_spec.tau` | Supply invariants (mint/burn/cap) |
| `34_auction_twap_risk_spec.tau` | Auction clearing + TWAP guard + risk budget |
| `35_auction_twap_risk_cpmm_spec.tau` | Auction + TWAP + risk + CPMM composite |
| `40_worldclass_dex_gate.tau` | Warmup-gated worldclass composite gate |
| `35_circuit_breaker.tau` | Circuit breaker with 3-step hysteresis |
| `36_median_oracle.tau` | Median-of-3 oracle validation |
| `37_adaptive_fee.tau` | Adaptive fee tiers based on volatility |
| `38_composite_dex_gate.tau` | Composite gate: breaker + oracle + fee + sandwich |
| `39_frontier_composite_dex.tau` | Frontier composite: auction + TWAP + median + breaker + fee + sandwich + CPMM + risk + supply |
| `40_volatility_bucket_gate.tau` | Volatility buckets + drift guard + breaker + fee tiers + CPMM + nonce + risk |
| `41_liquidity_shock_guard.tau` | Liquidity shock guard + CPMM hi/lo + median + stability + risk |
| `101_fee_flywheel_split.tau` | Fee conservation + minimum burn/reserve commitments |
| `102_buyback_burn_sink.tau` | Supply-before/after burn using 32-bit hi:lo |
| `103_stake_lock_tier.tau` | Lock-based withdrawal + tier assignment |
| `104_loyalty_fee_discount.tau` | Tier-based fee discounts with bounds |
| `105_insurance_buffer.tau` | Insurance buffer update and minimum coverage |
| `106_ecosystem_composite.tau` | Composite gate for DEX + value + stickiness |
| `107_exit_tax_lock.tau` | Early-exit tax with cross-mult check |
| `108_protocol_owned_liquidity_floor.tau` | Minimum protocol-owned liquidity floor |

## Running Tests

```bash
# Test single spec
./external/tau-lang/build-Release/tau experiments/01_basic_echo.tau --severity error --charvar false -x </dev/null

# Test all experiments
for spec in experiments/*.tau; do
  echo -n "$(basename $spec)... "
  if timeout 3 ./external/tau-lang/build-Release/tau "$spec" --severity error --charvar false -x </dev/null >/dev/null 2>&1; then
    echo "OK"
  else
    echo "FAIL"
  fi
done
```

## Template for New Specs

```tau
# Predicate definitions (single line, typed params)
predicate_name(param1 : bv[16], param2 : bv[16]) := (param1 > param2).

# Main spec using always keyword
always (o1[t]:sbf = 1:sbf <-> predicate_name(i1[t]:bv[16], i2[t]:bv[16])).
```

## File I/O Experiments (REPL Scripts)

Additional end-to-end I/O checks live in `experiments/io/`. These are REPL scripts that must be **piped** into Tau (not passed as a spec file). See `experiments/io/VERIFICATION.md` for exact commands and recorded outputs.
