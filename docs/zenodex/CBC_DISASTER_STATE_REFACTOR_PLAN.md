# CBC Disaster-State Refactor Plan

Status: proof-backed design boundary, runtime bridge still open.

This document records the correct-by-construction refactor direction for the
highest-impact remaining ZenoDEX disaster states. The public Lean boundary is:

```text
lean-mathlib/Proofs/CBCDisasterStateRefactors.lean
```

The proof file compiles as part of `Proofs` and gives scoped theorem targets
for gross margin, ADL, oracle typestate, validated intents, uniform clearing,
checked route settlement, ceiling fees, liquidation dust thresholds, and
stability-pool reward cooldown. It also includes route acyclicity, graceful
oracle-degradation margin rules, and pessimistic dual-oracle routing.

## Prime Directive

Invalid states should be inadmissible before optimization, settlement, or
liquidation logic runs.

```text
RawInput -> ValidDomainObject or Reject
ValidState x ValidCommand -> ValidState
RiskyCommand requires ActiveOracleWindow
RouteSettlement requires checker proofs
```

The practical effect is that large disaster searches are replaced by small
constructor and checker obligations.

## 1. Gross Margin For Partial Liquidation

Net-margin accounting can certify an exactly offsetting account as safe, then
make it unsafe when one leg is partially closed. The Lean witness is:

```text
net_margin_partial_close_trap
```

Gross-margin accounting avoids this trap for leg reductions:

```text
gross_margin_short_reduction_monotone
gross_margin_long_reduction_monotone
```

Runtime direction:

- maintenance checks for partially liquidatable perps accounts must use gross
  exposure or a stronger risk envelope;
- net exposure may remain a UX display or a capital-efficiency metric, but it
  must not authorize partial liquidation safety by itself;
- regression tests should include the offsetting-position witness.

Residual gap: the Lean model is real-valued and abstract. Runtime needs an
integer fixed-point bridge for the exact perps account representation.

## 2. ADL As A Solvent Typestate

The standard overflow model admits bad-debt growth:

```text
standard_loss_creates_bad_debt
```

The CBC ADL model omits a bad-debt field and requires an admissible haircut
command:

```text
ADLCommand.overflowCovered
adl_bad_debt_unrepresentable
adl_haircut_is_covered
```

Runtime direction:

- insurance overflow must enter an ADL or haircut path instead of accumulating
  protocol bad debt;
- the ADL command must prove the overflow is covered by available
  counterparty PnL or route to a separate governance recovery state;
- if coverage is not available, the system must freeze the market or enter a
  bounded recovery mode rather than silently minting bad debt.

Residual gap: the current proof establishes the constructor shape. It does not
prove production fairness, queue ordering, socialized loss policy, or legal and
governance acceptability of ADL.

## 3. Oracle Typestate Circuit Breaker

Oracle lag greater than the active window should change which commands can be
constructed.

```text
ActiveOracleWindow -> risky actions may run
StaleOracleWindow -> only safeExit, repay, freeze
```

The Lean boundary proves:

```text
stale_blocks_geometric_funding
stale_blocks_liquidation
active_window_allows_risky_actions
```

Runtime direction:

- liquidations and geometric funding must require an `ActiveOracleWindow`
  receipt;
- stale oracle state should still be representable, but only with safe
  recovery commands;
- UI and API surfaces should expose stale/frozen state explicitly.

Residual gap: production needs a parser/checker bridge from oracle receipts and
epochs into `ActiveOracleWindow` or `StaleOracleWindow`.

## 4. Boundary Structural Validation

Raw bytes and untrusted dictionaries should not reach settlement logic.

```text
RawIntent -> ValidIntent or Reject
```

The Lean boundary proves:

```text
valid_intent_has_nonzero_amount
valid_intent_no_self_swap
```

Runtime direction:

- parse exactly once at the trust boundary;
- validate amount, asset IDs, nonce, bounds, units, and vector lengths;
- internal APIs should consume typed domain values rather than raw payloads;
- malformed offset, zero-amount, self-swap, and phantom-liquidity states should
  be rejected before solver or settlement code runs.

Residual gap: this needs a concrete Python/Rust domain-object adapter and
negative tests for malformed serialized inputs.

## 5. Uniform Batch Clearing

Uniform clearing shifts the MEV claim from sequence bounds to permutation
invariance.

```text
same multiset of intents -> same aggregate receipt
```

The Lean boundary proves:

```text
uniform_clearing_permutation_invariant
```

Runtime direction:

- direct sequential execution should be unavailable in adversarial production
  paths;
- settlement should consume batch receipts, not miner/user ordering;
- clearing should use an average clearing price derived from the batch net
  execution unless a separate budget funds marginal-price equalization.

Residual gap: batch-boundary MEV, censorship, solver withholding, and inclusion
fairness remain separate protocol obligations.

## 6. Solver-Checker Route Settlement

The solver may optimize. The checker authorizes safety.

```text
CheckedRouteSettlement :=
  kBefore <= kAfter
  inputSum = expectedInput
  userMinOut <= outputAmount
```

The Lean boundary proves:

```text
checked_route_blocks_user_min_violation
checked_route_blocks_k_decrease
checked_route_has_exact_input_sum
```

Runtime direction:

- optimality should live outside the settlement trusted base;
- the settlement trusted base should verify safety, authorization, replay,
  exact input aggregation, user minima, and conservation;
- suboptimal solver output should be rejected only when it violates safety or
  declared policy. Otherwise it is a price-quality or UX issue.

Residual gap: the runtime checker must bind the actual settlement receipt to
these fields, and large batches need aggregate proofs or Merkle/FIRE receipts
so checking does not become an unbounded loop.

## 7. Ceiling Fees For Micro-Trades

Floor-division fees admit a positive micro-trade that pays zero fee whenever
the fee tier is below the denominator:

```text
floor_fee_bypass_exists_for_sub_denominator_bps
```

Ceiling fees close that bypass for every positive amount and positive fee tier:

```text
ceil_fee_positive
```

Runtime direction:

- value-moving swap paths should use the existing ceil-fee policy or reject
  trades below a minimum notional;
- fee calculation should be centralized so adapters cannot silently reintroduce
  floor fees;
- regression tests should cover `amount = 1` under every public fee tier.

Residual gap: the proof covers arithmetic shape. Runtime still needs adapter
parity tests for every path that computes or verifies fees.

## 8. Liquidation Dust Thresholds

Partial liquidation without a dust threshold can leave a one-unit residual:

```text
dust_griefing_witness
```

The CBC boundary rejects any partial liquidation whose remaining debt is
positive but below `minDebt`:

```text
valid_liquidation_prevents_dust
```

Runtime direction:

- vault and perps partial-liquidation code should enforce
  `remaining = 0 or minDebt <= remaining`;
- liquidation quote previews should expose when a requested partial close would
  be forced to full close;
- tests should include the one-unit debt witness.

Residual gap: the proof is debt-only. Runtime must also bind collateral seizure,
fees, oracle price, and liquidation reward to the same checked receipt.

## 9. Stability-Pool Reward Cooldown

Without cooldown, a same-epoch depositor can extract positive reward share from
an imminent reward event:

```text
jit_deposit_extracts_positive_reward
```

The CBC cooldown model routes same-epoch deposits into `pendingDeposits`, so
they have zero active shares for the current reward:

```text
cooldown_pending_deposit_extracts_zero_reward
```

Runtime direction:

- zUSD stability-pool deposits should become reward-active only after the
  configured epoch delay;
- reward distribution must use active shares only;
- withdrawal and activation ordering should be explicit in the receipt.

Residual gap: production still needs epoch transition rules, withdrawal
cooldowns, and reward-index accounting proofs.

## 10. Acyclic Route Typestate

Route cycles should be rejected as a structural property of a route, rather
than handled by gas limits, max-hop heuristics, or post-execution unwind logic.

```text
AcyclicRoute.path.Nodup
```

The Lean boundary proves:

```text
acyclic_route_length_equals_unique_pool_count
acyclic_route_no_revisit
```

Runtime direction:

- route constructors should reject repeated pool IDs before quote or settlement;
- settlement should consume an acyclic route object or receipt, rather than a
  raw list of pools;
- cyclic routes can remain available to offline search tools, but they must not
  enter the value-moving execution path without a separate, explicit proof.

Residual gap: this proves route-shape acyclicity. Runtime still needs a
parser/checker bridge from encoded route receipts to the `Nodup` route model,
plus tests for repeated-pool paths.

## 11. Graceful Oracle Degradation

A stale oracle need not force a single global halt. A dynamic margin function can
make new risk progressively harder while keeping safe recovery commands
available.

```text
margin(t) := min(maxMargin, baseMargin + penaltyPerEpoch * staleness)
```

The Lean boundary proves:

```text
dynamic_margin_ratio_monotone
dynamic_margin_ratio_capped
dynamic_margin_ratio_eventually_freezes
```

Staler oracle evidence never lowers the margin requirement. With a positive
penalty, sufficiently stale evidence reaches the configured freeze boundary.

Runtime direction:

- stale oracle modes should distinguish risk-increasing actions from
  risk-reducing actions;
- risk-increasing actions can require dynamic-margin satisfaction before the
  active-window hard stop;
- once the cap is reached, new debt or leverage issuance should be effectively
  unavailable while repay, close, freeze, and safe-exit paths remain explicit.

Residual gap: this is a margin-shape theorem. Production still needs integer
unit binding, oracle receipt freshness binding, and per-action command gates.

## 12. Pessimistic Dual-Oracle Routing

Multiple oracle sources are useful for fault tolerance, but raw averaging or
fail-open fallback can create split-brain arbitrage when one source lags the
other. The safe CBC shape is worst-case pricing:

```text
collateral_value := collateral * min(collateralPriceA, collateralPriceB)
debt_value       := debt       * max(debtPriceA, debtPriceB)
```

The Lean boundary proves:

```text
pessimistic_collateral_no_overvalue
pessimistic_debt_no_undervalue
pessimistic_health_dominates_price_pair
pessimistic_health_dominates_both_oracles
```

If an account passes the pessimistic check, it also passes under each oracle's
own collateral/debt price pair. This blocks cherry-picking the lagging oracle
for borrowing power or debt understatement.

Runtime direction:

- dual-oracle borrowing, liquidation, and cross-module settlement paths should
  use min collateral price and max debt price where both values are exposed;
- if divergence or epoch lag exceeds policy, risk-increasing actions should
  move to the stale/degraded path rather than averaging prices;
- the receipt should record each oracle price, observed epoch, divergence bound,
  lag bound, selected pessimistic prices, and action-specific consumer profile.

Residual gap: the theorem is real-valued and model-level. Runtime still needs
fixed-point integer bridges and exact wiring for zUSD/perps/settlement surfaces.

## Promotion Checklist

A CBC lane can be promoted from design boundary to production claim only when:

- the constructor/checker is implemented in the runtime path;
- every unsafe raw state is rejected before internal use;
- positive and negative tests cover the disaster witness;
- Lean, ESSO, Tau, or FIRE evidence covers the exact promoted claim;
- docs state the remaining external assumptions.

Current evidence:

```text
gross margin trap: proved in scoped Lean model
ADL bad-debt inadmissibility: proved as constructor shape
oracle stale risky-action block: proved as typestate model
validated intent nonzero/self-swap rejection: proved as constructor shape
uniform clearing permutation invariance: proved for aggregate receipt model
route safety checker: proved for checked settlement record
ceil fee: proved positive for positive trade and fee tier
liquidation dust threshold: proved no positive sub-threshold debt remains
stability-pool cooldown: proved same-epoch pending deposit extracts zero reward
acyclic routing: proved no repeated pool visit in the route typestate
graceful oracle degradation: proved monotone capped margin with eventual freeze
pessimistic dual-oracle routing: proved min-collateral/max-debt health dominance
```

This reduces the proof frontier. It does not yet finish the runtime refactor.
