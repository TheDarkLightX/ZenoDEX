---
title: ZENODEX_AUTOTRADER_CLIENT_POLICY_SURFACE
type: note
permalink: autonomous-tau-dex-review/docs/zenodex/zenodex-autotrader-client-policy-surface
---

# ZenoDEX AutoTrader Client Policy Surface

## Purpose

This note makes the client-side autotrader split explicit:

- strategy logic the user actually wants
- hard local guards the client should fail closed on
- assurance artifacts that prove what was compiled and signed

## Rule Split

```text
ClientAutoTraderPolicy := strategy_logic ∧ hard_local_guards ∧ assurance_artifacts
```

Standard reading:
- strategy logic describes what the user is trying to do,
- hard local guards describe the fail-closed limits the client should enforce,
- assurance artifacts describe what was compiled, checked, or signed.

Practical consequence: the autotrader can show and audit user intent separately from local safety posture.

## Preferred Authoring Layer

```text
UserRuleBundle -> compile -> StrategyIR -> ClientPolicySurface -> SignedClientPolicyBundle
```

Standard reading:
- the user should author a higher-level rule bundle,
- the client compiles that bundle into the existing `StrategyIR`,
- then the existing client policy surface and signed client bundle carry the assurance artifacts.

Practical consequence: the user-facing authoring format no longer needs to expose raw strategy-IR fields directly.

Implementation:
- `src/agents/autotrader_user_rule_bundle.py`

The current `v1` user bundle is still intentionally narrow, but it now supports two authoring families:
- swap-execution mode: `dca_swap_exact_in`
- trigger/order-intent modes: `stop_loss_order_intent` / `take_profit_order_intent`
- optional DCA presets: `capital_preservation_dca` / `conservative_dca` / `balanced_dca` / `price_discipline_dca` / `high_throughput_dca`
- optional trigger presets: `protective_stop_loss` / `disciplined_take_profit`
- market pair: `asset_in`, `asset_out`
- sizing rule: `fixed_order_size`
- DCA cadence rule: `cadence_epochs`
- trigger rule for order-intent modes: `trigger_price`
- budget rule: `per_window_max`, `lifetime_max`
- risk rule: `max_slippage_bps`, `max_oracle_staleness_epochs`, `require_quote_receipts`
- window rule: `valid_from_epoch`, `valid_until_epoch`, `min_order_spacing_epochs`
- controls: `kill_switch_enabled`, `max_live_orders`

Preset-authored strategies now also carry a reusable human-readable preset profile through the live report:
- `label`
- `optimize_for`
- `summary`
- `tradeoffs`
- `operating_profile`
- `guard_profile`

Practical consequence: the client can say what `conservative_dca` or `balanced_dca` is trying to optimize without reconstructing that meaning from raw limits.

This compiles into the same fail-closed signed client bundle lane that already has:
- hash pinning
- local guard evaluation
- owner signature verification
- live CLI and direct integration reject-path coverage

Current live execution posture:
- the authoring layer can now compile stop-loss and take-profit order-intent bundles
- the current live executor still only executes `dca_swap_exact_in` strategies
- non-DCA authored live inputs are rejected fail-closed with `unsupported_live_strategy_mode`
- the live report, shadow report, and preset metadata now expose one explicit support matrix across `compile`, `shadow`, and `live` surfaces
- direct compiled-strategy client policy surfaces now preserve `source_form=compiled_strategy_ir` instead of leaving that origin implicit

Preset tooling now also supports:
- list / describe / compare across both DCA and trigger presets
- recommendation from guard criteria plus optional `desired_user_rule_mode`
- preset catalog filters for `--only-live-supported-presets` and `--only-fail-closed-presets`
- optional recommendation hard filter `--require-live-supported` when the user only wants presets the current executor can run
- preset metadata now states required authoring parameters and whether current live execution is supported or fail-closed

## Current Surface

Implementation:
- `src/agents/autotrader_client_policy_surface.py`
- `src/agents/autotrader_local_guard_evaluator.py`
- `src/agents/autotrader_client_policy_bundle.py`

The current surface exports three top-level sections:

1. `strategy_logic`
- template
- asset universe
- allowed actions
- template parameters

2. `hard_local_guards`
- notional caps
- risk limits
- strategy window
- controls

3. `assurance_artifacts`
- Tau policy specs
- source form and optional `source_preset_id`
- source artifact hash
- Tau policy bundle hash
- signed policy artifact hash

## Design Rule

```text
hard_local_guard_violation -> client rejects_or_blocks_action
```

Standard reading: if a hard local guard is violated, the client fails closed.

Practical consequence: client automation stays user-controlled without becoming reckless.

## Scope Boundary

This surface is client-side only.

```text
client_policy_surface != protocol_validity_surface
```

Standard reading: this object helps the user client reason about strategy and safety; it does not define protocol-wide validity.

Practical consequence: this fits the ZenoDEX policy charter, where autotrader strategy stays off-protocol by default.

## Guard Evaluator

```text
GuardEvaluationOK <-> controls_ok ∧ slippage_ok ∧ provenance_ok ∧ oracle_freshness_ok ∧ execution_ok ∧ notional_budget_ok
```

Standard reading:
- the client-side guard evaluation passes exactly when every checked guard family passes,
- and unchecked optional families do not block the result.

Practical consequence: the client can explain a blocked action with stable family-level reason codes instead of a single opaque reject string.

The evaluator preserves existing guard/kernel reason strings where possible:
- `kill_switch_active`
- `slippage_limit_exceeded:...`
- `signal_packet_missing`
- `signal_quote_receipt_missing` / `signal_quote_receipt_invalid`
- `quote_receipt_stale:...`
- `strategy_window_not_open:...`
- `max_live_orders_reached:...`
- `per_order_limit_exceeded`
- `window_budget_exceeded`
- `lifetime_cap_exceeded:...`

## Portable Bundle

```text
PortableClientPolicyBundle <-> surface_hash_pinned ∧ optional_guard_evaluation_hash_pinned ∧ owner_signature_valid
```

Standard reading:
- the portable client policy bundle pins the client policy surface hash,
- optionally pins one concrete local guard evaluation,
- and must be signed by the strategy owner before the live path will accept it.

Practical consequence: a user can export a local automation policy as one replayable signed object instead of scattering strategy JSON, guard settings, and diagnostics across multiple files, and the live path now rejects unsigned bundles fail-closed.

Current bundle fields:
- `bundle_name`
- `built_at`
- `compiler_version`
- `client_policy_surface`
- `local_guard_evaluation`
- `signature`
- `signer_pubkey`


## Live Explanation Surface

```text
LiveExplanationSurface := user_rule_summary ∧ krr_explanation ∧ actionability_explanation ∧ actionability_summary
```

Standard reading:
- `user_rule_summary` says what the strategy intends,
- `krr_explanation` says why the KRR trusted or discounted it,
- `actionability_explanation` says what allowed or blocked the current action,
- `actionability_summary` compresses that into deterministic human-readable lines.

Practical consequence: dashboards and the CLI no longer need to reverse-engineer intent, trust posture, and blocking reasons from raw artifacts.

Current user-facing integration:
- `src/integration/autotrader_live.py`
- `tools/autotrader_live.py --text-summary`
- `tools/autotrader_live.py --list-user-rule-presets`
- `tools/autotrader_live.py --describe-user-rule-preset <preset_id>`
- `tools/autotrader_live.py --compare-user-rule-presets <left> <right>`
- `tools/autotrader_live.py --recommend-user-rule-preset ...criteria...`

Read-only preset inspection does not require live-preparation inputs or risk acknowledgement.

`--text-summary` keeps telemetry output in JSON, but emits a bounded human-readable summary on stdout for direct operator/client use.
