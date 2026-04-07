# ShapeForge Pokayoke Reasoning

## Baseline

Pokayoke is an advisory exact-in swap surface, not a consensus-critical settlement
rule. The current repo surface is spread across:

- `src/core/pokayoke_swap_guardrails.py`
- `src/core/pokayoke_swap_suggest.py`
- `src/agents/intent_signer.py`
- `tools/pokayoke/pokayoke_audit.py`

The strongest existing runtime boundary is the signer preflight: the exact-in
Pokayoke path can fail closed when the computed action exceeds
`pokayoke_max_action`.

## Working Model

```text
Φ := ⟨
  M = ZenoDEX,
  S = pokayoke_exact_in_swap_guardrails,
  A = operator(amount_in perturbation),
  T = promote the advisory guardrail slice honestly,
  V = reserve_in,reserve_out,amount_in,fee_bps,pending_volume_same_direction,confidence_bps,user_slippage_bps,slippage_options_bps,
  O = price_impact_preview, decide_swap_guardrails, suggest_amount_in_exact_in_cpmm, signer_preflight,
  G = positive_amount, bounded_confidence, valid_slippage_domain, signer_max_action,
  Obs = price_impact_bps, required_slippage_bps, mev_status, action, suggested_amount_in,
  K = action severity order allow < confirm < typed_confirm < block,
  E = contract + implemented + tested_discovery,
  Gap = no exact-out Pokayoke, no formal monotonicity law, heuristic marker audit only,
  N = action severity is not monotone in amount_in,
  Δ = add the slice, preserve the falsifier, and classify already-covered interlocks separately from real gaps
⟩
```

## What Improved

The repo now exposes the Pokayoke slice explicitly in ShapeForge and preserves a
real falsifier instead of relying on a vague warning in one helper comment.

Bounded brute-force found a concrete adjacent-amount witness:

- `reserve_in = reserve_out = 500`
- `fee_bps = 0`
- `pending_volume_same_direction = 0`
- `confidence_bps = 9000`
- `user_slippage_bps = 10`
- `slippage_options_bps = [10, 50, 100, 300, 500]`

Observed actions:

- `amount_in = 20` -> `typed_confirm` with `("high_price_impact",)`
- `amount_in = 21` -> `confirm` with `("moderate_price_impact",)`
- `amount_in = 23` -> `typed_confirm` with `("mev_conflict", "high_price_impact")`

That means the action lattice is not monotone in `amount_in`, even on adjacent
inputs in a fixed pool/adversary context. The current bounded probe schedule in
`src/core/pokayoke_swap_suggest.py` is therefore the honest posture; binary
search would be unsound unless we first isolate a smaller monotone sub-surface.

The audit surface is sharper too. `tools/pokayoke/pokayoke_audit.py` now marks
whether a failure mode is:

- `covered`
- `partial`
- `signal_only`
- `uncovered`

That prevents already-covered interlocks from being misread as missing gaps when
the marker corpus is current.

## Pokayoke Improvements Found With ShapeForge

Current highest-leverage improvements:

1. Keep the exact-in advisory slice explicit and bounded; do not overclaim it as
   a monotone optimizer.
2. Promote more negative knowledge into replayable witnesses whenever threshold
   aliasing or MEV-status flips change severity unexpectedly.
3. Separate true gaps from already-covered interlocks in the audit lane so the
   next Pokayoke work targets real missing barriers.
4. Add an exact-out Pokayoke boundary only if it has an equally explicit claim
   surface and deterministic evidence.

## Counterexample Mining And Lean Promotion Targets

### Counterexample Mining

Use bounded counterexample mining for the advisory surface, not as a proof label.
Best next campaigns:

1. mine adjacent-amount action flips near price-impact and MEV thresholds
2. cluster flips by reason transition (`high_price_impact -> moderate_price_impact`, `ok -> mev_conflict`, etc.)
3. derive a small counterexample corpus for regression tests and UI explainers

The repo now has a deterministic bounded miner for this lane:

- `tools/pokayoke/pokayoke_flip_miner.py`

Current preserved witness family in the fixed `500/500` zero-fee pool:

- `20 -> 21` drops from `typed_confirm` to `confirm`
- `22 -> 23` rises from `confirm` to `typed_confirm`

That is the right posture for Pokayoke today: mine and preserve small
falsifiers first, then decide which sub-surface is stable enough for Lean.

### Lean

Do not try to prove the full Pokayoke action surface first. The honest Lean
frontier is narrower:

1. prove local arithmetic laws for `price_impact_preview`
2. prove monotonicity only on subdomains where the MEV status is held fixed
3. prove that explicit severity comparisons are sound for the declared action
   order once the candidate surface is fixed

## Current Bound

The Pokayoke exact-in surface is now explicit as:

- a deterministic implemented guardrail decision
- a fail-closed signer preflight boundary
- a tested-discovery falsifier showing the action surface is not globally
  monotone in `amount_in`
- a sharper audit classification that distinguishes covered interlocks from real
  gaps

What remains outside the promoted claim:

- exact-out Pokayoke
- full optimization completeness
- any claim that guardrail severity is monotone in size
- any formal proof over the mixed MEV + price-impact decision surface
