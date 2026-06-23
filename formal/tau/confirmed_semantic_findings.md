# Confirmed Tau Semantic Findings

This packet records only source-backed semantic findings from the current
recommended hard-spec review. Each item below is supported directly by the Tau
spec text. It is intentionally narrower than
`formal/tau/remaining_execution_hard_specs.review.md`, which still contains
broader suspicion-oriented review notes.

Finding tags:

- `comment/name drift`
- `actual predicate logic mismatch`
- `arithmetic model narrowing`
- `ungated suboutput exposure`

## Confirmed Findings

### `sandwich_detection_v1`

- `actual predicate logic mismatch`
  The prose says the spec detects price movements "around target tx" and
  "net attacker profit", but the implemented predicate is only
  `front_impact_ok(i1, i2)` and `back_impact_ok(i3, i4)` under `params_ok`.
  There is no predicate relating the target leg to the surrounding legs, and
  there is no profit input or profit term anywhere in the file.
  Refs:
  [`src/tau_specs/recommended/sandwich_detection_v1.tau:7`](../../src/tau_specs/recommended/sandwich_detection_v1.tau#L7),
  [`src/tau_specs/recommended/sandwich_detection_v1.tau:10`](../../src/tau_specs/recommended/sandwich_detection_v1.tau#L10),
  [`src/tau_specs/recommended/sandwich_detection_v1.tau:52`](../../src/tau_specs/recommended/sandwich_detection_v1.tau#L52),
  [`src/tau_specs/recommended/sandwich_detection_v1.tau:57`](../../src/tau_specs/recommended/sandwich_detection_v1.tau#L57),
  [`src/tau_specs/recommended/sandwich_detection_v1.tau:60`](../../src/tau_specs/recommended/sandwich_detection_v1.tau#L60)

### `sandwich_window_guard_v1`

- `comment/name drift`
  `window_blocks (i6)` is declared as an updatable parameter and is consumed in
  the formulas, but the stream-mapping comment never defines `i6`.
  Refs:
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:4`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L4),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:17`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L17),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:56`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L56)

- `actual predicate logic mismatch`
  The file says it detects reversal patterns like `up-target-down` or
  `down-target-up`, but the logic only checks two independent absolute-move
  bounds, `i1 -> i2` and `i3 -> i4`. No predicate enforces opposite directions
  or otherwise relates the pre-target move to the post-target move.
  Refs:
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:7`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L7),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:9`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L9),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:44`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L44),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:49`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L49),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:52`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L52)

- `actual predicate logic mismatch`
  `window_blocks` is semantically inert beyond the positivity check `win > 0`.
  It does not affect `pre_move_ok`, `post_move_ok`, or the aggregate detection
  condition except through `params_ok`.
  Refs:
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:35`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L35),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:36`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L36),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:39`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L39),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:52`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L52)

- `ungated suboutput exposure`
  `o2` and `o3` are not gated by `params_ok`, while `o1` and `o4` are. Invalid
  params can therefore yield passing suboutputs.
  Refs:
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:56`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L56),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:58`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L58),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:60`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L60),
  [`src/tau_specs/recommended/sandwich_window_guard_v1.tau:62`](../../src/tau_specs/recommended/sandwich_window_guard_v1.tau#L62)

### `slippage_bounds_v2`

- `comment/name drift`
  The header says `max_price_impact_bps (i6)`, but the stream mapping and the
  formulas use `i6` as `price_after` and `i7` as the impact-bps input.
  Refs:
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:4`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L4),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:19`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L19),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:20`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L20),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:67`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L67),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:71`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L71)

- `actual predicate logic mismatch`
  The title and purpose promise explicit `min/max` output bounds and a
  "maximum output ceiling", but `output_ok` only checks `actual >= min_out`
  plus a lower-bound slippage inequality. There is no `max_output` input and no
  upper-bound predicate.
  Refs:
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:1`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L1),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:9`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L9),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:49`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L49),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:52`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L52),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:55`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L55)

- `ungated suboutput exposure`
  `o2` and `o3` omit `params_ok` even though `o4` includes it. This is not just
  theoretical: `price_ok(0)` is false, so `o1` fails on zero prices, but
  `impact_ok(0, 0, impact_bps)` is true by the equality branch, so `o3` can
  still be `1`.
  Refs:
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:39`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L39),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:46`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L46),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:58`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L58),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:60`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L60),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:67`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L67),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:69`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L69),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:71`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L71),
  [`src/tau_specs/recommended/slippage_bounds_v2.tau:73`](../../src/tau_specs/recommended/slippage_bounds_v2.tau#L73)

### `treasury_spend_categories_v2`

- `comment/name drift`
  The header says the immutable invariant is `spend <= category cap AND total cap`,
  but the file has only per-category caps. There is no total-cap input and no
  total-cap predicate anywhere in the formulas.
  Refs:
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:5`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L5),
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:17`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L17),
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:47`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L47),
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:53`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L53)

- `ungated suboutput exposure`
  `o2` is not gated by `category_valid`. For an unknown category, every
  `cap_for_*` helper is vacuously true because each one starts with
  `(cat != known_category) || ...`, so `o2` can be `1` while `o1` and `o4`
  are `0`.
  Refs:
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:38`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L38),
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:41`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L41),
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:42`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L42),
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:43`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L43),
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:44`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L44),
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:59`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L59),
  [`src/tau_specs/recommended/treasury_spend_categories_v2.tau:63`](../../src/tau_specs/recommended/treasury_spend_categories_v2.tau#L63)

### `usage_rebate_tiered_v1`

- `actual predicate logic mismatch`
  The header says rebates require usage and the purpose says "NO PASSIVE
  PAYOUTS", but `is_tier0(usage, t1)` is `usage < t1`, so zero usage still
  matches tier 0 whenever `t1 > 0`. Because `rates_ok` does not require
  `r0 = 0`, the file permits a positive tier-0 rebate for zero usage.
  Refs:
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:5`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L5),
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:8`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L8),
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:32`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L32),
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:38`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L38),
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:41`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L41)

- `ungated suboutput exposure`
  `o3` reports `tier_match_ok` without requiring `thresholds_ok` or `rates_ok`,
  even though `o4` requires both. Invalid thresholds or invalid rebate-rate
  schedules can therefore still yield a passing tier-match suboutput.
  Refs:
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:29`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L29),
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:32`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L32),
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:41`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L41),
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:44`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L44),
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:52`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L52),
  [`src/tau_specs/recommended/usage_rebate_tiered_v1.tau:54`](../../src/tau_specs/recommended/usage_rebate_tiered_v1.tau#L54)

### `limit_order_bounds_v1`

- `ungated suboutput exposure`
  `o3` reports `bounds_ok` without requiring `params_ok`, even though `o4`
  requires both. Out-of-range bps or unsafe price magnitudes can therefore
  still yield a passing bounds suboutput.
  Refs:
  [`src/tau_specs/recommended/limit_order_bounds_v1.tau:38`](../../src/tau_specs/recommended/limit_order_bounds_v1.tau#L38),
  [`src/tau_specs/recommended/limit_order_bounds_v1.tau:49`](../../src/tau_specs/recommended/limit_order_bounds_v1.tau#L49),
  [`src/tau_specs/recommended/limit_order_bounds_v1.tau:52`](../../src/tau_specs/recommended/limit_order_bounds_v1.tau#L52),
  [`src/tau_specs/recommended/limit_order_bounds_v1.tau:60`](../../src/tau_specs/recommended/limit_order_bounds_v1.tau#L60),
  [`src/tau_specs/recommended/limit_order_bounds_v1.tau:62`](../../src/tau_specs/recommended/limit_order_bounds_v1.tau#L62)

### `vote_weight_v1`

- `actual predicate logic mismatch`
  The title and purpose present this as time-weighted voting where longer lock
  means higher voting power, but the implemented `weight_math_ok` only checks:
  lower bound, upper bound, lock-duration cap, and the two endpoint conditions
  at `lock_dur = 0` and `lock_dur = max_dur`. There is no predicate linking
  intermediate `lock_duration` values to intermediate weights.
  Refs:
  [`src/tau_specs/recommended/vote_weight_v1.tau:1`](../../src/tau_specs/recommended/vote_weight_v1.tau#L1),
  [`src/tau_specs/recommended/vote_weight_v1.tau:5`](../../src/tau_specs/recommended/vote_weight_v1.tau#L5),
  [`src/tau_specs/recommended/vote_weight_v1.tau:7`](../../src/tau_specs/recommended/vote_weight_v1.tau#L7),
  [`src/tau_specs/recommended/vote_weight_v1.tau:8`](../../src/tau_specs/recommended/vote_weight_v1.tau#L8),
  [`src/tau_specs/recommended/vote_weight_v1.tau:67`](../../src/tau_specs/recommended/vote_weight_v1.tau#L67)

- `ungated suboutput exposure`
  `o3` reports `weight_math_ok` without requiring `params_ok`, even though `o4`
  requires both. Invalid token amounts, invalid multiplier bounds, or unsafe
  multiplication ranges can therefore still yield a passing weight-math
  suboutput.
  Refs:
  [`src/tau_specs/recommended/vote_weight_v1.tau:50`](../../src/tau_specs/recommended/vote_weight_v1.tau#L50),
  [`src/tau_specs/recommended/vote_weight_v1.tau:67`](../../src/tau_specs/recommended/vote_weight_v1.tau#L67),
  [`src/tau_specs/recommended/vote_weight_v1.tau:70`](../../src/tau_specs/recommended/vote_weight_v1.tau#L70),
  [`src/tau_specs/recommended/vote_weight_v1.tau:78`](../../src/tau_specs/recommended/vote_weight_v1.tau#L78),
  [`src/tau_specs/recommended/vote_weight_v1.tau:80`](../../src/tau_specs/recommended/vote_weight_v1.tau#L80)

### `protocol_token_v1` (recommended copy)

- `arithmetic model narrowing`
  The claim here applies to
  [`src/tau_specs/recommended/protocol_token_v1.tau`](../../src/tau_specs/recommended/protocol_token_v1.tau),
  not to the separate root copy at
  [`src/tau_specs/protocol_token_v1.tau`](../../src/tau_specs/protocol_token_v1.tau).
  The recommended file explicitly states "no carry/borrow" and the helper
  formulas enforce exactly that: `add_32` never propagates low-limb carry into
  `sum_hi`, and `sub_32` requires both limbs to be independently nondecreasing
  before subtracting.
  Refs:
  [`src/tau_specs/recommended/protocol_token_v1.tau:43`](../../src/tau_specs/recommended/protocol_token_v1.tau#L43),
  [`src/tau_specs/recommended/protocol_token_v1.tau:44`](../../src/tau_specs/recommended/protocol_token_v1.tau#L44),
  [`src/tau_specs/recommended/protocol_token_v1.tau:46`](../../src/tau_specs/recommended/protocol_token_v1.tau#L46)

- `arithmetic model narrowing`
  Under ordinary 32-bit arithmetic, the transition
  `0x0000ffff + 0x00000001 = 0x00010000` is valid, but the recommended
  `add_32` rejects it because the low limb wraps to `0x0000`, so
  `sum_lo >= a_lo` fails. Likewise,
  `0x00010000 - 0x00000001 = 0x0000ffff` is valid 32-bit subtraction, but the
  recommended `sub_32` rejects it because `a_lo >= b_lo` fails. The root copy
  at
  [`src/tau_specs/protocol_token_v1.tau:43`](../../src/tau_specs/protocol_token_v1.tau#L43)
  and
  [`src/tau_specs/protocol_token_v1.tau:45`](../../src/tau_specs/protocol_token_v1.tau#L45)
  does propagate carry and borrow, so this narrowing is path-specific.

### `protocol_token_policy_v1`

- `arithmetic model narrowing`
  The policy file uses the same restricted helper model as the recommended
  `protocol_token_v1`: no carry propagation in `add_32` and no low-limb borrow
  in `sub_32`. `token_ok` therefore keeps the composite policy in the same
  narrowed arithmetic model.
  Refs:
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:35`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L35),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:36`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L36),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:38`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L38),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:44`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L44),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:50`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L50)

- `comment/name drift`
  The header says the file combines `protocol_token_v1` transition validity with
  the underflow guard, but `o1` is actually defined from a locally rebuilt
  `token_ok` with locally rebuilt transition predicates. Because the repo also
  contains a separate root `protocol_token_v1.tau` with different arithmetic,
  that header is path-ambiguous and semantically misleading to a reviewer.
  Refs:
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:3`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L3),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:4`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L4),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:44`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L44),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:46`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L46),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:48`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L48),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:50`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L50),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:60`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L60)

- `actual predicate logic mismatch`
  `underflow_ok` uses lexicographic `value_gte_32`, which is compatible with
  ordinary 32-bit ordering, but `policy_ok` still conjuncts it with `token_ok`,
  which uses the stricter no-carry/no-borrow helpers. The underflow guard
  therefore does not restore full 32-bit semantics to the composite policy.
  Refs:
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:50`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L50),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:52`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L52),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:54`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L54),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:55`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L55),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:56`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L56),
  [`src/tau_specs/recommended/protocol_token_policy_v1.tau:62`](../../src/tau_specs/recommended/protocol_token_policy_v1.tau#L62)

### `tokenomics_fee_split_32_v1`

- `comment/name drift`
  `o1 = share_bps_ok` sounds like per-share basis-point validation, but the
  implemented check is only `b1 + b2 + b3 = 10000`. There is no per-share
  `<= 10000` bound.
  Refs:
  [`src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau:5`](../../src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau#L5),
  [`src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau:17`](../../src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau#L17),
  [`src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau:28`](../../src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau#L28),
  [`src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau:40`](../../src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau#L40)

- `ungated suboutput exposure`
  The file is labeled a `32-bit safe variant`, but `safe_range_ok` is applied
  only at `o4`. The suboutputs `o2` and `o3` can therefore report success
  without the safe-range guard.
  Refs:
  [`src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau:1`](../../src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau#L1),
  [`src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau:36`](../../src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau#L36),
  [`src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau:41`](../../src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau#L41),
  [`src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau:43`](../../src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau#L43),
  [`src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau:44`](../../src/tau_specs/recommended/tokenomics_fee_split_32_v1.tau#L44)

### `tokenomics_usage_rebate_32_v1`

- `comment/name drift`
  The header describes a usage gate plus cap and bps math, but `usage_ok`
  includes an extra constraint on `rebate`, namely `rebate <= score`. That
  extra coupling is not described in the stream mapping or the rule comment.
  Refs:
  [`src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau:5`](../../src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau#L5),
  [`src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau:16`](../../src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau#L16),
  [`src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau:20`](../../src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau#L20),
  [`src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau:29`](../../src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau#L29),
  [`src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau:40`](../../src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau#L40)

- `ungated suboutput exposure`
  The file is labeled a `32-bit safe variant`, but `safe_range_ok` is only part
  of `o4`. The suboutputs `o2` and `o3` can succeed without the safe-range
  guard.
  Refs:
  [`src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau:1`](../../src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau#L1),
  [`src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau:36`](../../src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau#L36),
  [`src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau:42`](../../src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau#L42),
  [`src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau:43`](../../src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau#L43),
  [`src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau:45`](../../src/tau_specs/recommended/tokenomics_usage_rebate_32_v1.tau#L45)
