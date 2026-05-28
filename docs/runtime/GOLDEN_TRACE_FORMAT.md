# Golden Trace Format (v1)

A **golden trace** is a deterministic, replayable record of a transition
sequence produced by the **authoritative Python runtime**. Golden traces are
the conformance anchor for the Rust shadow runtime (`rust-runtime/`): replaying
the same `tx` list through Rust must reproduce every recorded `post_state_root`
and `receipt_hash` exactly, and reject the same inputs with the same reason
codes.

This document specifies version `1` of the format. The first kernel covered is
`fee_router` (protocol fee routing); the schema is intentionally generic so
later runtime surfaces (replay guards, balances, zUSD, batch clearing) reuse it
without change.

## Files & tools

| Path | Role |
|------|------|
| `tools/runtime/golden_trace_lib.py` | Shared schema + apply/replay logic (the source of truth). |
| `tools/runtime/export_golden_trace.py` | Export a trace from the Python runtime. |
| `tools/runtime/replay_golden_trace.py` | Replay/verify a trace against the Python runtime. |
| `tools/runtime/rust_shadow_replay.py` | Replay a trace through the Rust shadow and diff vs. Python. |
| `tests/runtime/golden_traces/*.json` | Committed corpora (e.g. `smoke.json`). |

## Acceptance commands

```bash
python3 tools/runtime/export_golden_trace.py --out tests/runtime/golden_traces/smoke.json
python3 tools/runtime/replay_golden_trace.py tests/runtime/golden_traces/smoke.json
python3 tools/runtime/rust_shadow_replay.py  tests/runtime/golden_traces/smoke.json
pytest tests/runtime -q
```

## Schema

```json
{
  "version": 1,
  "kernel": "fee_router",
  "initial_state_root": "0x…",
  "steps": [
    {
      "tx": { "kind": "route_fee", "source": "dex", "asset": "zUSD",
              "amount": 12347,
              "split_table": {"buyburn_bps": 6000, "stakers_bps": 0,
                              "reserve_bps": 2000, "hosts_bps": 2000} },
      "expected_accept": true,
      "expected_reject_reason": null,
      "post_state_root": "0x…",
      "receipt_hash": "0x…"
    }
  ],
  "final_state_root": "0x…"
}
```

* `version` — schema version (`1`).
* `kernel` — the transition kernel the trace exercises (`fee_router`).
* `initial_state_root` — state root **before** any step. For `fee_router` this
  is the root of the zero `FeeAccumulator`.
* `steps[i].tx` — the transition input (see *tx kinds* below).
* `steps[i].expected_accept` — `true` if the transition accepted the input.
* `steps[i].expected_reject_reason` — `null` on accept; otherwise the **stable
  reason string** (see *rejection codes*).
* `steps[i].post_state_root` — state root **after** the step. On a rejected step
  the state is unchanged, so this equals the pre-step root.
* `steps[i].receipt_hash` — receipt hash on accept; `null` on reject.
* `final_state_root` — state root after the last step.

The base schema (`tx` / `expected_accept` / `expected_reject_reason` /
`post_state_root` / `receipt_hash`) is exactly the format requested in the
migration plan and is **kernel-agnostic**.

## `tx` kinds — `fee_router`

```json
{
  "kind": "route_fee",
  "source": "dex" | "perps" | "borrow" | "redemption",
  "asset": "<utf-8 asset id>",
  "amount": <non-negative integer fee>,
  "split_table": {
    "buyburn_bps": <int>, "stakers_bps": <int>,
    "reserve_bps": <int>, "hosts_bps": <int>
  }
}
```

`amount` is a JSON integer with arbitrary magnitude (the corpus includes values
larger than `u64`). Tools must preserve integer precision (the Rust CLI enables
`serde_json`'s `arbitrary_precision`).

## `tx` kinds — `replay_guard`

```json
{
  "kind": "admit",
  "sender": "0x<96 hex chars>",
  "nonce": <integer in [1, 4294967295]>
}
```

Replayed via the `replay-guard-trace` CLI subcommand. Reject codes:
`malformed_tx`, `unknown_tx_kind`, `unknown_field:<name>` (structural), and
`invalid_sender`, `invalid_nonce`, `duplicate_nonce` (`nonce == last`),
`stale_nonce` (`nonce < last`), `nonce_gap` (`nonce > last + 1`) (semantic).
Validation order: structural → `invalid_sender` → `invalid_nonce` →
duplicate/stale/gap. State (per-sender last nonce) is unchanged on rejection.
The accumulator root is `domain_sep("replay_guard_state", v1)` over the
sender-sorted `(sender_bytes, last_nonce)` entries; the admission receipt hash is
`domain_sep("replay_admission", v1)` over `SND`(sender) `NON`(nonce) `PRV`(prev).
Sender canonicalization matches the runtime fixed-hex helper: raw hex, `0x` /
`0X`, mixed case, and surrounding whitespace collapse to lowercase `0x...`.

## `tx` kinds — `balances`

```json
{ "kind": "credit",   "recipient": "0x<96 hex>", "asset": "0x<64 hex>", "amount": N }
{ "kind": "transfer", "sender": "0x<96 hex>", "recipient": "0x<96 hex>",
  "asset": "0x<64 hex>", "amount": N }
```

Replayed via `replay-balance-trace`. `credit` funds `(recipient, asset)`;
`transfer` moves `amount` of `asset` from `sender` to `recipient` and is
supply-conserving. `amount` is an integer in `[1, MAX_BALANCE]`
(`MAX_BALANCE = 2**112 - 1`). Reject codes: `malformed_tx`, `unknown_tx_kind`,
`unknown_field:<name>` (structural), and `invalid_sender`, `invalid_recipient`,
`invalid_asset`, `invalid_amount`, `self_transfer`, `insufficient_balance`,
`balance_overflow` (semantic). Transfer validation order: sender → recipient →
asset → amount → self → insufficient → overflow. Zero balances are never stored
(sparse). State root is `domain_sep("balance_table", v1)` over sorted
`(pubkey-48B, asset-32B, uvarint amount)`; the receipt hash is
`domain_sep("balance_receipt", v1)` over `KND` `SND`(presence+sender) `RCP`
`AST` `AMT`.
Pubkey and asset fields canonicalize through the same fixed-hex helper used by
the Python runtime: raw hex, `0x` / `0X`, mixed case, and surrounding whitespace
collapse to lowercase `0x...` form before hashing or state updates.

## `tx` kinds — `zusd`

```json
{ "kind": "bootstrap_oracle", "auth_ok": true, "price_e8": 100000000 }
{ "kind": "deposit_collateral", "amount_e8": 100000000000 }
{ "kind": "mint_zusd", "amount_e8": 20000000000 }
{ "kind": "redeem_zusd", "amount_e8": 1000000000 }
{ "kind": "advance_epoch", "delta": 5 }
{ "kind": "oracle_report" | "oracle_commit" | "repay_zusd" | "withdraw_collateral"
        | "deposit_sp" | "withdraw_sp" | "liquidate", ... }
```

Replayed via `replay-zusd-trace`. The authority is `src/core/zusd.py`'s
single-vault `step`; the Rust shadow mirrors it. Unknown fields are **ignored**
(matching the authority). Amounts are arbitrary positive integers — the
authority's `_require_pos_int` is unbounded and oversized values are rejected by
command-specific logic, so the shadow uses bignum arithmetic. Reject reasons are
stable codes mapped from the authority's prose (e.g. `mint_blocked_oracle`,
`mint_below_min_debt`, `mint_violates_mcr`, `redeem_violates_mcr`,
`not_positive_int`, `bounded_check_failed`, `invariant_violation`,
`unknown_action`, ...); see `tools/runtime/zusd_kernel_lib.py`. State root is
`domain_sep("zusd_state", v1)` over the 32 state fields as uvarints; the receipt
hash commits to `(command_tag, post_state_root)`.

## Rejection codes (stable)

Every rejection carries a stable machine code. Domain-constraint rejections
append a sub-code after `:`. Codes are produced identically by the Python
reference (`src/core/fee_router.py` + `tools/runtime/golden_trace_lib.py`) and
by the Rust shadow (`zenodex-runtime-core` + `zenodex-runtime-cli`).

| Code | Layer | Meaning |
|------|-------|---------|
| `malformed_tx` | structural | tx not an object, or required field has the wrong type. |
| `unknown_tx_kind` | structural | `kind` is not `route_fee`. |
| `unknown_field:<name>` | structural | unexpected field in the tx or split table (`<name>` is the first such field in sorted order). |
| `negative_amount` | semantic | `amount` is negative. |
| `amount_too_large` | semantic | `amount > MAX_FEE_AMOUNT` (`2**112 - 1`). |
| `split_component_out_of_range` | semantic | a bps value is outside `[0, 10000]`. |
| `split_does_not_sum_to_10000` | semantic | the four bps do not sum to `10000`. |
| `unknown_domain` | semantic | `source` is not a known fee domain. |
| `domain_constraint_violated:buyburn_below_floor` | semantic | dex/perps `buyburn_bps < 5000`. |
| `domain_constraint_violated:stakers_below_floor` | semantic | borrow `stakers_bps < 5000`. |
| `domain_constraint_violated:redemption_buyburn_must_be_zero` | semantic | redemption `buyburn_bps != 0`. |
| `domain_constraint_violated:redemption_hosts_must_be_zero` | semantic | redemption `hosts_bps != 0`. |
| `domain_constraint_violated:redemption_reserve_below_floor` | semantic | redemption `reserve_bps < 2000`. |
| `arithmetic_overflow` | semantic | an accumulator component would exceed `MAX_FEE_AMOUNT`. |

### Validation order (must match across runtimes)

The order matters when an input violates several rules at once. Both runtimes
evaluate in this fixed order:

1. structural: object → `kind` → unknown tx fields → field types →
   split-table parse (unknown/missing/typed fields),
2. semantic (`route_fee`): `negative_amount` → `amount_too_large` →
   `split_component_out_of_range` → `split_does_not_sum_to_10000` →
   `unknown_domain` → domain floors → arithmetic.

## Canonical hashing

State roots and receipt hashes are `0x`-prefixed SHA-256 over an explicit,
ordered byte pre-image built with the repo's canonical primitives
(`src/state/canonical.py`, mirrored in `zenodex-runtime-core::canonical`):

* `encode_uvarint` — unsigned LEB128.
* `encode_bytes` — `uvarint(len)` prefix + raw bytes.
* `domain_sep_bytes(label, v)` — `b"zenodex:" + label + b":v" + v + b"\x00"`.

**Receipt** (`domain_sep "fee_receipt" v1`): tagged fields in fixed order —
`SRC`(source) `AST`(asset) `AMT`(amount) `BBN`(buyburn) `STK`(stakers)
`RSV`(reserve) `HST`(hosts) `DST`(dust).

**Accumulator root** (`domain_sep "fee_accumulator" v1`): `DST` encodes a
sorted list of `(source, asset, amount)` dust entries. `CBB`, `CST`, `CRS`, and
`CHS` each encode a sorted list of `(asset, amount)` bucket entries for
buyburn, stakers, reserve, and hosts. Empty and zero entries are omitted.

Dust is scoped by `(source, asset)`. Bucket totals are scoped by `asset`. This
prevents a remainder or balance in one token unit from being consumed as another
token unit.

No floats appear anywhere in a pre-image; all numbers are LEB128-encoded
integers. Output ordering is explicit (never map iteration).

## Determinism guarantees

* `export_golden_trace.py` writes canonical JSON (`sort_keys`, 2-space indent,
  trailing newline). Re-running it is **byte-identical**
  (`tests/runtime/test_golden_trace_replay.py::test_committed_smoke_trace_is_up_to_date`).
* State roots are independent of dict insertion order and of Python version
  (pure-integer LEB128 + SHA-256).
* A committed corpus that drifts from the current runtime semantics fails the
  "up-to-date" test, forcing regeneration.

## Coverage today vs. later

`smoke.json` exercises, **in scope for the `fee_router` kernel**: fee-split
conservation across all four domains, host fee routing, buyback (`buyburn`)
accrual, source/asset-scoped dust carry, and every rejection code above.

Disaster paths that belong to **other** runtime surfaces — duplicate/replayed
payout rejection, invalid signature, insufficient balance, zUSD mint/redeem,
batch clearing — are added to the corpus as those surfaces are migrated
(Phase 6 in `RUST_RUNTIME_MIGRATION_PLAN.md`). The schema already supports them:
each is just another `kind` with its own `expected_reject_reason`.
