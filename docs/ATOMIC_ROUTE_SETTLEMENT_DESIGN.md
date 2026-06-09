# Atomic Route Settlement — Design / Build Spec (2026-06-08)

Decision (user): build split-routing as an **atomic, quote-receipt-bound route settlement**,
NOT N independent swaps. Safety contract:

```
all quoted legs validate + apply  -> commit post-state
any leg fails                     -> deterministic reject, NO pool or balance state changes
```

N independent per-pool swaps remain ONLY as an explicitly-labeled dev/fallback path — never
the production split-routing claim, never called "atomic."

## Build status: DESIGN-READY, BUILD-BLOCKED (collision)

The three consensus-core files this touches — `src/integration/dex_engine.py`,
`src/core/settlement_strong_validator.py`, `src/core/batch_clearing.py` — are under heavy
concurrent WIP (164+ lines, NOT route-related: a new `_first_rejected_settlement_intent_error`,
`_validate_settlement_strong_impl` edits, `DexEngineConfig`/`apply_ops` edits). Building the
route path into them now means consensus-core merge conflicts. **Build the moment that WIP
settles** (or in an isolated worktree off the settled base), golden-first, then heavy Codex review.

## What already exists (build ON this, don't reinvent)

- Quote receipts carry `legs`, each with `hops` (`dex_engine.py:745`).
- The N-leg-bound model already validates **full leg coverage** (`dex_engine.py:934`:
  `set(observed_leg_indices) == set(range(len(legs)))`), **no duplicate leg** (`:926`), and
  per-leg `quote_receipt_leg_index` binding (`:912`). Reuse this coverage/dup logic.
- `apply_ops` returns a candidate post-state and the caller commits only on `result.ok` —
  this IS the atomicity primitive (build candidate, commit-or-discard). State is immutable
  (`dataclasses.replace`), so candidate-apply = thread an evolving copy; discard on any failure.
- Pool-fingerprint binding + stale-receipt rejection already exist for quote-bound intents
  (`dex_engine.py:740` `receipt_pool_fingerprint`).

## The new surface

### 1. Intent model (`src/state/intents.py` — CLEAN, safe to edit)
- Add `IntentKind.ROUTE_EXACT_IN` and `IntentKind.ROUTE_EXACT_OUT`.
- Add `RouteIntent(Intent)` validating (fields stored in the `.fields` dict, like SwapIntent):
  - `quote_receipt_hash` (binds the exact quoted route)
  - `route_kind` ∈ {exact_in, exact_out} (or carried by the IntentKind)
  - `asset_in`, `asset_out` (route endpoints)
  - `leg_indices`: the FULL set of the receipt's leg indices (sorted, no dup, no gap)
  - exact-in: `total_amount_in` (>0) + `total_min_amount_out` (>=0)
  - exact-out: `total_amount_out` (>0) + `total_max_amount_in` (>=0, REQUIRED — no unbounded input)
  - common: `sender_pubkey`, `nonce`, `deadline`
- `intent_id = hash_v0("...route_intent_v0", canonical(payload))`; one signature binds the whole route.

### 2. Validation (`settlement_strong_validator.py` / `dex_engine.py` — WIP, build later)
Deterministic reject precedence (fail-closed, first failure wins):
1. schema / field validity (bad amounts, missing required, bad pubkey)
2. `quote_receipt_hash` matches a present, non-stale receipt (else `stale_or_unknown_quote_receipt`)
3. leg coverage: `leg_indices == set(range(len(legs)))` — reject `incomplete`/`extra`/`duplicate` leg
4. per-leg pool fingerprint matches the receipt (else `pool_fingerprint_mismatch` — stale pool)
5. route endpoints: leg[0].asset_in == route.asset_in, leg[-1].asset_out == route.asset_out, chain continuity
6. nonce (replay) + deadline
7. totals: exact-in `total_out >= total_min_amount_out`; exact-out `total_in <= total_max_amount_in`

### 3. Atomic apply (`dex_engine.py` — WIP, build later)
```
candidate = copy(pre_state)              # immutable; thread the evolving candidate
for leg in legs (in receipt order):
    ok, candidate, leg_out = apply_leg(candidate, leg)   # one hop/pool swap on the candidate
    if not ok: return Reject(leg_failure_code), pre_state   # NO commit — discard candidate
verify totals (min_out / max_in) on the accumulated route
if totals fail: return Reject(slippage_code), pre_state
return Accept, candidate                  # commit only here
```
- Conservation must hold across all legs (sum of per-leg deltas; fee recipients counted).
- Deterministic: same inputs → identical post-state root (replayable).

## Test matrix (mandatory — the user's list)
1. successful 2-pool atomic split; 3-pool atomic split
2. one failing leg rolls back ALL previous candidate leg effects (state == pre_state)
3. duplicate leg index rejected; missing leg rejected; extra leg rejected
4. stale quote receipt rejected
5. mismatched pool fingerprint rejected
6. exact-in: total output below `total_min_amount_out` rejected; exact-out: total input above
   `total_max_amount_in` rejected
7. deterministic replay → identical state root
8. user balance + pool conservation across all legs
9. (parity) the UI-signed route intent_id reproduces the backend's (cross-language, like exact-out)
10. existing single-pool SWAP_EXACT_IN/OUT behavior byte-identical (route is purely additive)

## UI (after the engine path lands)
- A "split route" submit that signs ONE RouteIntent (extend `dexIntentSigner.js` with route-intent
  parity, like exact-out) + a UI surfacing; honest finality (deriveSwapFinality) preserved.

## Sequencing
1. (now) this design.
2. (blocked) engine path — build when the settlement-core WIP settles; golden-first; Codex review.
3. intent model (`intents.py`) is CLEAN and could be built first in isolation if desired.
