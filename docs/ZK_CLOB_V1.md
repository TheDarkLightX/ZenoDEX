# zk-CLOB v1 — Proof-Carrying Central Limit Order Book

> Status: **v1 (Python core built + tested)**. RISC0 guest STARK, escrow,
> LTLf liveness, and machine-checked (Lean/ESSO) invariants are **phase 2** and
> are explicitly *not* delivered in v1. No proof is produced in v1.

## The moat

dYdX v4 runs an off-chain order book and trusts honest validators to *order* and
*match* correctly. A user who cannot re-derive the match has to trust the
sequencer.

ZenoDEX encodes the matching **rule** — **price** priority, maker-price fills, and
conservation — as a deterministic, integer kernel. A correct match (the resulting
`post_book_root` plus the matched fill receipts) is a **precondition of client
acceptance**: the client re-runs the *same* kernel and refuses any book transition
whose claimed matching does not replay bit-for-bit.

> Trust the math, not the sequencer. If the host must be honest, it has already
> failed.

> **v1 scope honesty (read first — scopes every "price-time priority" claim below).**
> v1 delivers the above for **price** priority, conservation, and bit-for-bit replay.
> The **time** half of "price-time priority" is **conditional**: `sequence` is
> currently *submitter-supplied and only bounds-checked*, so v1 proves "the matcher
> respected the `(price, sequence, order_id)` order it was *given*," **not** "the
> queue could not be reordered" (a submitter can set `sequence = 0` to queue-jump).
> Closing it — deriving `sequence` from the canonical ingress order (ascending
> `intent_id`, `src/tau_specs/batching_v1_4.tau`) so the client re-derives it rather
> than trusting a submitted one — is **deferred** (see the PRICE-TIME PRIORITY caveat
> and Honest deferred scope). So v1 is "trust the math, not the sequencer" for price +
> replay; the sequencer-independence of *time* priority is the deferred piece.

The matcher is consensus-critical-shaped (CBC): a **total function**
`apply_order(book, taker) -> accept | reject`, pure, integer-only, with
candidate-commit (validate fully before mutating), stable reject codes,
reject-is-no-op, and deterministic total-order tie-breaks.

## Files

| File | Role |
|------|------|
| `src/state/clob_book.py` | Canonical book state + domain-separated `state_root()` (the commitment) |
| `src/core/clob_matching.py` | Pure continuous matching kernel + conservation-checked settlement path + atomic book/balance wrapper |
| `src/core/clob_intent_normal_form.py` | Deterministic CLOB normal form + `ClobOrderIntent` -> `ClobOrder` bridge |
| `src/state/intents.py` | `IntentKind.LIMIT_ORDER` / `CANCEL_ORDER` + `ClobOrderIntent` / `CancelOrderIntent` validators (additive) |
| `tests/core/test_clob_matching.py` | Core invariant gate |
| `tests/state/test_clob_book.py` | Commitment-layer gate |
| `tests/core/test_clob_intent_validation.py` | Intent type + bridge + normal-form + AMM-firewall gate |
| `src/kernels/dex/clob_match_v1.yaml` | ESSO-IR model of the matching state machine — **z3+cvc5 VERIFIED for the bounded single-maker/single-taker case** (Inductive k=1); full book is phase-2 |

## Matching rule (continuous, price-time priority, maker-price fills)

* **Crossing.** A BUY taker crosses a SELL maker iff `taker.price >= maker.price`;
  a SELL taker crosses a BUY maker iff `taker.price <= maker.price`. An incoming
  order that does **not** cross the best opposite order **rests** — this is *not*
  a reject.
* **Priority.** The taker walks the opposite book in the strict total order
  `order_priority_key`: best price first (BUY book highest, SELL book lowest),
  then earliest `sequence` (time priority), then `order_id` (final tie-break).
  Because `order_id` is unique within a book (`DUP_ORDER_ID` rejected), the key is
  a **strict** total order — no two resting orders ever compare equal.
* **Fill price = the RESTING (maker) order's limit price `P_m`.** Not an oracle,
  not a midpoint. This is the crux convention.
* **Quote.** `quote = floor(matched_base * P_m / PRICE_SCALE)`, integer-only,
  checked against a documented `i128`-safe product bound (no silent wrap).
* **Partial fills.** A taker larger than a maker consumes it fully and continues;
  a maker larger than the taker has its resting quantity reduced and remains; a
  leftover taker re-rests (subject to `BOOK_FULL`).
* **Settlement.** Each fill emits buyer `(-quote, +base)` / seller `(+quote, -base)`
  `BalanceDelta` pairs (the *same* floored quote on both sides), settled through
  the conservation-checked balance kernel (`src/core/balance_kernel.transfer`).
  The low-level matcher returns a candidate post-book. A live caller uses
  `apply_order_with_settlement`, which commits both the post-book and post-balance
  state only after every transfer accepts.

`PRICE_SCALE = 10**8` (quote-per-base * 1e8), mirroring `perp_np_matching.E8`.

## Reject codes (stable; reject-is-no-op)

| Code | Cause |
|------|-------|
| `bad_price` | price not in `[1, MAX_PRICE_Q_PER_BASE]` (bool is **not** int) |
| `bad_qty` | base_qty not in `[1, MAX_BASE_QTY]` |
| `bad_side` | side not a `ClobSide` |
| `bad_sequence` | sequence not a u64 |
| `bad_order_id` | order_id not a canonical 32-byte hex |
| `bad_owner` | owner not a canonical 48-byte pubkey |
| `dup_order_id` | order_id already resting (replay/dup guard) |
| `self_trade` | taker would match its own resting maker |
| `book_full` | a non-crossing / leftover order cannot rest (capacity) |
| `insufficient_balance` | a settlement transfer lacks funds (settlement path) |
| `unknown_order` | cancel: no resting order has that id |
| `not_owner` | cancel: requester is not the resting order's owner |

`NOT_CROSSING` is **not** a reject: such an order rests. On any reject the book
`state_root` is unchanged (tested on every reject path, including the atomic
partial-walk-then-self-trade case).

## Key invariants (v1 = Python-validated obligations; phase-2 = Lean/ESSO)

These are stated as **obligations** validated by the Python property/boundary
tests listed. They are *not yet* machine-checked proofs.

### CROSSING-LIMIT (headline)

**Claim.** When a BUY taker crosses a SELL maker (`taker.price >= maker.price`)
and the fill executes at the maker price `P_m`, *both* limits hold at once:

```
buyer pays per-base  P_m  <=  taker.price   (buyer's limit)
seller receives      P_m  ==  maker.price   (its own resting limit)  >=  seller's limit
```

**Integer derivation (BUY taker).** The fill price *is* `P_m = maker.price`.
Crossing gives `taker.price >= maker.price = P_m`, so the buyer's per-base cost
`P_m <= taker.price` — within the buyer's limit. The seller is the resting maker,
so it receives *exactly* its own resting price `P_m = maker.price`, which is by
definition `>=` its own limit. The quote actually transferred is
`q = floor(base * P_m / SCALE) <= base * P_m / SCALE`, and since
`P_m <= taker.price`,

```
q = floor(base * P_m / SCALE)  <=  floor(base * taker.price / SCALE)
```

so the buyer never pays more quote than its limit entitles — floor only ever
moves the cost **down**. The SELL-taker / BUY-maker case is symmetric with the
inequalities reversed. ∎

*Validated by:* `test_crossing_limit_property_random_pairs` (400 random crossing
pairs, both sides), `test_no_overdelivery_taker_within_limit_buy_taker`,
`test_boundary_exact_cross_fills_at_that_price`.

### NO-TRADE-CROSSES-A-LIMIT

No executed fill has price `> a buyer's limit` or `< a seller's limit`. Follows
directly from CROSSING-LIMIT + the maker-price convention.
*Validated by:* the same property test (asserts `seller_limit <= P_m <= buyer_limit`).

### PRICE-TIME PRIORITY

Matching consumes resting orders in strict `(price, sequence, order_id)` order; no
later-or-worse order fills before an available better-or-earlier one.
*Validated by:* `test_price_time_priority_earlier_sequence_fills_first`,
`test_taker_walks_multiple_makers_best_first`, and the sorted-level invariant in
`test_sorted_level_invariant_strict_total_order`.

> **Caveat — the *time* guarantee is conditional on a trusted sequence source.**
> Price priority is unconditional (a pure function of the orders). The *time*
> component is only as honest as `sequence`, which in v1 is **submitter-supplied and
> merely bounds-checked** — a submitter can set `sequence = 0` to **queue-jump** an
> earlier same-price maker. So v1 proves "the matcher respected the
> `(price, sequence, order_id)` order it was *given*," NOT "the host/submitter could
> not reorder the queue." The trustless fix is to assign `sequence` from the
> **canonical ingress order** (ascending `intent_id`, no privileged ordering — cf.
> `src/tau_specs/batching_v1_4.tau`) so the client *re-derives* the sequence instead
> of trusting a submitted one. Canonical sequence assignment is **deferred** (see
> Honest deferred scope).

### CONSERVATION (Δ = 0, rounding-independent)

Both sides book the **same** quote integer, so per match
`sum(base in) == sum(base out)` and `sum(quote in) == sum(quote out)` exactly,
*for any rounding of quote*. This reuses the `Settlement`/`BalanceDelta`
conservation homomorphism (Δ : Settlement →+ ℤ).
*Validated by:* `test_conservation_delta_zero_random_batches` (60 random
batches), `test_dust_fill_quote_zero_*` (conservation even when quote floors to 0).

### NO-OVERDELIVERY (rounding bound)

`quote = floor(base * P_m / SCALE)`. Floor keeps the taker strictly within its
limit and the maker absorbs the sub-unit rounding **in its own disfavor**,
bounded by `< 1` quote unit per fill: the residual
`base*P_m - quote*SCALE ∈ [0, SCALE)`.
*Validated by:* `test_no_overdelivery_quote_is_floor_and_rounding_loss_under_one_unit`.

> **Dust case (documented, not a bug).** `base = 1` at a maker price `P_m < SCALE`
> floors to `quote = 0`: the buyer receives base for zero quote. Conservation
> still holds exactly and the loss is `< 1` quote unit (the no-overdelivery
> bound). This is the `1-unit` boundary; the maker that posted a sub-`SCALE`
> price accepts the dust by construction. Tested in
> `test_dust_fill_quote_zero_when_base_times_price_below_scale`.

### DETERMINISM

The same multiset of resting + incoming orders yields an identical fill sequence
and identical `post_book_root`, independent of input arrival permutation — modulo
the explicit `(price, sequence, order_id)` order. The batch driver `apply_orders`
sorts incoming by `(sequence, order_id)` **before** applying, so the
sequence-sort (not arrival order) is the determinism witness.
*Validated by:* `test_determinism_shuffle_invariance_interacting_orders` (50
permutations of orders that cross at different sequences),
`test_determinism_sequence_sort_is_load_bearing`,
`test_state_root_shuffle_invariance_many_permutations` (book layer).

### REJECT-IS-NO-OP

Every reject (`bad_*`, `self_trade`, `dup_order_id`, `book_full`,
`insufficient_balance`) leaves the relevant committed root unchanged. The pure
matcher rejects leave the book unchanged; `settle_fills` rejects leave balances
unchanged; `apply_order_with_settlement` rejects leave both book and balances
unchanged.
*Validated by:* every `test_reject_*_no_op`,
`test_settlement_insufficient_balance_is_no_op`, and the atomic settlement
rollback tests.

### NON-VACUITY

A concrete crossing witness (BUY@101 vs SELL@100, qty 50) actually fills at the
maker price 100, so the invariants are not vacuously true.
*Validated by:* `test_non_vacuity_witness_fills`.

## Relate, do not duplicate: where CLOB sits among the matchers

| Module | Mechanism | Price | Priority |
|--------|-----------|-------|----------|
| `src/core/batch_clearing.py` | Pool-facing greedy `(A,B)` clearer; orders trade against an **AMM pool** | pool/CPMM execution price | best-limit-price-first, lex `(A,B)` tie-break |
| `src/core/uniform_batch_clearing.py` | One **uniform** clearing price for the whole batch | single uniform price | n/a (uniform) |
| `src/core/perp_np_matching.py` | **Net-zero clearinghouse**, quantity only | one **published clearing price** (no discovery) | canonical pubkey/nonce order; largest-remainder; **no price-time** |
| **CLOB** (this) | **Continuous, peer-to-peer** order book | the **resting maker's limit** (no oracle) | strict **price** priority, then `sequence` then `order_id` — the **time** half is conditional on a canonical `sequence` source (v1: submitter-supplied; canonical assignment deferred, see intro caveat) |

The CLOB reuses the repo's deterministic-matcher idiom — the
`_get_limit_price` / lex tie-break seed from `batch_clearing.py` and the canonical
sparse `state_root()` template from `balance_kernel.py` — but is a *different*
mechanism: continuous, peer-to-peer, maker-priced, price-time. It is **firewalled
from the oracle**: unlike `src/kernels/dex/order_intent_v1.yaml` (an
oracle-priced, keeper-triggered scheduled-order kernel), the CLOB fill price is
the resting maker's limit and **no oracle enters the matching path**. CLOB and the
order-intent keeper model are related only at the intent-type / plumbing layer.

## Intent plumbing (additive)

`IntentKind` gains `LIMIT_ORDER` and `CANCEL_ORDER` (additive). `ClobOrderIntent`
and `CancelOrderIntent` validate shape with the same `_require_int_field`
bool-is-not-int discipline as the AMM intents. `clob_order_from_intent` is the
single, total bridge from a validated intent to the frozen `ClobOrder` the matcher
consumes (it re-validates via `ClobOrder.__post_init__`).

**Firewall.** `LIMIT_ORDER` / `CANCEL_ORDER` are recognized kinds reserved for the
CLOB path. The **AMM batch-settlement ingress** (`src/integration/operations.py`)
**rejects** them by design (fail-closed): there is no CLOB engine wiring in v1, so
routing a CLOB order into AMM settlement would be incorrect. This is an
intentional, tested contract (`test_amm_ingress_rejects_{limit,cancel}_order_kind`),
not an oversight. An `IntentKind` whose members are not all accepted by every
consumer is coherent: each consumer states which kinds it accepts.

## Domain bounds

| Constant | Value | Why |
|----------|-------|-----|
| `PRICE_SCALE` | `10**8` | quote-per-base * 1e8 (mirrors `perp_np_matching.E8`) |
| `MAX_PRICE_Q_PER_BASE` | `(1<<56)-1` | keeps `base*price < 2**112` for the Rust `i128` shadow |
| `MAX_BASE_QTY` | `(1<<56)-1` | same product envelope |
| `MAX_SEQUENCE` | `(1<<64)-1` | u64 sequence |
| `MAX_BOOK_ORDERS` | `1<<20` | `BOOK_FULL` capacity guard |

`compute_quote` rejects (`OverflowError`) any `base*price` above
`MAX_BASE_QTY * MAX_PRICE_Q_PER_BASE` rather than wrapping.

## Phase-2 design: the RISC0 guest proving path (DESIGN ONLY — no proof in v1)

> **No STARK is produced in v1.** This section is a *design* for the phase-2 guest.
> The `no_std` Rust port of the matcher, postcard wiring, the `riscv32im` guest
> build, and an actually-produced receipt are **not** delivered this pass: the
> RISC0 proving tree and proving cost put a verified proof out of scope for one
> pass.

**Naming reconciliation.** The original design referenced a `ZenoProofInputV1`
enum with a `Clob(ClobProofInputV1)` arm. In the **main tree**, the shipped guest
shape is the struct pair `StateProofInputV1` / `StateProofJournalV1`
(`zk/state_proof_risc0/shared/src/lib.rs`), *not* an enum-with-arms.
(MEMORY notes a `ZenoDexProofInputV1` enum exists on a different feature branch.)
This doc designs against the **actual main-tree shape** and surfaces the
discrepancy rather than silently swapping names.

**Proposed `ClobProofInputV1` / `ClobJournalV1`** (mirroring `StateProofJournalV1`):

```rust
// shared/src/lib.rs (phase 2)
pub struct ClobProofInputV1 {
    pub pre_book_root: [u8; 32],          // == hash(pre_state)
    pub base_asset: [u8; 32],
    pub quote_asset: [u8; 32],
    pub resting: Vec<ClobOrderV1>,        // canonical pre-book
    pub incoming: Vec<ClobOrderV1>,       // processed in (sequence, order_id) order
    pub pre_app_hash_present: bool,
    pub pre_app_hash: [u8; 32],
    pub expected_post_book_root: [u8; 32],
}

pub struct ClobJournalV1 {
    pub journal_version: u32,
    pub pre_book_root: [u8; 32],
    pub post_book_root: [u8; 32],
    pub orders_commitment: [u8; 32],      // commit to (resting, incoming)
    pub matched_receipts_root: [u8; 32],  // root over per-fill receipts
    pub pre_app_hash_present: bool,
    pub pre_app_hash: [u8; 32],
    pub post_app_hash: [u8; 32],
}
```

The guest would (1) re-run the **same** deterministic matching the Python core
runs — same total order, same floor-quote, same reject codes; (2) check
`pre_book_root == hash(pre_state)`; (3) commit `post_book_root` and
`matched_receipts_root` via the existing `commit_journal` path in
`methods/guest/src/main.rs`. A verifier then accepts **only** a replayable match.

The Python `ClobBook.state_root()` is the reference the guest must reproduce: it
already follows the `balance_kernel`/`StateProofJournalV1` hashing discipline
(domain-sep prefix, length prefix, fixed-width fields, canonical order).

## Honest deferred scope (v1)

- **No STARK / no RISC0 guest code.** Design only (above).
- **No escrow.** Resting orders are **not** collateral-locked in v1; balance
  sufficiency is enforced at **settlement** of matched fills (`settle_fills` via
  `balance_kernel.transfer`, which returns `insufficient_balance`), not when an
  order rests. Use `apply_order_with_settlement` for atomic book+balance commit;
  escrow is deferred.
- **Machine-checked invariants are partial.** A **bounded** single-maker /
  single-taker ESSO-IR model (`clob_match_v1.yaml`) **is** cross-solver verified
  (z3+cvc5 agree, Inductive k=1, verdict VERIFIED) for the maker-price /
  no-overfill / maker-remainder / no-phantom-fill invariants. The **full
  multi-order book** invariants (walking many makers, leftover re-rest,
  self-trade/dup atomicity, the rounding/conservation bound over `PRICE_SCALE`,
  determinism) ship as **Python-validated obligations** (the tests above), not
  yet as Lean/ESSO proofs over the full book. A Lean formalization over a bounded
  book is the phase-2 target.
- **Cancel: ownership enforced, signature deferred.** `apply_cancel` is
  implemented: only a resting order's `owner` may cancel it (`unknown_order` /
  `not_owner` / `bad_order_id` rejects, reject-is-no-op). Binding the `requester`
  pubkey to a *verified signature* end-to-end is deferred.
- **No CLOB engine ingress.** The AMM settlement ingress rejects CLOB kinds by
  design; full CLOB ingress (routing `LIMIT_ORDER` / `CANCEL_ORDER` intents into
  the matcher inside the engine) and LTLf liveness (resting orders eventually
  fill or cancel) are deferred.
- **Sequence assignment is not yet canonical (time-priority is conditional).** The
  matcher honors the `(price, sequence, order_id)` order it is *given*, but
  `sequence` is **submitter-supplied and only bounds-checked** in v1 — so the *time*
  half of price-time priority depends on a trusted sequence source (a submitter can
  set `sequence = 0` to queue-jump). Deriving `sequence` from the **canonical ingress
  order** (ascending `intent_id`, per `src/tau_specs/batching_v1_4.tau`) so the client
  re-computes it without trusting the submitter/host is **deferred** to the
  CLOB-ingress pass. Until then the time guarantee is "respected the order given,"
  not "the queue could not be reordered."
