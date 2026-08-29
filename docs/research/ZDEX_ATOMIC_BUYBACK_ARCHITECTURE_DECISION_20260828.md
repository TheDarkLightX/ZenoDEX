# ZDEX Atomic Buyback Architecture Decision

Date: 2026-08-28

Status: research-only architecture decision. Production, settlement, release,
publication, migration, and value-moving authority remain `NONE`.

## Decision

The primary ZDEX buy-and-burn route will use one authenticated atomic command
occurrence. That occurrence allocates the governed fee amount, updates the
buyback reserve, purchases ZDEX through the profile-selected Spot pool, and
burns the exact purchased amount.

The route will not consume a previously issued occurrence-specific budget
object. A delayed budget-object route may be introduced later only if the
product contract requires delayed or independently schedulable buybacks.

This decision minimizes live obligations, migration state, replay surfaces,
and partial-spend states while preserving an accumulated governed buyback
reserve.

## Required state flow

Let:

```text
F  = fee amount selected for allocation
b  = buyback allocation from F
aᵢ = other destination allocations
r  = explicitly carried residue
B0 = buyback reserve before the command
q  = quote-asset amount selected by the active profile for this purchase
p  = ZDEX purchased and burned
B1 = buyback reserve after the command
```

The route must prove:

```text
F = b + sum(aᵢ) + r
0 <= q <= B0 + b
B1 = B0 + b - q

spot_quote_reserve_post = spot_quote_reserve_pre + q
spot_zdex_reserve_post  = spot_zdex_reserve_pre - p
zdex_supply_post        = zdex_supply_pre - p
purchased_zdex_atoms    = burned_zdex_atoms
```

Every rejected transition has identical prestate and poststate and emits no
economic effects.

## Governed spend-selection refinement

The functional core uses one spend rule:

```text
available = checked_u128(B0 + b)
q = min(available, per_command_quote_cap, route_safe_quote_limit)
B1 = available - q
```

The selected release profile supplies a positive minimum spend, a per-command
cap, and a positive minimum block interval. Consensus height determines cadence. The
route-safety limit remains an authenticated Spot/Oracle input and must bind the
same profile, route, command occurrence, prestate, pool, assets, and pricing
policy. A zero safe limit, stale state, regressed height, incomplete cooldown,
reserve overflow, or result below the governed minimum rejects without effects.

The spend-selection mechanism is implemented as an unmounted kernel in Python
and Rust and is mirrored by checked Lean natural-number models:

- `src/core/zdex_buyback_spend_v1.py`
- `src/core/zdex_buyback_spot_safety_receipt_v1.py`
- `src/core/zdex_verified_buyback_spend_v1.py`
- `zk/global_settlement_abi_v1/src/zdex_buyback_spend.rs`
- `lean-mathlib/Proofs/ZDEXBuybackSpendV1.lean`
- `lean-mathlib/Proofs/ZDEXAtomicBuybackAccountingV1.lean`

The Python SHADOW adapter snapshots the complete global prestate, selects its
disabled Spot lane commitment, requires a finalized non-future Oracle
occurrence from that state, verifies the exact profile-selected Spot image and
canonical journal, and derives consensus height and the route-safe limit from
that authenticated occurrence. More precisely, it calls an injected receipt
verifier with the exact image and journal bytes; no production-trusted verifier
is mounted yet. It then requires the actual Spot quote input to equal the spend
selected from the canonical fee state.

Exact numeric caps, intervals, minimum output, freshness, deviation, impact,
and liquidity policy remain versioned profile inputs. These modules do not
compose both lane receipts or authorize settlement by themselves.

## Sole-owner map

| Economic fact | Sole authoritative owner | Global representation |
|---|---|---|
| Spot pool reserves | `SPOT_LIQUIDITY` lane | Verified global accounting projection |
| Fee ingress, fee destinations, and buyback reserve | `ZDEX_TOKENOMICS` lane | Verified global accounting projection |
| ZDEX live supply and burn controls | `ZDEX_TOKENOMICS` lane | Global supply projection |
| Purchased ZDEX awaiting same-route burn | Ephemeral typed route port | No durable state |
| Consumed-object identity | Global settlement verifier | Dedicated canonical nullifier map |

The term `owner` in this table identifies which state machine may update an
accounting fact. It does not describe legal custody or key control. User assets
remain controlled by the corresponding keys and protocol rules.

## Functional composition

```text
derive_buyback_intent(profile, tokenomics_pre, global_pre)
  -> BuybackIntentPort

SpotTransition(spot_pre, intent)
  -> spot_post + PurchasedZDEXPort

TokenomicsTransition(tokenomics_pre, intent, PurchasedZDEXPort)
  -> tokenomics_post

Spot lane coordinator + Tokenomics lane coordinator
  -> two exact lane journals with zero terminal roots

RouteCompositionJournalV1
  -> global pre/post roots + canonical effects + zero terminal root

epoch verifier + compare-and-swap publisher
  -> one atomic commit
```

The active profile selects the pool, full pool definition, quote asset, ZDEX
asset, route release, module releases, Oracle policy, purchase rule, limits,
and port schemas. A trigger caller supplies timing and authentication inputs
allowed by policy. The caller does not select economic resources or burn
destinations.

The ephemeral purchased-ZDEX port cannot be published or stored separately.
Any failure in purchase validation, burn validation, lane composition, route
composition, receipt verification, or publication leaves the complete
economic prestate unchanged.

## ABI V1 consumed-object completion

`EconomicCommandOccurrenceV1` already commits `consumed_object_ids`, while the
current global verifier quarantines every nonempty value because durable
single-use state is missing. Before O-008 freezes ABI V1 ownership, complete
the declared semantics with:

```text
ConsumedObjectNullifierEntryV1 {
    object_id,
    consumer_occurrence_id
}

GlobalEconomicStateV1 {
    ...
    consumed_object_nullifiers: canonical ordered tuple
}
```

The verifier derives insertions from accepted command occurrences. Callers do
not propose arbitrary nullifier writes. The global poststate root commits the
updated map, and publication applies state, replay, nullifiers, effects,
receipts, history, and outbox changes in one compare-and-swap transaction.

This completion receives new content-derived verifier, profile, corpus, and
image identifiers. Existing research receipts retain their historical bytes
and remain `VERIFY_ONLY`. Once O-008 freezes ABI V1, any foundational change to
the nullifier representation requires ABI V2.

An empty initial nullifier map is admissible only after evidence establishes
that no pre-freeze object has live spending authority. Current buyback routes
remain unmounted and must continue to reject new persistent budget objects.

## Rejected alternatives

### Reusing command replay rows

The replay relation binds command replay and occurrence identities. Synthetic
replay identifiers cannot safely represent several consumed objects mapped to
one consumer occurrence. Reuse would change replay semantics and migration
meaning.

### Lane-local spent sets

A private lane spent set would leave cross-route and cross-lane reuse outside
the global verifier. It would also create a second publication authority for a
global single-use fact.

### Prior occurrence-specific budgets by default

Persistent budget objects require single-use nullifiers, amount backing,
partial-spend or change semantics, cancellation, expiry, terminal drain, and
migration. Those states add no value when the product only needs an
accumulated reserve and profile-scheduled atomic execution.

## PulseX-derived negative obligations

The comparative PulseX review contributed five named failure families:

- `PBAB-RI-01`: caller-selected inventory execution;
- `PBAB-PR-01`: price-free reserve extraction;
- `PBAB-BR-01`: reusable fee budget;
- `PBAB-TS-01`: terminal or partial-effect bypass;
- `PBAB-CF-01`: configuration suppresses burning.

PulseX source was used as comparative evidence only. No PulseX code is copied
or treated as authoritative for ZenoDEX semantics.

## Required negative evidence

1. Reuse the same consumed object in the same epoch, adjacent epochs, delayed
   epochs, and reordered epochs.
2. Omit or duplicate either required lane write.
3. Debit the buyback reserve without the exact tokenomics poststate.
4. Change pool reserves without the exact Spot poststate.
5. Burn supply without the exact tokenomics supply transition.
6. Persist the transient purchased-ZDEX port.
7. Substitute pool, pool definition, assets, amount, profile, route, releases,
   Oracle occurrence, occurrence identity, prestate, or port order.
8. Present a nonzero terminal root or disconnected global state chain.
9. Crash before and after publication, retry exactly, race two roots, and use a
   stale compare-and-swap head.
10. Exercise zero, one atom, maximum neighbors, overflow, dust, residue,
    minimum output, Oracle freshness, and impact boundaries.

## Unresolved product policies

This architecture does not select:

- fee percentages or destination shares;
- numeric spend caps, minimums, and cadence intervals;
- residue disposition;
- minimum output, Oracle or TWAP source, freshness, finality, or deviation;
- execution-impact and MEV bounds;
- minimum pool liquidity;
- cooldown, batching, splitting, or protected ordering;
- retained-supply and decimal-step policy.

Fixtures and comparative protocols cannot select these values. Their eventual
policy envelope needs explicit user approval, deterministic boundary evidence,
and a new content-derived release.

## PulseX lessons applied in this checkpoint

The implementation keeps the useful atomic shape: observed quote value moves
directly from the canonical buyback balance into the governed Spot purchase,
and the actual ZDEX output is the amount later required at the burn boundary.
The release-selected pool, assets, and Oracle policy replace caller-selected
inventory. The journal requires a positive safe limit and output minimum and
binds both to the receipt. A future governed Spot guest must establish their
Oracle, freshness, liquidity, and impact formulas before this closes the
price-free reserve-extraction risk. Hosting compensation remains a separate fee
destination and cannot suppress burning through a zero-bounty configuration
branch.

## Claim ceiling

The spend-selection kernel now has Python/Rust canonical-root parity, bounded
Lean arithmetic and atomic-accounting theorems, and an authenticated SHADOW
Spot/Oracle adapter. The replacement two-lane route, complete tokenomics lane
state transition, ABI V1 nullifier completion, RISC0 guests, runtime-to-theorem
refinement, migration, durable publication, and all value-movement gates remain
incomplete. No production, settlement, release, publication, migration, or
value-moving authority is claimed.
