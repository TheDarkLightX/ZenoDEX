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
| Consumed-object identity | Not used by the primary route | Empty occurrence field, checked by the global verifier |

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

route-level atomic candidate
  -> exact effects + nonzero lane-coordination obligation

Spot lane coordinator + Tokenomics lane coordinator
  -> two exact lane journals that discharge the module obligation

RouteCompositionJournalV1
  -> global pre/post roots + canonical effects + closed route obligation

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

## Exact lane-port checkpoint

The SHADOW functional core now derives one immutable route-port value from the
already validated purchase and burn journals. It contains exactly two paired
dependencies:

```text
tokenomics_quote_out_atoms = spot_quote_in_atoms = q
spot_zdex_out_atoms        = tokenomics_burn_in_atoms = p
```

The value also binds the exact authority-head root, policy registry,
receipt-verifier binding, profile, route, command occurrence, module releases,
economic policies, Oracle occurrence, assets, source and pool principals,
purchase and burn journal roots, and receipt-bound leaf roots. The
authority-head root commits the authority generation. Each role-specific flow
root commits its exact transferred amount. Construction rejects a
cross-journal or cross-authority mismatch in any of those coordinates, the
transient burn state, or the port identity. Python and Rust share a fixed
value-carrying quote-flow vector. Lean proves that the abstract lane
observations recompose the atomic poststate and preserve quote conservation,
exact Spot output, and exact supply reduction.

This checkpoint establishes the dependency interface only. It does not create
a lane journal, verify a lane receipt, discharge the nonzero coordination
obligation, or authorize route or epoch publication. The next coordinator must
verify complete lane-owned states and module receipts against these exact
ports.

### Historical purchase-leaf boundary

`ZDEXAMMPurchaseJournalV2` and its receipt verifier remain SHADOW donors. Their
effect plan contains the tokenomics buyback-reserve debit, both Spot pool
reserve movements, and the route-transient purchased-ZDEX credit while naming
only one Spot lane write. That shape cannot serve as a complete Spot module
proof under the sole-writer map.

The successor Spot leaf must derive a complete Spot lane prestate and poststate
and expose only the selected-pool transition plus typed route ports. The
successor tokenomics leaf must own fee allocation, buyback-reserve spending,
cadence, and exact burn inside one complete tokenomics state. Route composition
will build the four-row global custody projection after both lane receipts
verify. No existing purchase receipt is promoted by this decision.

## ABI boundary for consumed objects

`EconomicCommandOccurrenceV1` already commits `consumed_object_ids`, while the
current global epoch verifier rejects every nonempty value because ABI V1 has
no durable single-use object state. The primary same-occurrence composer also
requires an empty tuple and creates no persistent budget object. The older
delayed-budget Python reference and Rust composer remain historical donors. The
Rust entry point is deprecated, its result is typed `HistoricalResearchOnly`,
and neither donor can enter the ABI V1 epoch verifier.

Adding durable consumed objects would add a foundational state category and
invariant. It requires `GlobalSettlementABI V2`, content-derived verifier and
profile identifiers, explicit amount backing, exact nullifier semantics,
terminal drain, migration, and publication evidence. Existing V1 research
receipts retain their historical bytes and remain `VERIFY_ONLY`.

## Rejected alternatives

### Reusing command replay rows for a future delayed route

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

1. Present any nonempty consumed-object tuple to the ABI V1 primary route.
2. Omit or duplicate either required lane write.
3. Debit the buyback reserve without the exact tokenomics poststate.
4. Change pool reserves without the exact Spot poststate.
5. Burn supply without the exact tokenomics supply transition.
6. Persist the transient purchased-ZDEX port.
7. Substitute pool, pool definition, assets, amount, profile, route, releases,
   Oracle occurrence, occurrence identity, prestate, or port order.
8. Present a zero module terminal root before both lane coordinators and global
   refinement discharge the obligation, or disconnect the obligation chain.
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

The spend-selection kernel has Python/Rust canonical-root parity, bounded Lean
arithmetic and atomic-accounting theorems, and an authenticated SHADOW
Spot/Oracle adapter. Python finalization now returns an opaque accepted witness
that binds the exact pending transition and verified burn receipt. The Rust
SHADOW composer derives and binds complete tokenomics pre/post state, canonical
same-principal pool effects, and a nonzero lane-coordination obligation. Its
governed purchase and burn witnesses must share one opaque current-authority
statement that binds the profile, authority generation, policy registry,
verifier registry, root image, and receipt-verifier binding. Currentness and
receipt validity remain external verifier-port premises; test verifiers do not
establish deployment authority. Typed Python and Rust lane ports now bind the
exact quote and ZDEX dependency amounts, and Lean proves their abstract
decomposition. A Spot lane coordinator and a tokenomics coordinator that
covers the complete atomic state, including fee allocation, cadence, and burn,
remain incomplete. The existing burn-only tokenomics coordinator does not
close that obligation. RISC0 guests, runtime-to-theorem refinement, migration,
durable publication, and all value-movement gates also remain incomplete. The
ABI V1 global epoch verifier continues to reject persistent consumed objects.
No production, settlement, release, publication, migration, or value-moving
authority is claimed.
