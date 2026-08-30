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

### Exact Spot functional-core checkpoint

`ZDEXSpotBuybackTransitionV1.lean` defines the command-specific Spot state
machine required by the successor leaf. The formal input contains a canonical
sorted unique pool registry whose siblings may use other registered curves, an
exact injective mathematical pool identifier, the pool lifecycle state, the
governed tokenomics quote-input port, and a finalized subject-bound Oracle
occurrence. Purchased ZDEX is absent from the input authority and is derived by
the CPMM-v8 exact-in equation. The selected pool alone must use CPMM v8. The
accepted result changes one selected pool, emits only the two typed Spot pool
reserve custody deltas and one pre/post-root-bound Spot lane write, exposes
paired quote and purchased-ZDEX ports, journals the exact state, effect, port,
release, policy, Oracle, pool, and terminal commitments, and creates a nonzero
fully context-bound terminal obligation. Rejection returns the exact prestate
with empty effects, ports, and obligation.

The command imports the existing `ZDEXBuybackPriceSafetyV1` policy and proves
its local predicate equivalent to that complete price-safety contract. Profile
authorization commits the exact release, execution and price policies, and the
governed Oracle provider. The prestate root is tied to the full Spot state. The
Oracle occurrence must be a final member of a canonical provider-restricted
registry under the authority-supplied Oracle registry root. The typed quote
port commits nonzero, distinct Tokenomics source pre/post roots plus its effect,
journal, and receipt-binding roots. Both flow identifiers include those roots
and the command occurrence, preventing cross-occurrence aliases in the exact
mathematical encoding. Admission also requires U64 bounds for epoch and height
fields, U128 bounds for every fee, CPMM, route-limit, and price-envelope
intermediate, signed-effect magnitude bounds, and nonzero unrelated Spot roots.

Sibling pools using another curve must name a release in the exact release
registry with `ACTIVE_NEW` or `DRAIN_ONLY` status. Unknown, retired, or revoked
curve releases cannot satisfy pool well-formedness. Lean proves injectivity for
the mathematical state, release, self-consistent profile, Oracle registry,
flow, and full terminal-obligation commitments. It also proves exact
selected-pool lookup in the actual post-registry, universal sibling
preservation, canonical registry preservation, CPMM product nondecrease over
that looked-up state, and one Spot-local conservation theorem linking reserve
differences, fee/net identity, custody effects, and both value ports. The
terminal obligation has the exact `MUST_BURN_PURCHASED_ZDEX` kind, ZDEX supply
burn domain, Tokenomics consumer, burn asset, burn principal, and amount.
Accepting fixtures cover a rounded nonzero fee, a one-atom quote, the exact
Oracle freshness boundary, and a registered sibling curve. Negative witnesses
cover each ordered reject family plus cross-occurrence substitution,
unauthorized Oracle provider, invalid Tokenomics source provenance,
unregistered and revoked curve releases, stale Oracle data, and the first
height outside U64.

This bounded release fixes `protocol_fee_share_bps = 0`. The complete rounded
swap fee therefore remains in the pool. A nonzero protocol share would require
a third typed value port, a named receiver state machine, different reserve
effects, and a new release. The 3,000,000,000-atom reserve and swap caps are
also release semantics for this checkpoint; they are not promoted as final
production economic limits.

The historical purchase journals cannot be refined by relabeling their output
field. The Python donor vector with `q = 125`, reserves `1000/1000`, zero fee,
and `p = 111` agrees with exact CPMM rounding. The Rust donor vector with
`q = 125`, reserves `2000/500`, zero fee, and `p = 40` does not: exact CPMM
output is `floor(500 * 125 / 2125) = 29`. That vector remains historical
SHADOW evidence and is invalid for the successor exact-CPMM release.

The Lean checkpoint is an exact mathematical state machine. At source SHA-256
`e5c2bc35f15afc38cb9f812ac99bd8dc824153ff1b1f2d55845cae550bfa861d`,
independent read-only review approved it only as the subject for Python/Rust
refinement and retained a NO-GO for mounting, settlement authority, and
production claims. It does not establish canonical-byte or cryptographic-root
refinement, Python/Rust parity, RISC0 receipt verification, lane composition,
global replay consumption, or ZenoLedger publication authority.

### Python/Rust runtime-correspondence checkpoint

The SHADOW Python and Rust cores now implement the bounded Spot transition in
`src/core/zdex_spot_buyback_transition_v1.py` and
`zk/global_settlement_abi_v1/src/zdex_spot_buyback_transition.rs`. Both derive
the governed pool from canonical lane state, derive the exact CPMM output,
preserve unrelated pools, emit two Spot reserve effects and one Spot lane
write, and retain the exact purchased amount in a must-burn terminal
obligation. Rust accepted fields are private. Python accepted values rederive
the complete projection from their frozen subject during construction and on
explicit validation. Before either comparison, Python traverses the complete
subject and accepted projection as a closed exact-type graph, including the
opaque price witness, under fixed node and depth budgets. It then compares
every corresponding node by exact runtime type and value. This rejects
foreign equality behavior, Boolean/integer and string/enum equality aliases,
cycles, and oversized forged graphs before they can validate a different
canonical commitment. Python module privacy is not treated as authority.
Rejected economic transitions preserve the input state and expose empty
effects. The Python core keeps rejection precedence in one explicit ordered
phase and separates pool selection, arithmetic, price verification, state
projection, effects, ports, terminal obligation, and journal construction at
named invariant boundaries.

The runtimes share fixed roots for the prestate, transition context, poststate,
effect plan, private ports, terminal obligation, and journal. Boundary evidence
covers one atom, rounded fees, exact CPMM conservation, guard precedence, and
overflow in the Oracle-deviation products. It also covers hostile accepted
wrapper fields and canonical reversed-asset ordering, which rejects as
`POLICY_MISMATCH` before lane-state validation in Lean, Python, and Rust. A deterministic 100-example
generated campaign checks accepted-state determinism and conservation over a
bounded reserve and trade domain. This is bounded differential and property
evidence. It is not a universal Python/Rust refinement proof.

The Rust transition currently retains a long linear guard-and-projection body
so the release-defined rejection order remains directly inspectable while the
shared differential corpus is still incomplete. This is explicit structural
debt, not a preferred final shape. Splitting it requires before-and-after
parity for every reject class and every canonical accepted root.

The current Lean and runtime models have several explicit correspondence
obligations:

- Lean fixes one exact approved release; runtime accepts a bounded,
  content-committed local release family whose identifiers still require a
  current-profile verifier.
- Lean stores reserve principals in each pool definition; runtime derives each
  reserve principal from the canonical pool identifier and asset.
- Lean derives a mathematical profile identifier; runtime binds a local
  caller-constructible profile root and authorization record.
- Lean checks an explicit selection decomposition; runtime derives the unique
  selected pool from canonical state.
- Runtime compresses complete command and dependency coordinates into a
  cryptographic context root; no factorization or commutation theorem yet maps
  that root to Lean's injective mathematical encoding.
- Runtime additionally requires every pool's creating module release in a
  separate `ACTIVE_NEW` or `DRAIN_ONLY` registry. Lean currently requires only
  a nonzero creation release identifier.

These degree-of-freedom reductions are fail-closed runtime choices. A successor
Lean revision or an explicit abstraction/refinement theorem must cover all six
differences before the implementation is described as an exact Lean
refinement.

The profile authorization, Oracle registry snapshot, and Tokenomics source
receipt-binding root remain typed, caller-constructible inputs to this local
core. They become authority only after a current-head verifier binds them to
the active global state and exact verified receipts. No such adapter, Spot
guest, lane receipt, or production verifier is mounted by this checkpoint.

### Exact Tokenomics functional-core checkpoint

The SHADOW Python and Rust cores now implement the successor `ZDEX_TOKENOMICS`
leaf in `src/core/zdex_tokenomics_buyback_transition_v1.py` and
`zk/global_settlement_abi_v1/src/zdex_tokenomics_buyback_transition.rs`. The
leaf owns one complete tokenomics state, `ZDEXTokenomicsBuybackLaneStateV1`:
a bucket-free supply control record (asset, hyperdeflation policy root,
decimals, precision epoch, live supply, burn budget epoch, remaining epoch burn
cap), the canonical fee states, one cadence state per fee asset, and the six
unrelated component roots. The state carries no Spot pool reserve mirror, and
purchased ZDEX awaiting burn has no durable representation. This follows the
lane decomposition in `ZDEXAtomicBuybackTransitionV1.lean`, where the
tokenomics lane owns the fee-backed quote source, live supply, replay, and
burn-pending observations while the Spot lane owns the selected pool.

Phase A, `derive_zdex_tokenomics_buyback_intent_v1`, runs the ordered guards
`AUTHORITY_MALFORMED`, `RELEASE_MISMATCH`, `PROFILE_MISMATCH`,
`STATE_COMMITMENT_MISMATCH`, `SAFETY_LIMIT_MISMATCH`, `POLICY_MISMATCH`,
`LANE_MALFORMED`, and `SELECTION_MISMATCH`, then reuses the existing fee
allocation and reserve-spend kernels. The fee command is the committed fee
ingress of the governed quote asset, so no caller-selected fee budget exists.
The spend is `q = min(B0 + b, per_command_cap, route_safe_limit)`, cadence
advances to the consensus height, and the spend-phase effect plan contains the
allocation rows plus one custody debit of the buyback reserve and no lane
write. Kernel rejections surface as `SPEND_REJECTED` together with the exact
inner spend code and fee code, so an invalid phase and code combination is
unrepresentable.

The phase-A output is the acyclic semantic port `ZDEXAtomicBuybackQuotePortV2`.
It carries proof-independent producer and consumer module release ids, the
producer pre and post lane roots, the producer effect-plan root, the amount,
the pool, the quote asset, and the profile, route, occurrence, and global
pre-state coordinates. The fee-reserve source principal is fixed by the ABI;
the pool-reserve destination principal is derived from the selected pool and
quote asset. Neither principal is independently caller-selectable. The port
omits journal and receipt-binding roots. Independent review established that binding the
Tokenomics verified-leaf `binding_root` inside the Spot quote port would create
a hash fixed-point cycle through `private_port_root`, the module journal, the
receipt, and the verified wrapper. The historical `ZDEXSpotQuoteInputPortV1`
bytes are preserved unchanged; that port still requires `source_journal_root`
and `source_receipt_binding_root`, so a Spot V2 port that consumes only the
acyclic fields is required work before the two successor leaves compose without
placeholder provenance.

Phase B, `transition_zdex_tokenomics_buyback_v1`, re-derives phase A and binds
the Spot terminal obligation by recomputing both Spot flow identities from the
obligation's own context root: the purchased flow must name the governed pool,
ZDEX asset, pool reserve principal, occurrence-bound burn principal, and the
purchased amount (`PURCHASE_PORT_MISMATCH`), and the quote flow must name
exactly the derived `q` (`QUOTE_FLOW_MISMATCH`). The burn uses the existing
retained-supply arithmetic and the remaining epoch cap; `BURN_REJECTED` carries
`RETAINED_SUPPLY_FLOOR_REACHED`, `EPOCH_BURN_CAP_REACHED`, or
`BURN_EXCEEDS_CAPACITY`. The accepted result changes the fee state, cadence,
live supply, and remaining epoch cap; emits the allocation rows, the reserve
debit, one `BURN` row, quote and ZDEX conservation rows, the fee conservation
row, one `ZDEX_TOKENOMICS` lane write, and one occurrence consumption; and
never emits a row for the ephemeral burn port. The private ports value pairs
the produced quote port with the consumed obligation. The journal commits the
context root, the pre, spend-post, and post lane roots, the spend and full
effect-plan roots, `H(port)`, the ports root, the discharged obligation id, the
fee occurrence root, the spend intent root, the safety-limit binding root, and
every amount, and its construction checks `F = b + other + r`,
`B1 + q = B0 + b`, `purchased = burned`, `live_post + p = live_pre`,
`retained <= live_post`, and `cap_post + p = cap_pre`. Every rejection returns
the identical prestate with empty effects and no ports or journal. Python
accepted and intent values rederive from their frozen subject under the same
closed exact-type graph discipline as the Spot leaf; Rust accepted fields are
private.

Evidence covers fixed vectors shared by both runtimes (ten commitment roots),
composition with the real Spot leaf in both languages, spend-selection and
burn-capacity boundaries, one-atom flow through both leaves, cadence and fee
width boundaries, a deterministic 100-example spend-selection campaign and a
100-example full-transition campaign, a two-occurrence history with replay
rejection, guard-precedence mutants, obligation substitution mutants, and
accepted-value forgery. The packet is
`tests/evidence/test_hygiene/THV1-20260830-zdex-tokenomics-buyback-runtime-core-v1.json`.

The outer route composer, which does not exist yet, must pair the exact
`H(port)` consumed by Spot with the Tokenomics journal `quote_port_root` and
`private_ports_root`, pair the Spot terminal obligation id with
`discharged_obligation_id`, check the Spot consumed port fields against the V2
port, and bind both lane journals to opaque verified leaf wrappers. The
safety-limit port, the obligation context root, and the profile authorization
remain caller-constructible provenance inside this leaf. No receipt is
verified, no lane coordinator or runtime-to-Lean refinement theorem exists for
the tokenomics leaf, the fee, spend, and retained-supply parameters remain
unselected research fixtures, and no production, settlement, publication, or
value-moving authority is established.

### Lean Tokenomics formal-model checkpoint

`lean-mathlib/Proofs/ZDEXTokenomicsBuybackTransitionV1.lean` defines the
successor `ZDEX_TOKENOMICS` state machine for the same occurrence. It imports
the Spot leaf and the spend kernel, so it consumes the exact
`FlowIdentity`, `TerminalObligation`, and `selectedQuoteSpend` values those
modules define rather than re-declaring them.

The command carries no caller-selected amounts. The fee amount is the committed
fee ingress, the quote spend is the governed selection
`min(B0 + b, per-command cap, route-safe limit)`, and the burned amount is read
from the Spot purchased-ZDEX port. Closed destinations are an exact six-field
record, so destination cardinality, key, and canonical order are unrepresentable
failures rather than checked ones.

Lean proves, on the accepted transition: exact fee conservation
`F = b + sum(a) + r` over floored basis-point shares; `B1 + q = B0 + b` together
with the subtraction form `B1 = B0 + b - q`; that the spend respects the
reserve, the per-command cap, and the authenticated route-safe limit; that the
quote port carries exactly the derived spend; that the purchased port amount,
the obligation amount, the emitted burn magnitude, and the live-supply decrease
are one value; exact supply reduction with a positive post-supply; tokenomics
quote conservation, so the only quote atoms leaving the lane are `q`;
preservation of lane well-formedness and of every unrelated component root;
cadence advance under the governed interval; canonical effects that are
nonzero, lane-owned, gross rather than netted, and accompanied by exactly one
bound lane write and an empty consumed-object tuple; exact discharge of the
`MUST_BURN_PURCHASED_ZDEX` obligation with a retained nonzero route
coordination obligation; exact journal binding; and rejection as an exact
no-effect, no-discharge, no-op. Every reject family has a concrete witness.
Accepting fixtures cover the governed candidate split, the exact cadence
boundary, and a four-atom fee whose shares all floor to zero.

Three pairing theorems connect the two leaves directly: under the hypothesis
that this leaf consumes the Spot leaf's accepted ports and obligation, the Spot
quote input equals the governed tokenomics spend, the Spot purchased output
equals the tokenomics burn, the Spot quote port's source post-state and
effect-plan roots equal this leaf's derived roots, and the discharged
obligation identity and amount are the Spot-issued ones.

Every checked theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`. The file uses no `native_decide`, so no claim rests on
compiler-level evaluation.

#### Obligation-independence result

Building the first accepting witness exposed one ordering constraint the
earlier checkpoints did not state. A tokenomics effect plan that committed to
the discharged obligation identifier, or that read the burn principal from the
consumed obligation, would introduce an avoidable dependency cycle.

This release therefore takes the burn principal from the governed release and
keeps discharged obligation identifiers outside the effect-plan root, binding
them through the result and the journal instead. Three theorems check the
property directly: the accepted post-state and effect-plan root are invariant
under substituting the consumed obligation, and the derived spend is invariant
under substituting both Spot ports. The final post-state and burn effect still
depend on the purchased-output flow. These theorems therefore do not establish
the runtime's stronger acyclic two-phase construction.

#### Remaining formal/runtime abstraction gap

The Lean `TokenomicsState` is an abstract mathematical projection of the
runtime `ZDEXTokenomicsBuybackLaneStateV1`. Its injective natural-number
commitments do not model canonical bytes or cryptographic hashing. It also
consumes the historical Spot V1 mathematical port shape, while the runtime
successor emits the acyclic shared `ZDEXAtomicBuybackQuotePortV2`. An explicit
abstraction function, shared language-neutral corpus, and checked refinement
theorems are still required before the Python and Rust implementations can be
described as refinements of this model.

#### Nonclaims for this checkpoint

The model is an exact mathematical state machine over natural numbers. It does
not establish canonical-byte encoding, cryptographic root construction,
collision resistance, Python or Rust parity, RISC0 receipt verification, Spot
lane-receipt verification, route or epoch composition, migration, or ZenoLedger
publication. The route-safe quote limit, the Oracle registry root, the source
journal and receipt-binding roots, and the Spot flow preimages remain
authenticated verifier-port premises supplied to the core. The fixture
percentages, caps, minimum spend, and cadence interval are release semantics for
this bounded candidate and select no production economic policy. The pairing
theorems assume a route composer that supplies matching leaves; no such
composer, mount, or settlement authority is created here.
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
remain incomplete. The exact Spot command has bounded Python/Rust differential
evidence, with the complete Lean/runtime correspondence obligations described
above.
The successor tokenomics leaf now owns fee allocation, reserve spend, cadence,
the acyclic V2 quote port, exact burn, and supply update in one complete
state with bounded Python/Rust differential evidence. A separate Lean formal
model proves its abstract fee, reserve, burn, rejection, and conditional
cross-leaf equations. Exact canonical-byte and state-projection refinement
between those artifacts remains open. The leaf verifies no receipt, and Spot
V1 still consumes two placeholder provenance roots until a Spot V2 port exists.
The existing burn-only tokenomics coordinator does not close the route
obligation. Current-head admission, authenticated Tokenomics source receipt,
RISC0 guests, universal runtime-to-theorem refinement, migration, durable
publication, and all value-movement gates also remain incomplete. The ABI V1
global epoch verifier continues to reject persistent consumed objects. No
production, settlement, release, publication, migration, or value-moving
authority is claimed.
