# TauFold account and ZenoDEX swap integration

Status: pure joint Spot/asset/global successor implemented; connected publication remains
open. This contract selects an isolated integration, with no live migration or
activation. ZenoDEX V3 and existing intent, arithmetic and publication semantics
remain authoritative.

## Ownership and execution

```text
TauFold account host: authenticated delegation, budget reservation, durable outbox
    -> authenticated committed dispatch and exact original SwapIntent
    -> ZenoDEX: current-head authentication and independently selected route
    -> pure swap plan + complete asset/pool/LP/global reconciliation
    -> admitted economic receipt + current writer authority
    -> existing ZenoLedger publication point
    -> independently authenticated terminal outcome
    -> TauFold: settle actual spend and release the unused reservation
```

TauFold controls a spending allowance. Its reservation is not a second copy of
assets or a lock on ZenoDEX balances. ZenoDEX owns the real economic state and
must obtain the sender balance, destination balance, pool and timestamp from
one admitted snapshot. A caller-constructed context or plan grants no authority.
The destination must independently authenticate source dispatch ancestry and
the original BLS intent; an account-host policy receipt cannot replace either
that signature or a proof of the full economic transition.

There is one economic publication point. The future swap route must extend the
existing isolated publisher's complete atomic record and recovery replay. It
must not acknowledge a reservation merely because a quote or pure plan exists.
Genesis, full pool/LP ownership, asset-origin policy, fees, both lane roots,
global tables, nonce/replay and terminal delivery identity need one compatible
profile. Historical custody and margin formats remain unchanged.

## Implemented economic component

`src/core/spot_swap_plan_v2.py::plan_spot_swap_v2` consumes the actual immutable
`SwapIntent`, explicit scalar account context and a complete immutable snapshot
of every existing `PoolState` field. Legacy mutable pool inputs are copied;
foreign subclasses and malformed structural values reject before execution.
Returned values retain no caller-owned mutable pool or intent fields.

The component supports one active CPMM pool in either direction and exact-input
or exact-output commands. It uses the existing v8 settlement quote functions.
Ceil fees, floor output, minimal exact-output gross input, reserve/amount bounds
and the existing 200-bps exact-output overdelivery ceiling are retained. The
isolated policy retains the entire rounded fee in pool reserves, as the existing
zero-protocol-share donor does; this does not select whole-product fee shares.
LP supply and all other pool metadata remain unchanged.

The closed field set is pool, input/output assets, positive-u32 nonce, the
appropriate amount/minimum or maximum, and optional recipient. Extra quote,
oracle or routing fields reject instead of being ignored. Deadline comparison
uses the explicitly supplied block timestamp, preserving `validation.py`.

The result contains the exact intent, complete pre/post pool, actual input,
output and fee, and both resulting account balances. Per-asset account and pool
deltas cancel; holdings remain nonnegative, recipient balances fit u128,
post-reserves remain in the next input's domain and pool product does not fall.
A rejected command returns no plan and changes no inputs. Structural rejection
uses TypeError/ValueError; economic rejection uses a closed reason enum.

The scalar balances are independently supplied data. Full LP ownership tables,
asset policy, global projection, authenticated nonce/time, Rust refinement,
receipt verification and store publication are outside this component. The
publicly constructible plan must be rederived inside the qualified acceptance
path. It is not a verified witness or a complete SPOT lane implementation.
In particular, retained LP supply does not establish valid pool genesis or
claimant backing. A global consumer must establish those conditions before
admitting even an arithmetically valid plan.

## Complete pure joint successor

`spot_swap_state_v2.py` commits one pool, its complete LP owner/share table,
all four existing LP duration/churn metadata fields (including dormant owners),
and ordered per-sender intent nonces. LP shares sum exactly to the pool supply;
the existing minimum locked-owner position remains present. Pool identity uses
the existing canonical parameter hash. This is a new candidate schema, not an
importer or migration of historical state. Both owner tables reuse the existing
4096-row ceiling and the state reuses the 1-MiB canonical-byte ceiling. Capacity
is checked before traversing raw rows, including forged exact-type inputs.

LP/nonce owners and joint swap sender/recipient must already use lowercase,
0x-prefixed 48-byte public-key encoding, matching legacy committed state.
Prefix/case aliases deliberately reject in this candidate profile; signed bytes
are never rewritten. This establishes unique identity text, not BLS point
validity or proof of possession. The all-zero minimum-lock owner remains valid.
Historical decoding and the lower-level scalar planner remain unchanged.

`spot_swap_global_v2.py::transition_spot_swap_global_v2` snapshots the complete
asset, Spot and global inputs, binds every original intent field and occurrence,
and derives both account amounts from that state. Physical pool holdings use
the existing asset custody table under `spot_pool`, keyed by canonical pool ID
and asset. Exactly two rows must equal the two reserves; a second reserve ledger
or nominal atom claims on these same holdings are inadmissible in this profile.
The complete asset projection and both lane roots/releases must match. Asset
origins must validate, assets must be enabled and non-native with eight atom
decimals. This isolated route admits zero asset transfer fees; composition with
nonzero token-transfer fees remains unsupported rather than silently omitted.

An accepted swap updates two account holdings, two pool custody holdings, both
lane roots, height, the global replay entry and the sender's Spot intent nonce.
The existing generic global refiner checks the complete economic tables and
effects. Fee allocation annotates the input custody increase and is counted
once in physical holdings. Unrelated custody, liabilities, terminal obligations,
oracle state, history and outbox remain unchanged. Public graph getters return
detached values; outputs and statement hashes confer no authority.

LP owners, shares, supply and metadata remain unchanged during swaps. Withdrawal
rights retain the existing floor-proportional burn rule over current reserves.
Recomputing fixed atom entitlements per holder would introduce a new rounding
and dust-allocation policy; this representation avoids that obligation. It
does not implement LP mint, burn, transfer, pool closure or locked-share terminal
disposition. These remain required lane work.

The inner signed intent nonce must equal the sender's last nonce plus one, as
the existing singleton-intent policy requires. It is independent of the outer
occurrence nonce: asset outer1, swap inner1/outer2, asset outer3, swap inner2/outer4
is valid. Inner reuse/gaps and outer replay reject with no consumed nonce or
economic effects. A full nonce table permits existing owners to advance while
rejecting a new row. The statement binds the explicit block timestamp; its
authentication and provenance remain shell obligations.

The joint successor is Python-only and unmounted. Rust refinement, a guest and
exact journal, genuine economic receipts, admitted genesis, authenticated
dispatch, publisher recovery and terminal delivery remain open. Existing custody
and margin receipts cannot certify this new Spot transition.

## Rust exchange patterns reused through FCIS

The September 14 source comparison supports custody plus shares as the smallest
current representation. It does not qualify any external deployment or establish
an incident-free history.

| Pinned source | Useful pattern | ZenoDEX boundary |
| --- | --- | --- |
| [Raydium CPMM `59fb845a9…`](https://github.com/raydium-io/raydium-cp-swap/blob/59fb845a9e5bb569c8b2f3415f13b0c0ebcc6b92/programs/cp-swap/src/states/pool.rs#L200-L220) | Bind exact vaults and LP supply; subtract separately owned fee buckets from accounted reserves. | The selected all-fees-retained profile needs no separate fee bucket. Keep ZenoDEX's explicit locked LP owner and existing rounding. |
| [Orca `408c945fe…`](https://github.com/orca-so/whirlpools/blob/408c945fef4c49ab70def4303377cfaf8f0f3c99/programs/whirlpool/src/manager/position_manager.rs#L7-L52) | Position fee-growth checkpoints avoid updating every LP on each swap. | CPMM shares already avoid per-owner repricing. Add accumulators only for separately claimable fees; do not copy wrapping/overflow-to-zero semantics. |
| [Astroport `ad95c2084…`](https://github.com/astroport-fi/astroport-core/blob/ad95c208468a3797ebf1c45f91e888f1d2e938c6/contracts/pair/src/contract.rs#L507-L598) | Compute proportional withdrawals and return explicit transfer/burn messages. | Reuse pure plans plus shell effects, preserving ZenoDEX's own pre-state timing and accounting. |

Solana provides [atomic transaction execution](https://solana.com/docs/core/transactions)
and token-program authority checks; Rust alone does not. The corresponding FCIS
obligations are authenticated snapshot acquisition, complete deterministic
transition checking, and one atomic authorized publication. Transport replay
protection does not eliminate replay of a business intent inside a new outer
transaction. Existing ZenoDEX nonce, fee and rejection policies remain pinned.

## Terminal reconciliation

Bind source configuration, actor, workflow, step, delivery/entry identity,
reservation, exact intent and destination occurrence. Commit destination dedup
with the economic result. An exact retry returns that same committed result.
For maximum reservation m and authenticated actual debit x <= m, settle x and
release m-x. The concrete test reserves 10, requests output 7, spends 9 and
leaves 1 available for release after authenticated settlement.

Response loss leaves the reservation pending until the committed result is
recovered. Timeout, ordinary rejection and queue acknowledgement cannot release
it: the command may still commit on retry. Cancellation needs a durable
destination fence establishing that the intent cannot later commit. Revocation
prevents new reservations while preserving outstanding liabilities.

## ZenoFCIS 1.1 lessons and compatibility

The reviewed source is ZenoFCIS commit
`3b2224d5a081e7ab3e2e282ad6704bcb177d25ac` (v1.1.0). Its
[bounded completion contract](https://github.com/TheDarkLightX/ZenoFCIS/blob/3b2224d5a081e7ab3e2e282ad6704bcb177d25ac/docs/BOUNDED_COMPLETION.md)
provides checked finite exit plans and ordered preparation. Use completion
checking for declared lifecycle/capacity models only after relating those models
to real runtime guards. Strictly decreasing ranks do not supply scheduling,
economic eligibility or external finality.

PreparedFold retains all inputs and checks the starting root, version and
invocation on finish. Its logical budget excludes the application's complete
candidate, receipt and outbox. Reuse the ordinary catalog/law authority and
atomic shell after preparation; independently bound the complete publication.
The extension supplies no smaller final commit, persistent partial checkpoint
or operating-system memory limit. Source inspection is not release replay.

TauFold's existing pinned FCIS host remains an immutable historical subject.
Any 1.1 adoption needs a separate source/profile identity and fresh compatibility
and recovery replay. This component introduces no FCIS dependency or schema
change. Native proof-work reuse is deferred until the full route is qualified.

## Next executable acceptance

Connect one authentic committed TauFold dispatch to this economic component,
complete global reconciliation and the existing publisher. Require successful
publication plus retained refusals for wrong source/intent/subject/head/profile,
duplicate or conflicting delivery, insufficient holdings, response loss,
restart and contradictory terminal outcomes. A test credential or protocol
receipt fixture must not be described as a genuine economic proof.
