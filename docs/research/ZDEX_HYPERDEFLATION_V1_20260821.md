# ZDEX Hyperdeflation V1 Research Contract

Date: 2026-08-21

Status: `EXPERIMENTAL_UNMOUNTED`

Production authority: `NONE`

## Scope

This packet defines a finite, integer-safe ZDEX burn leaf and an exact
denomination-rescale transition. It replaces the proposed fixed percentage
supply floor with a per-occurrence retained-supply rule. It does not alter the
legacy tokenomics release, mount a writer, authorize a token sale, or prove the
AMM pricing rule. The packet now includes an unmounted candidate fee-allocation
core. Governance has not selected its percentages or hosting policy.

The intended economic lifecycle is:

```text
protocol fee revenue
  -> governed quote asset allocation
  -> proved AMM purchase of ZDEX
  -> route-bound ZDEX source bucket
  -> exact ZDEX burn leaf
  -> one atomic global commit
```

Independent Rust and Python burn cores consume typed route context and bind the
exact purchase occurrence, source bucket, amount, policy, pre-state root, and
precision epoch. The canonical supply state also commits the burn-budget epoch
and its remaining capacity; acceptance decrements that capacity. The Rust
retention calculation uses quotient/remainder decomposition to avoid a
`u64 * u128` intermediate overflow. A deterministic Rust/Python refinement
derives the route burn journal and global effects from the accepted transition
and the exact purchase journal it names. The refinement authenticates no
receipt and grants no authority. A separate
Rust/Python shadow composer models receipt admission for exact Spot and
tokenomics leaf journals through release-selected verifier ports and pairs their
effects. Independent Rust and Python fee-allocation cores derive a
buyback-budget occurrence from a charged-fee bucket. An unmounted RISC0 3.0.6
workspace now reuses the Rust allocation transition, commits only the canonical
allocation occurrence, requires `Succinct` receipt shape, and rejects
placeholder methods and noncanonical receipt encodings. A second unmounted
RISC0 3.0.6 workspace reuses the exact Rust burn transition and route
refinement, commits only the canonical burn journal, bounds input and receipt
bytes before decoding, requires `Succinct` receipt shape, and rejects
placeholder methods and noncanonical receipt encodings. A third unmounted
RISC0 3.0.6 workspace reuses the complete tokenomics-lane coordinator, verifies
the exact burn leaf as a guest assumption, and commits only the canonical
complete-lane journal. The real AMM purchase guest, generated images and
receipts, governed percentage and host-compensation selection, recursive route
proof, active profile admission, and atomic global commit remain separate
obligations.

## Candidate fee-allocation contract

The closed destination order is:

```text
BUYBACK
QUALIFIED_HOST_POOL
TREASURY
PROOF_REWARDS
COVER_RESERVE
LP_REBATES
```

The current research candidate assigns, in basis points:

```text
(2000, 0, 3000, 1000, 1000, 500)
```

The assigned total is 7,500 bps. The remaining 2,500 bps is deliberately
unassigned. A zero candidate host share records an unresolved policy decision;
it does not select zero host compensation for a release.

For one admitted charged-fee input `F` and destination share `b_i`:

```text
A_i = floor(F * b_i / 10000)
R = F - sum(A_i)
F = sum(A_i) + R
```

`R` combines unassigned-share value and integer rounding dust. The transition
moves `R` into the named `protocol:fee-unallocated-reserve`. No command in this
packet spends that reserve. A later release needs a separate governed command
and evidence before those atoms may move.

The immutable state records the fee asset, policy root, charged-fee ingress,
destination balances, residue reserve, total controlled amount, and supply.
An accepted transition checks selected-balance conservation, unchanged supply,
an exact `FeeConservationRowV1`, no lane write, and no external outbox effect.
Its roots describe one fee-asset substate, so only the complete-lane
coordinator may emit a tokenomics lane write. Zero fees, policy drift,
insufficient ingress, and signed-effect width excess produce typed no-effect
rejection.

The allocation occurrence commits chain, deployment, profile, writer epoch,
allocation route, authorized buyback route, tokenomics release, command
occurrence, fee asset, all six allocations, residue, lane roots, and effect-plan
root. Rust and Python golden tests agree on the policy, state, effect, and
occurrence commitments.

## Integer contract

Let:

```text
S = positive live ZDEX supply in current-epoch atoms
0 < p < q = committed dimensionless retention policy
R(S) = 1 + floor((p*S - 1) / q) = ceil(p*S / q)
```

For a burn amount `b`, the ratio guard is:

```text
0 < b <= S - R(S)
```

The full implemented burn capacity is:

```text
B_max = min(
  S - R(S),
  source_atoms - source_reserve_floor_atoms,
  committed_remaining_epoch_burn_cap_atoms,
  route_epoch_burn_ceiling_atoms,
  route_safe_output_cap_atoms
)
```

Every accepted burn satisfies:

```text
S_post = S_pre - b
S_post >= R(S_pre) >= 1
source_debit_atoms = authorized_burn_atoms = b
authorized_issue_atoms = 0
sum(post_buckets) = S_post
remaining_epoch_burn_cap_post
  = remaining_epoch_burn_cap_pre - b
```

This is not a floor at a fixed percentage of initial supply. For example,
`p/q = 9/10` permits at most ten percent of the current supply per admitted
occurrence, subject to the other caps. Repeated finite burns can reduce supply
below ten percent of its initial value while each accepted state remains
positive.

## Exact fixed-precision threshold

Positive burn headroom exists exactly when:

```text
q <= (q - p) * S
```

Equivalently, the first integer supply with positive ratio headroom is:

```text
S_min = ceil(q / (q - p))
```

Below this threshold, the current atom precision cannot express another burn
under the committed fraction. The transition returns
`PRECISION_RESCALE_REQUIRED` with identical pre-state, post-state, and no
effects.

## Route authority binding

The verifier-supplied `ZDEXBurnRouteContextV1` binds:

- route release ID;
- policy root;
- purchase occurrence root;
- burn source bucket;
- exact purchased ZDEX atoms;
- burn-budget epoch;
- source-reserve, route-epoch, and route-output ceilings.

The burn journal commits the canonical root of this complete route context.
Changing a nonlimiting ceiling therefore changes the public statement even when
the same amount and supply transition would still accept.

The command must repeat the purchase occurrence root, source bucket, and exact
purchased amount. Any mismatch returns `PURCHASE_BINDING_MISMATCH` with no
effect. A route context from another committed burn-budget epoch returns
`BURN_BUDGET_EPOCH_MISMATCH`. The state-owned remaining capacity is
authoritative; the route ceiling can only reduce it. The accepted result carries
the policy and route context, recomputes its capacity, and consumes the exact
burn from committed capacity before construction succeeds.

The burn-journal refinement also recomputes the purchase effect-plan root and
requires the purchase route, policy, journal root, ZDEX asset, amount, aggregate
owned value, supply, and transient burn bucket to equal the checked burn. The
checked supply-state roots are explicitly tokenomics burn-substate roots. They
do not claim to be complete tokenomics lane roots. The source bucket must
contain exactly the purchased amount before the burn and be absent afterward;
partial source-bucket burns remain valid in the general core but cannot be
presented as the atomic purchase-to-burn route leaf. The tokenomics module
release ID is an explicit nonzero input whose registry membership remains an
outer release-verifier obligation.

This burn-leaf context does not authenticate the purchase by itself. The shadow
route composer performs the next structural step: it verifies release-selected
succinct receipt envelopes for exact canonical leaf journals and requires one
shared route, occurrence, profile, writer epoch, issue/burn policy, governed
buyback-budget occurrence, quote input, ZDEX asset, purchased amount, and
transient burn bucket.

The buyback-budget occurrence must authorize the exact purchase route, use the
same chain, deployment, profile, writer epoch, tokenomics release, and quote
asset, allocate the exact quote input, and target the closed protocol buyback
bucket. A shadow receipt-admission boundary recomputes the allocation from the
candidate policy, pre-state, and charged fee before constructing a witness.
Profile selection is a separate verifier input. The verifier first binds the
expected profile ID and authority epoch to one `SHADOW` economic profile, its
lane, coordinator, and route registries, and a canonical economic-policy
registry. The policy registry contains one exact
`(policy_kind, command_kind, policy_root)` binding and is bounded to 256
canonically ordered bindings. The fee receipt candidate cannot supply module
releases, routes, guest image IDs, or the selected
profile. Those values are derived from the verifier-selected registries.
Self-consistent alternative release graphs, same-ID status substitutions,
independent lane/coordinator/route-registry substitutions, trusted authority
epoch substitutions, policy-registry substitutions, occurrence-profile
substitutions, and journal epoch substitutions reject before the
receipt-verifier port is called.
The Python composer repeats that recomputation because Python module internals
cannot provide same-process authority. The Rust witness constructor is private.
The buy-and-burn command lists the budget root in its exact consumed-object set.
Its effect plan consumes only the buy-and-burn command occurrence, matching the
global epoch effect contract. Composer tests use an injected accepting verifier
and contain no cryptographic proof. Fast RISC0 workspace tests use a deliberate
placeholder method and therefore also contain no cryptographic proof. The
expected profile ID and authority epoch must eventually come from the sole
settlement shell under its consensus/write lock. Historical inclusion,
persistent global consumed-object enforcement, a generated guest image, and a
real allocation receipt remain open.

The purchase journal commits these exact balance projections:

```text
buyback quote source: Q_source_post + Q = Q_source_pre
AMM quote balance:    Q_pool_pre + Q = Q_pool_post
AMM ZDEX balance:     Z_pool_post + B = Z_pool_pre
transient burn bucket: 0 -> B
```

The burn journal commits:

```text
transient burn bucket: B -> 0
ZDEX controlled balances post + B = pre
ZDEX supply post + B = pre
```

Shadow composition cancels the transient `+B` and `-B`, emits exactly one
authorized ZDEX supply burn of `B`, consumes the command occurrence once,
retains the complete Spot lane write, and emits no external outbox row. It emits
no tokenomics lane write from the partial burn substate. Its nonzero
terminal-obligations root commits `VERIFIED_COMPLETE_LANE_ROOT`, so the common
epoch verifier cannot admit it until a tokenomics lane coordinator proves and
supplies the complete lane transition. Any binding or history mismatch returns
a typed rejection with an empty effect plan.

The source-level coordinator core now defines a closed tokenomics-lane envelope
containing the exact ZDEX supply state, a canonical registry of one to 64
fee-allocation states uniquely ordered by fee asset, and explicit component
roots for staking, qualified-host claims, treasury claims, proof rewards, cover
reserves, and LP rebates. Global replay, terminal-obligation, profile-policy,
and history commitments retain their existing owners in `GlobalEconomicStateV1`
and `EconomicProfileSnapshotV1`; the lane root does not duplicate them. For a
burn, every component except the supply state must remain canonically equal.
The coordinator requires the burn module journal to
leave its lane roots at zero, binds the burn-substate private port and its
`VERIFIED_COMPLETE_LANE_ROOT` obligation, checks the exact burn journal and
effects, and derives one common `LaneCompositionJournalV1` with the complete
pre/post lane roots and one canonical tokenomics lane write. Attempts to place
the partial burn-substate roots in the module journal's lane-root fields reject
as `PARTIAL_LANE_ROOT_CLAIM`. The module journal's `receipt_root` is a
deterministic commitment to the burn journal, substate roots, effect plan,
private port, and terminal obligations. It binds the statement supplied to the
coordinator; receipt authentication remains the verifier's responsibility.

The Rust and Python shadow receipt boundaries require an existing opaque
`VerifiedZDEXBurnV1`, bind its exact module image to the governed module
release, recompute the complete lane transition, and ask the injected verifier
to admit the byte-exact lane journal under the profile-selected coordinator
image. Only then can they construct an opaque process-local
Rust `VerifiedZDEXTokenomicsLaneV1` or the corresponding guarded Python marker.
Their binding roots have Rust/Python golden parity. Rust keeps the witness
fields private. Python's constructor token is
process-local misuse resistance and carries no authority; Python also
revalidates the content-derived profile and selected releases immediately
before every verifier call. The unmounted coordinator guest repeats the same
Rust preflight, calls
`env::verify` for the exact child image and journal, and commits the complete
lane journal. Its host adds the real child receipt as the sole assumption,
requires unconditional `Succinct` child and coordinator receipts, and verifies
both exact journals and images.

The current route composer deliberately retains its nonzero coordinator
obligation and does not consume the verified lane witness. Generated guest
images, a real child receipt, a real recursive coordinator receipt, exact route
connection, and release/source/toolchain manifests are required before the
route may carry the full tokenomics lane write or clear the obligation. The
existing fee-allocation occurrence fields named
`pre_lane_root`/`post_lane_root` still commit only the fee-allocation substate.
The source-level Rust and Python fee-allocation coordinator preserves those V1
canonical bytes, binds them through a typed private port and module journal,
and embeds exactly one changed fee asset in the complete tokenomics lane. It
rejects partial-root claims, changed sibling fee assets, changed supply or
claim-component roots, route substitutions, and module-receipt substitutions
with an unchanged lane root and empty effects. It reruns the supplied
fee-allocation policy and exact leaf transition, so a policy witness that is
inconsistent with the bound allocation cannot become a module statement.
Rust/Python golden roots agree. A coherently regenerated alternative policy is
rejected only when governed admission compares it with the profile-selected
policy root; that adapter remains a promotion gate.

The SHADOW RISC0 tokenomics coordinator now has two disjoint canonical input
schemas under one coordinator image: the historical burn schema and a policy-bound
fee-allocation schema. Schema dispatch is closed, both paths recompute the
complete lane journal, and the guest resolves the exact release-selected child
image and journal as its sole assumption. Host preflight admits only an
unconditional Succinct child receipt with byte-identical journal output. The
fee path has lightweight compile and negative preflight evidence; a rebuilt
coordinator image, real fee child plus coordinator proof, content-derived
coordinator release, profile-selected policy and receipt adapter, release-bound
cycle enforcement, and route connection remain open.

All receipt-admission implementations are deliberately `SHADOW`-only.
`ACTIVE_NEW`, composite, conditional, empty, wrong-effect, and
verifier-rejected inputs fail the reference boundaries. Generic injected test
verifiers can accept fixture bytes and therefore grant no cryptographic claim.
The pinned RISC0 adapters additionally reject fake, development-mode,
placeholder, noncanonical, wrong-image, and wrong-journal receipts. No generated
burn or coordinator image and no real burn or coordinator receipt is present.
The accepted shadow composition is also not yet a common
`RouteCompositionJournalV1`; it cannot enter epoch recursion or publication.

## Exact denomination rescale

For additional decimal precision `k > 0`:

```text
F = 10^k
decimals_post = decimals_pre + k
precision_epoch_post = precision_epoch_pre + 1
bucket_atoms_post[i] = bucket_atoms_pre[i] * F
S_post = S_pre * F
remaining_epoch_burn_cap_post = remaining_epoch_burn_cap_pre * F
```

All buckets in the supplied projection must be present exactly once and in
canonical order. V1 bounds that projection to 1,024 entries. Authentication and
complete global bucket coverage remain separate obligations. Cross
multiplication proves that represented token quantity is unchanged:

```text
atoms_post * scale_pre = atoms_pre * scale_post
scale_post = scale_pre * F
```

The Python research core uses u128 atom bounds, u64 epoch and policy fields,
and a maximum single rescale step of 38 decimals because `10^38` fits u128 and
`10^39` does not. It rejects overflow before multiplication.

Finite u128 storage, a finite maximum-decimals policy, and a u64 precision
epoch still impose a terminal representation envelope. This packet therefore
makes no claim of literal infinite execution on finite hardware. A future
release can extend the envelope only through a new proved representation and
migration contract.

## Global ABI blocker

`GlobalSettlementABI V1` currently expresses supply movement as:

```text
supply_post = supply_pre + authorized_issue - authorized_burn
```

A denomination rescale multiplies atom counts while preserving represented
economic quantity. Recording the multiplication as issuance would be
economically false. Recording zero issuance and zero burn would violate the V1
atom-count equation.

Consequently, denomination rescale cannot be mounted under
`GlobalSettlementABI V1`. It requires an ABI revision that commits the unit
scale and proves value-preserving migration across every ZDEX-denominated
bucket, liability, threshold, price representation, pending obligation,
receipt consumer, API, client, and historical decoder.

## Disaster-state closures

| Disaster state | Current closure | Remaining obligation |
|---|---|---|
| Supply reaches zero through rounding | Ceiling retention, positive-supply theorem, tested Rust/Python golden-vector root parity including u128/u64 extremes, and a source-level burn guest wired to the exact Rust transition | Generated burn image, in-VM execution and real receipt, complete result-encoding vectors, and release-selected policy/state binding |
| Caller invents the purchased amount | Exact purchase journal, verifier witness, occurrence, source, and amount binding in a shadow route | Real Spot guest and governed profile membership |
| Preexisting ZDEX is mixed into the purchase output | Purchase transient bucket must project `0 -> B` | Complete global balance-root connection in the Spot guest |
| Purchased ZDEX is only partly burned | Burn transient bucket must project `B -> 0`; the burn guest preflight rejects partial drain and composed transient rows cancel | Generated burn receipt, real coordinator receipt, recursive route proof, and atomic commit |
| Burn journal is assembled independently from the checked transition | Rust/Python refinement derives the journal, burn-substate roots, route-context root, totals, and effects; the source-level burn guest reruns that Rust refinement; coherent amount, route, policy, asset, bucket, total, and nonlimiting-cap substitutions are distinguished or reject | Generated burn image and real receipt plus release-selected receipt verification |
| Partial burn substate is presented as the complete tokenomics lane | Burn journal fields are explicitly named burn-substate roots; leaf effects emit no tokenomics lane write; the coordinator source and guest reject partial lane-root claims and preserve every unrelated component commitment; shadow receipt admission requires the exact verified burn leaf and complete-lane journal; route composition retains a nonzero complete-lane obligation | Generated coordinator image, real child and coordinator receipts, release-backed lane-state registry, route connection, and atomic publication |
| Python value is mutated after constructor validation | Accepted burn inputs, fee state, common module journals, effect plans, coordinator values, and purchase/burn journals revalidate at refinement, effect projection, root computation, or coordinator admission; hostile scalar and root mutations are regression tested | Python values remain non-authoritative until a release-selected proof verifier admits the exact journal |
| Rejected transition changes value | Canonically equal pre/post state and empty effects; Python also preserves object identity | Runtime adapter parity |
| Epoch ceiling is reused by sequential burns | Burn-budget epoch and remaining capacity are committed in the pre-state and decremented in the post-state; stale larger route ceilings cannot increase capacity | Profile-selected epoch reset transition, guest execution, and global sequencing |
| Fee split loses atoms to truncation or is coherently rewritten | Exact allocation-plus-residue equation, named reserve, policy-bound transition replay, and a mutation test that shifts one atom between destinations while updating state/effects/roots | Governed residue-release lifecycle and proof-backed policy selection |
| Fee-allocation substate is presented as the complete tokenomics lane | Source-level Rust/Python coordinator replaces the partial write with one complete-lane write, preserves every sibling component, and has golden-root parity plus mutation-killing no-op tests; the SHADOW RISC0 coordinator recomputes the same complete-lane statement and verifies the exact fee child assumption | Rebuilt image, real recursive proof, governed coordinator release and receipt adapter, route connection, and atomic publication |
| Caller invents a buyback budget | Shadow route recomputes the fixed-policy allocation and binds journal digest, state roots, amount, source, and consumed-object ID; this rejects semantically invalid invented budgets | Real allocation guest receipt, historical inclusion, and persistent global consumed-object enforcement |
| Buyback budget debits another holder | Closed protocol buyback source bucket in both composers | Complete mounted caller inventory |
| Accepted allocation wrapper shifts value between destinations | Independent transition recomputation rejects a sum-preserving allocation mutant before receipt verification | Real guest/image evidence and profile-selected policy registry |
| Burn secretly issues ZDEX | Effect requires zero authorized issuance | Complete writer inventory |
| Test faucet mints protocol ZDEX | Source guard and authored exact no-state-change scenario reject the canonical protocol-token asset | Dependency-closed integration replay; this branch lacks the tracked consensus-time donor required to import the plugin |
| Partial denomination migration | All supplied projection buckets and the remaining burn budget scale exactly or transition rejects | Complete global ZDEX bucket registry and atomic migration |
| Multiplication or epoch overflow | Python pre-multiplication guard, Rust widened quotient/remainder retention, checked rescale, and u64 epoch exhaustion | Guest execution and independent arithmetic review |
| Oversized serialized input exhausts decoding resources | Supply-state decoding rejects more than 1,024 projection rows; the burn guest and host enforce a 1 MiB canonical-input ceiling before decoding; receipt admission enforces a 16 MiB ceiling and the ABI journal ceiling | Apply equivalent pre-decode bounds to every remaining guest and mounted adapter; parsed string allocation elsewhere remains outside this leaf |
| Old receipt is replayed after rescale | Precision epoch and pre-state root binding | Global nonce/nullifier and profile binding |
| Buy-and-burn has no market demand | No mathematical closure claimed | Economic and liquidity analysis |
| Hosting becomes privileged control | No privilege is granted by this core | Permissionless host protocol and failover evidence |

## Autonomous operation constraint

The target architecture uses permissionless mechanical operation:

- any qualified host may perform the same typed work under the same rules;
- host compensation is determined by committed protocol policy;
- AI agents submit ordinary authenticated commands and receive no publication,
  settlement, release-selection, or emergency override authority;
- deterministic verifiers decide admission;
- no promoter-controlled agent is required for ordinary operation;
- development promises, upgrade authority, and any token-offering lifecycle are
  recorded separately from protocol operation.

These constraints reduce discretionary managerial dependence and improve the
technical autonomy claim. They do not determine whether any offer or sale is a
security. Legal classification depends on facts, communications, control, and
the applicable law at the time.

SEC Release No. 33-11434 was supplied as a proposed-rule input. Proposed rules
are not operative exemptions. This packet grants no sale authority. Sale
proceeds must remain separate from recurring protocol fees and buy-and-burn
accounting unless a release-specific legal and economic review approves an
exact design.

## Evidence in this packet

- `src/core/zdex_hyperdeflation_types_v1.py`: closed immutable ABI values;
- `src/core/zdex_hyperdeflation_math_v1.py`: pure retention, capacity, and
  bucket-projection arithmetic;
- `src/core/zdex_hyperdeflation_results_v1.py`: self-recomputing accepted and
  exact no-effect rejected values;
- `src/core/zdex_hyperdeflation_v1.py`: narrow transition orchestration and
  stable public import surface;
- `tests/core/test_zdex_hyperdeflation_v1.py`: BDD, BVA, mutation-killing,
  malformed-input, exhaustive-small-domain, stateful epoch-capacity,
  reject-no-effect, projection-bound, and Rust-root golden evidence;
- `zk/global_settlement_abi_v1/src/zdex_hyperdeflation_types.rs`, the bounded
  decode, transition-result, and accepted-validation siblings, and
  `zdex_hyperdeflation.rs`: independent checked Rust projection with widened
  retention arithmetic, fail-closed input/state decoding, exact burn/rescale
  transitions, crate-controlled accepted values, and typed no-effect rejection;
- `zk/global_settlement_abi_v1/tests/zdex_hyperdeflation.rs`: every reject code,
  sequential epoch-capacity consumption, exhaustive small-domain positivity,
  38/39-decimal BVA, u128/u64 arithmetic and root boundaries, bounded malformed
  decode, and Python/Rust policy/pre/post-root golden evidence;
- `src/core/zdex_hyperdeflation_route_refinement_v1.py` and the matching Rust
  module: self-recomputing, non-authoritative checked-burn to route-journal and
  effect-plan refinement;
- `tests/core/test_zdex_hyperdeflation_route_refinement_v1.py` and the matching
  Rust test: coherent-substitution, partial-drain, stale-effect-root, output
  mutation, hostile post-construction revalidation, no-outbox, and three-root
  cross-language golden evidence;
- `lean-mathlib/Proofs/ZDEXHyperdeflationV1.lean`: machine-checked restricted
  theorems for ceiling equivalence, the exact headroom threshold, positive
  retained supply, accepted-burn positivity, guard necessity, exact bucket
  scaling, and finite geometric positivity;
- `tests/formal/test_lean_zdex_hyperdeflation_v1.py`: placeholder scan and
  focused Lean elaboration;
- `src/core/zdex_purchase_burn_*_v1.py`: immutable shadow journals, canonical
  effects, release-selected receipt admission, process-local witness markers,
  and pure two-lane composition;
- `zk/global_settlement_abi_v1/src/zdex_purchase_burn_*.rs`: independent Rust
  projection of the same journals, effects, receipt boundary, and composer;
- `tests/core/test_zdex_purchase_burn_route_v1.py` and
  `zk/global_settlement_abi_v1/tests/zdex_purchase_burn_route.rs`: BVA,
  substitution, malformed-receipt, shadow-promotion, exact-once transient
  bucket, no-effect rejection, and cross-language composition-root evidence;
- `src/core/zdex_fee_allocation_types_v1.py` and
  `src/core/zdex_fee_allocation_v1.py`: immutable candidate fee types,
  canonical effects, typed rejection, and pure transition;
- `src/core/zdex_fee_allocation_receipt_verification_v1.py`: shadow-only exact
  transition recomputation and non-authoritative process-local allocation marker;
- `zk/global_settlement_abi_v1/src/zdex_fee_allocation_types.rs` and
  `zk/global_settlement_abi_v1/src/zdex_fee_allocation.rs`, plus the receipt
  verification module: independent checked Rust projection of the candidate
  allocation core and its shadow admission boundary;
- `zk/zdex_fee_allocation_risc0`: unmounted RISC0 3.0.6 guest source, canonical
  input/journal seam, pinned succinct-receipt host adapter, placeholder and fake
  receipt denial, receipt-size BVA, and an ignored real-proof replay target;
- `zk/zdex_hyperdeflation_burn_risc0`: unmounted RISC0 3.0.6 burn guest source,
  canonical bounded input/journal seam, exact shared transition and refinement,
  pinned succinct-receipt host adapter, placeholder and fake receipt denial,
  input/journal/receipt BVA, typed development-mode rejection, and an ignored
  real-proof replay target;
- `src/core/zdex_tokenomics_lane_v1.py`,
  `src/core/zdex_tokenomics_lane_coordinator_v1.py`, and
  `zk/global_settlement_abi_v1/src/zdex_tokenomics_lane_*.rs`: closed
  multi-fee-asset tokenomics-lane envelope without duplicated global
  commitments, burn private port, exact unrelated-component preservation,
  deterministic module-statement commitment, typed no-effect rejection,
  canonical full-lane write, common lane-composition journal derivation, and
  shadow release-selected receipt admission requiring an exact verified burn
  leaf before constructing a non-authoritative process-local lane marker;
- `tests/core/test_zdex_tokenomics_lane_coordinator_v1.py` and the matching Rust
  test: every typed coordinator rejection branch, fee-registry width/order BVA,
  partial-lane-claim rejection, all-component preservation, malformed
  post-construction revalidation, self-consistent forged leaf-total rejection,
  route/private-port/substate/module-receipt substitution, foreign verified-leaf
  rejection, profile/image/journal/receipt-shape admission failures, verifier
  rejection, journal-byte BVA, and Rust/Python lane-witness golden parity;
- `zk/zdex_tokenomics_lane_coordinator_risc0`: unmounted RISC0 3.0.6 recursive
  coordinator source, exact governed module-release preflight, guest-side
  `env::verify` over the child image and canonical burn journal, host-side
  `add_assumption` with unconditional `Succinct` enforcement, bounded
  input/journal/receipt admission, placeholder and development-mode denial, and
  an ignored real recursive-proof replay target;
- `tests/core/test_zdex_fee_allocation_v1.py` and
  `zk/global_settlement_abi_v1/tests/zdex_fee_allocation.rs`: denominator BVA,
  exhaustive small-domain conservation, no-effect rejection, route binding,
  hostile Python scalar, and five-commitment cross-language golden evidence;
- `src/integration/tau_testnet_dex_plugin.py`: testnet faucet exclusion for the
  canonical protocol-token asset;
- `tests/integration/test_tau_testnet_dex_plugin.py`: exact rejection and
  no-state-change scenario. This scenario is authored but is not counted as
  replayed branch evidence because `src/core/consensus_time.py` is absent from
  this branch; the original dirty checkout contains a different untracked
  candidate that was deliberately not copied into this packet.

## Promotion gates

This work remains `EXPERIMENTAL_UNMOUNTED` until all of the following exist:

1. a normative ZDEX tokenomics release selecting `p/q`, epoch caps, route caps,
   all 10,000 fee basis points or an explicit long-lived residue policy, host
   compensation, and governance envelopes;
2. a complete profile-selected ZDEX bucket projection and policy release feeding
   the Rust burn core; current parity covers exact supplied state and does not
   establish complete mounted bucket coverage;
3. generated fee-allocation and burn guest ELFs and image IDs, real `Succinct`
   receipts, exact release/source/toolchain manifests, profile selection by the
   sole settlement shell, and end-to-end governed admission with wrong-profile,
   epoch, route, module, image, journal, and fake-receipt substitutions;
4. a real Spot purchase guest plus authenticated fee-allocation output and
   purchase receipt that feed the exact purchase-to-burn journals into the
   route composer;
5. generated tokenomics coordinator and burn images, real child and recursive
   receipts for both burn and fee-allocation complete-lane paths, exact route
   connection, release/source/toolchain manifests, and replayed
   wrong-image/journal/profile/assumption evidence before either route
   discharges its nonzero obligation or supplies the full tokenomics lane write;
6. release-bound cycle/resource enforcement in the proof statement and
   governed receipt admission; the current leaf verifier cannot authenticate a
   module release `max_cycles` ceiling;
7. complete protocol-token issue/burn writer inventory and deny-by-default
   mounting;
8. an ABI revision and proved total migration before any precision rescale;
9. stateful replay, reordering, partial-failure, migration, and mixed-lane
   evidence;
10. independent economic, proof, authority-boundary, and legal review;
11. one atomic ZenoLedger commit path with no legacy value writer.

Passing focused core tests supports only the restricted statements and
executable behaviors named above. The blocked plugin import is a promotion gap,
not a passing integration result.

## Research Kernel record

Run ID: `zenodex-zdex-hyperdeflation-v1-20260821`

The run records source-hashed local evidence, refutation plans, retrieval-only
TheoremSearch results, the ABI blocker, the route-composition gap, the finite
representation limit, and the clean-integration dependency failure. The two
local claims remain `TESTABLE`: the Research Kernel promotion gate did not
recognize its support-edge and contradiction-search predicates, so no
`SUPPORTED` promotion was forced.
