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

The implemented Python burn core consumes a route-authenticated purchase
occurrence. A separate Rust/Python shadow composer models receipt admission for
exact Spot and tokenomics leaf journals through release-selected verifier ports
and pairs their effects. Independent Rust and Python fee-allocation cores derive a
buyback-budget occurrence from a charged-fee bucket. The real AMM guest,
tokenomics guest, governed percentage and host-compensation selection,
recursive route proof, profile admission, and atomic global commit remain
separate obligations.

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
an exact `FeeConservationRowV1`, one tokenomics lane write, and no external
outbox effect. Zero fees, policy drift, insufficient ingress, and signed-effect
width excess produce typed no-effect rejection.

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
  remaining_epoch_burn_cap_atoms,
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
- source-reserve, epoch, and route ceilings.

The command must repeat the purchase occurrence root, source bucket, and exact
purchased amount. Any mismatch returns `PURCHASE_BINDING_MISMATCH` with no
effect. The accepted result carries the policy and route context and
recomputes its capacity before construction succeeds.

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
The Python composer repeats that recomputation because Python module internals
cannot provide same-process authority. The Rust witness constructor is private.
The buy-and-burn command lists the budget root in its exact consumed-object set.
Its effect plan consumes only the buy-and-burn command occurrence, matching the
global epoch effect contract. The tests use an injected accepting verifier and
contain no cryptographic proof. Historical inclusion, persistent global
consumed-object enforcement, and a real allocation guest receipt remain open.

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

Composition cancels the transient `+B` and `-B`, emits exactly one authorized
ZDEX supply burn of `B`, consumes the command occurrence once, orders the Spot
and tokenomics lane writes, and emits no external outbox row. Any binding or
history mismatch returns a typed rejection with an empty effect plan.

Both receipt-admission implementations are deliberately `SHADOW`-only.
`ACTIVE_NEW`, composite, conditional, fake, development, empty, wrong-effect,
and verifier-rejected receipts cannot construct the opaque verified leaf
witnesses. The injected verifier port remains a reference boundary; this
packet contains no RISC0 guest image or cryptographic verifier implementation.
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
```

All live ZDEX buckets must be present exactly once and in canonical order.
Cross multiplication proves that represented token quantity is unchanged:

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
| Supply reaches zero through rounding | Ceiling retention and positive-supply theorem | Rust and guest parity |
| Caller invents the purchased amount | Exact purchase journal, verifier witness, occurrence, source, and amount binding in a shadow route | Real Spot guest and governed profile membership |
| Preexisting ZDEX is mixed into the purchase output | Purchase transient bucket must project `0 -> B` | Complete global balance-root connection in the Spot guest |
| Purchased ZDEX is only partly burned | Burn transient bucket must project `B -> 0`; composed transient rows cancel | Recursive route proof and atomic commit |
| Rejected transition changes value | Identical state object and empty effects | Runtime adapter parity |
| Fee split loses atoms to truncation | Exact allocation-plus-residue equation and named reserve | Governed residue-release lifecycle |
| Caller invents a buyback budget | Shadow route recomputes the fixed-policy allocation and binds journal digest, state roots, amount, source, and consumed-object ID; this rejects semantically invalid invented budgets | Real allocation guest receipt, historical inclusion, and persistent global consumed-object enforcement |
| Buyback budget debits another holder | Closed protocol buyback source bucket in both composers | Complete mounted caller inventory |
| Accepted allocation wrapper shifts value between destinations | Independent transition recomputation rejects a sum-preserving allocation mutant before receipt verification | Real guest/image evidence and profile-selected policy registry |
| Burn secretly issues ZDEX | Effect requires zero authorized issuance | Complete writer inventory |
| Test faucet mints protocol ZDEX | Tau testnet plugin rejects the canonical protocol-token asset | Clean dependency-closed integration replay |
| Partial denomination migration | All projected buckets scale exactly or transition rejects | Complete global ZDEX bucket registry and atomic migration |
| Multiplication or epoch overflow | Pre-multiplication u128 guard and u64 epoch exhaustion reject | Rust checked/widened arithmetic parity |
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
  malformed-input, exhaustive-small-domain, and reject-no-effect evidence;
- `lean-mathlib/Proofs/ZDEXHyperdeflationV1.lean`: machine-checked restricted
  theorems for ceiling equivalence, the exact headroom threshold, positive
  retained supply, accepted-burn positivity, guard necessity, exact bucket
  scaling, and finite geometric positivity;
- `tests/formal/test_lean_zdex_hyperdeflation_v1.py`: placeholder scan and
  focused Lean elaboration;
- `src/core/zdex_purchase_burn_*_v1.py`: immutable shadow journals, canonical
  effects, release-selected receipt admission, process-local witness markers, and pure
  two-lane composition;
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
- `tests/core/test_zdex_fee_allocation_v1.py` and
  `zk/global_settlement_abi_v1/tests/zdex_fee_allocation.rs`: denominator BVA,
  exhaustive small-domain conservation, no-effect rejection, route binding,
  hostile Python scalar, and five-commitment cross-language golden evidence;
- `src/integration/tau_testnet_dex_plugin.py`: testnet faucet exclusion for the
  canonical protocol-token asset;
- `tests/integration/test_tau_testnet_dex_plugin.py`: exact rejection and
  no-state-change scenario.

## Promotion gates

This work remains `EXPERIMENTAL_UNMOUNTED` until all of the following exist:

1. a normative ZDEX tokenomics release selecting `p/q`, epoch caps, route caps,
   all 10,000 fee basis points or an explicit long-lived residue policy, host
   compensation, and governance envelopes;
2. a Rust retention/capacity core with Python differential parity and checked
   widened arithmetic;
3. a RISC0 guest and exact journal/image/profile binding;
4. real Spot, fee-allocation, and tokenomics guests whose authenticated outputs
   refine the shadow allocation occurrence, purchase-to-burn journals, and
   exact route composer;
5. complete protocol-token issue/burn writer inventory and deny-by-default
   mounting;
6. an ABI revision and proved total migration before any precision rescale;
7. stateful replay, reordering, partial-failure, migration, and mixed-lane
   evidence;
8. independent economic, proof, authority-boundary, and legal review;
9. one atomic ZenoLedger commit path with no legacy value writer.

Passing the local tests supports only the restricted statements and executable
behaviors named above.

## Research Kernel record

Run ID: `zenodex-zdex-hyperdeflation-v1-20260821`

The run records source-hashed local evidence, refutation plans, retrieval-only
TheoremSearch results, the ABI blocker, the route-composition gap, the finite
representation limit, and the clean-integration dependency failure. The two
local claims remain `TESTABLE`: the Research Kernel promotion gate did not
recognize its support-edge and contradiction-search predicates, so no
`SUPPORTED` promotion was forced.
