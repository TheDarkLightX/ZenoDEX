# ZDEX Hyperdeflation V1 Research Contract

Date: 2026-08-21

Status: `EXPERIMENTAL_UNMOUNTED`

Production authority: `NONE`

## Scope

This packet defines a finite, integer-safe ZDEX burn leaf and an exact
denomination-rescale transition. It replaces the proposed fixed percentage
supply floor with a per-occurrence retained-supply rule. It does not alter the
legacy tokenomics release, mount a writer, authorize a token sale, or prove the
complete atomic purchase-and-burn route.

The intended economic lifecycle is:

```text
protocol fee revenue
  -> governed quote asset allocation
  -> proved AMM purchase of ZDEX
  -> route-bound ZDEX source bucket
  -> exact ZDEX burn leaf
  -> one atomic global commit
```

The implemented core covers the burn leaf after a route has authenticated the
purchase occurrence. The AMM purchase, fee allocation, hosting allocation,
route composition, and atomic global commit remain separate obligations.

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

This binding does not authenticate the purchase by itself. A future route
composer must verify the purchase receipt, prove that its exact ZDEX output was
credited to the declared burn source, pair that output one-to-one with the burn
debit, and reject residue or duplicate consumption.

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
| Caller invents the purchased amount | Exact purchase-occurrence, source, and amount binding | Authenticated purchase receipt and route composer |
| Rejected transition changes value | Identical state object and empty effects | Runtime adapter parity |
| Accepted wrapper is forged | Exact owned types and constructor recomputation | Opaque verifier witness for publication |
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
- `src/integration/tau_testnet_dex_plugin.py`: testnet faucet exclusion for the
  canonical protocol-token asset;
- `tests/integration/test_tau_testnet_dex_plugin.py`: exact rejection and
  no-state-change scenario.

## Promotion gates

This work remains `EXPERIMENTAL_UNMOUNTED` until all of the following exist:

1. a normative ZDEX tokenomics release selecting `p/q`, epoch caps, route caps,
   fee allocations, host compensation, and governance envelopes;
2. a Rust core with Python differential parity and checked widened arithmetic;
3. a RISC0 guest and exact journal/image/profile binding;
4. an authenticated AMM purchase receipt and exact route composer;
5. complete protocol-token issue/burn writer inventory and deny-by-default
   mounting;
6. an ABI revision and proved total migration before any precision rescale;
7. stateful replay, reordering, partial-failure, migration, and mixed-lane
   evidence;
8. independent economic, proof, authority-boundary, and legal review;
9. one atomic ZenoLedger commit path with no legacy value writer.

Passing the local tests proves only the restricted statements and executable
behaviors named above.

## Research Kernel record

Run ID: `zenodex-zdex-hyperdeflation-v1-20260821`

The run records source-hashed local evidence, refutation plans, retrieval-only
TheoremSearch results, the ABI blocker, the route-composition gap, the finite
representation limit, and the clean-integration dependency failure. The two
local claims remain `TESTABLE`: the Research Kernel promotion gate did not
recognize its support-edge and contradiction-search predicates, so no
`SUPPORTED` promotion was forced.
