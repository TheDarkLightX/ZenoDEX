# Independent service-budget model review

Date: 2026-09-05. Status: `INDEPENDENT_SCOPED_REVIEW_AND_REPLAY`.
Authority: none. Reviewed source was frozen by its author before final replay.
The reviewer did not edit the implementation, tests or Lean source.

No blocker was found for the packet's restricted arithmetic and research
claims. The universal single-entitlement bound is substantive and has an
explicit proof. Procurement and budget experiments retain their bounds.
Authentic funding, service delivery, claimant identity, auction incentives and
the complete publication lifecycle remain separate obligations.

## Exact subject and independence

| Subject | SHA-256 |
| --- | --- |
| [Research model](../../tools/tokenomics/lp_service_budget_v1.py) | `b7d81fa74c77efae33f7561d42aa6976a7f52dcc4690c873a1dc2b4a496ea7e5` |
| [Companion tests](../../tests/tools/test_lp_service_budget_v1.py) | `c10cde8388ca3f5b6c7769dfbc6c2c1c371858163fec97d25ac9d351bc10fe9d` |
| [Four Lean theorems](../../lean-mathlib/Proofs/ServiceFeeBudgetFloorV1.lean) | `942c536b3d5d074e52b93bef97b5ba4d08a49bcaa3297d8e452a97eeb903e1e8` |
| [AutoGov donor reconciliation](ZENODEX_AUTOGOV_TOKENOMICS_RECONCILIATION_20260905.md) | `da64f43758d8f69760d6fee2d8bcd3a7beb20e3dfcb3f54a1af29a9a28eb7692` |

The research-model author was `/root/authority_discovery`; the donor-note
author was the integrating parent. This reviewer authored the preceding
protocol comparison and proposed the carry identity and benign bid-markup
control during review. Those suggestions are disclosed contributions, not a
fully blinded review. The source hashes above matched before and after the
independent checks. No current runtime/guest changes are included in this
review subject. The author's forthcoming discovery narrative was not part of
these frozen four files.

## Findings and precise mathematical scope

### 1. Confirmed mounting boundary: an ownership model is not authenticated inventory

`AssetBudget` at model line 23 declares disjoint same-asset ownership buckets.
`reserve_service` at line 49 moves `payment_cap` from `free` to
`contract_escrow`, preserving their sum and leaving principal, earned claims,
risk and designated burn funds unchanged. Its insufficient-free-budget guard
is the correct scoped construction. `fee_partition` at line 57 rejects shares
above the denominator and assigns every remaining atom to one residual output.

The constructor validates nonnegative integers and the asset label. It does
not acquire a physical ledger balance, authenticate fee origin or prove that
the declared ownership buckets cover a real state exactly once. Likewise,
`ServiceLot.position_id` is caller data, as the model explicitly documents.
Rejecting identical strings establishes neither independent collateral nor
exclusive commitment across an authenticated history. These are high-priority
requirements before mounting, rather than defects in the declared research
model. The model grants no authority and makes no mounted-completeness claim.

The current arithmetic also does not select an economic priority among
required operating expenses, risk reserve top-ups and discretionary support.
Protecting declared buckets is different from proving that their initial
amounts cover the required services and risks.

### 2. Resolved during review: original cap versus remaining escrow

The original helper argument named `escrow` was ambiguous after partial
payment. The frozen `terminal_claims` at line 66 now explicitly consumes
`funded_cap`, `earned_total`, `paid_total`, with:

```text
0 <= paid_total <= earned_total <= funded_cap
provider_unpaid = earned_total - paid_total
funder_refund = funded_cap - earned_total
provider_unpaid + funder_refund = funded_cap - paid_total
```

The retained control is cap 10, earned 4, already paid 3: the current physical
balance is 7, partitioned into provider liability 1 and funder refund 6. Passing
the current balance 7 as the original cap would instead return 1 and 3. The
author clarified the API and added the exact partially paid case before
freeze. The original arithmetic identity was sound; the repair resolves the
boundary meaning.

This helper returns quantities. It does not authenticate the two recipients,
perform a payout, prevent replay or close the service contract's state
machine. A mounted lifecycle still needs claim identities, cancellation
authority, exactly-once settlement and recovery.

### 3. Confirmed theorem: fixed aggregate entitlement is nondecreasing and 1-Lipschitz

Define, in one asset's integer atoms:

```text
E(F) = min(C, floor(l*F/D))
D > 0, 0 <= l <= D; F,W,C >= 0
```

The frozen Lean source proves:

- `floor_growth_le` at line 12:
  `floor(l*(F+W)/D) <= floor(l*F/D)+W`.
- `floor_increment_le` at line 21: the equivalent natural-number increment
  bound.
- `capped_increment_le` at line 27: `E(F+W)-E(F) <= W` for fixed `C`.
- `capped_monotone` at line 33: `E(F) <= E(F+W)`. This makes explicit that
  natural subtraction is not hiding a decrease in the interpretation above.

The main proof expands multiplication, uses `l*W <= D*W`, applies division
monotonicity and removes the exact `D*W` quotient. The downstream arithmetic
is handled by `omega`. The proof is universally quantified over natural
amounts and valid rates; it is not limited to the solver's sampled coefficient
set. It does not assume the desired inequality in a witness record.

Two live examples establish positive payout and a tight boundary. One further
example refutes the careless extension to separately rounded claims.
There are no placeholders, custom axioms or unexpected imports. The source
imports only `Std`. Actual axiom output is recorded below.

The theorem is an entitlement-growth result. Interpreting it as an economic
no-wash result additionally requires the same rate, cap, eligibility and fee
attribution in both histories; no newly unlocked subsidy or historical claim;
and a coalition cost comparison that includes every recaptured fee, host,
proof, voter and sponsor flow. A gross fee is not automatically an
irrecoverable coalition cost. Beneficial changes to another admitted position
or to an Oracle-dependent payoff are outside this inequality. The frozen
model explicitly retains broader incentive-compatibility nonclaims.

### 4. Confirmed rounding limit and a useful generalization

Two half-shares independently rounded against cumulative fees illustrate the
limit: at `F=1`, total payout is 0 and owned carry is 1; at `F+W=2`, payout is
2 and carry is 0. Payout growth 2 exceeds the added fee 1 because a previously
owned atom is released. This is not creation of a new atom, and it is not a
counterexample to the single-entitlement theorem.

For `m>=1` uncapped shares with nonnegative integer `n_i`, positive `D` and
`sum(n_i)=D`, define:

```text
P(F) = sum_i floor(n_i*F/D)
R(F) = F - P(F)
P(F+W)-P(F) = W + R(F)-R(F+W)
0 <= R(F) <= m-1
P(F+W)-P(F) <= W+m-1
```

The identity follows by subtraction of the two complete partitions. The
residual bound follows by summing the fractional remainders: their sum is an
integer strictly below `m`. The bound on `R` stated here requires the shares
to sum to `D`; unassigned policy weight is not merely bounded rounding dust.
Caps can also leave a larger unallocated balance and must not silently inherit
this residual bound.

The reviewer independently enumerated `m=1..4`, `D=1..7`, all full integer
share vectors and `F,W=0..8`: the identity, residue bound and increment bound
all passed. This is a bounded executable check plus an algebraic derivation,
not a newly compiled Lean theorem. Formalizing this partition lemma is a
useful next mathematical improvement. Its runtime connection must preserve
who owns the old residue and whether the release authorizes its reallocation.

### 5. Confirmed procurement scope: minimum reported ask-cost, not truthful bidding

`select_unit_lots` at model line 99 selects the `q` cheapest lots, with a
deterministic ID tie-break. For identical, independently deliverable unit lots,
the selected set minimizes total reported ask-cost: the kth cheapest price is
no greater than the kth price of any q-element alternative. Consequently, if
this minimum exceeds the available budget, no affordable exact-q subset exists
in that model. This argument covers the zero-quantity boundary as well.
The exhaustive small-set oracle agrees with the implementation.

These guarantees do not cover different lot sizes, coupled delivery,
overlapping capital, bidder truthfulness, coalition-proofness or actual social
cost. The retained heterogeneous example needs 10 units, with lots
`(6 units, cost 6)` and `(10 units, cost 11)`: ratio order costs 17 while the
second lot alone costs 11. It is a control against extending this unit-lot
algorithm, not an input supported by it.

A separate benign pay-as-bid example now executes the actual selector. For one
unit and budget 10, Alice's true cost is 1 and Bob asks 10. Alice wins at either
ask 1 or ask 9. If awarded her own ask, her utility changes from 0 to 8. Minimum
reported cost does not induce truthful reporting. The selector itself does
not implement a payment rule, so this is a conditional interpretation control,
not a demonstrated flaw in its allocation computation.

Before extending procurement, choose the actual standardized service and
payment/information model. An exchange proof for the current unit algorithm
would be useful; a heterogeneous model requires a different optimization and
incentive analysis. No governance quantities should be inferred from the test
grid.

## Independent executable evidence

Commands run from the worktree root unless a directory change is shown:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider tests/tools/test_lp_service_budget_v1.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/tokenomics/lp_service_budget_v1.py > /tmp/zenodex-v3-service-budget-independent-replay01.json
cd lean-mathlib
lean --version
lean -DwarningAsError=true Proofs/ServiceFeeBudgetFloorV1.lean
lean -DwarningAsError=true /tmp/zenodex-v3-service-budget-axioms01.lean
```

Results:

- **11 tests passed in 0.16 seconds**.
- **4,100** fee-partition cases, **2,925** terminal cases and **1,280**
  unit-procurement cases passed the replay.
- **157 UNSAT queries**: arbitrary nonnegative integer fee/wash/cap values
  for `D=1..16,l=0..D`, plus `D=10000,l in {0,1,2500,9999,10000}`. This Z3
  result retains the coefficient bound; the Lean theorem supplies the
  universally quantified arithmetic result.
- Replay used Z3 **4.15.4**, library SHA-256
  `56d9977b9276bcb8cda9973a14058fcaa9f3bfee14ed57408b9faacd76d4d8f3`.
  The independently regenerated JSON was byte-identical to the author's
  result: SHA-256
  `890261a20ab34b34429bc14c4500196f0de10a8872d693f03db70e97d246be70`.
- Lean **4.27.0**, commit `db93fe1608548721853390a10cd40580fe7d22ae`,
  compiled the exact source with warnings treated as errors. The audit copy
  was checked to be the identical source prefix plus exactly four
  `#print axioms` commands, then independently compiled.
- `floor_growth_le` lists `[propext]`; the other three list
  `[propext, Quot.sound]`. No `sorryAx` or custom trust extension appeared.
  Audit-copy SHA-256:
  `e2d5f6c28e9284307b55a3e785dab2c95a342a70ff46b7361694a0fd06689bb9`.
  Author-retained axiom output SHA-256:
  `c8165541e9e96d6e3e9358664cb46e88346543a9747d3f8890b121dc79a18122`.

The proof-quality scan found no placeholder/trust/broad-automation flags. Its
heuristic score was not used as a grade or proof. The author also reports
Ruff/mypy success in `zenodex-v3-service-budget-checks-final01.json`; those
style checks were not independently repeated here. Its initial `lake env`
failure from unavailable Mathlib dependencies remains author-recorded negative
evidence. The direct Std-only compile above needs no Mathlib build/download.

The executed comparison policies and assertions are semantic controls. This
review did not run a source-mutation campaign, so it does not report a mutant
kill count. No Cargo, remote job, whole-repository gate, deployed observation,
auction equilibrium solver or runtime-refinement proof was run.

## Brief independent AutoGov donor-note read

The donor note's distinctions are supported by the inspected sources:

- Historical mechanism note section 2.3 explicitly defines a deviator's payoff
  via an accepted out-of-envelope change. Excluding that event does not show
  that every in-envelope allocation or observation is incentive compatible.
- `SURFACE_PARAMETER_NAMES_V1` at policy line 77 has nine parameters. The
  separate legacy `PARAMETER_NAMES_V1` has ten; the donor note correctly refers
  to the nine-parameter governance surface. Neither is a service-award command.
- `AutogovNextTrajectoryBudget.usedAfter_eq_start_plus_totalMovement` and
  `zero_start_totalMovement_le_limit` carry one limit and accumulator through a
  list. The result controls parameter motion, without proving a monetary-loss
  bound or a reset policy.
- The retained node test at line 461 of
  `test_zeno_ledger_node_autogovnext.py` checks an appended rejected-policy
  receipt and equal economic roots. Its outcome differs from V3 precommit
  rejection purity. The donor note preserves that difference.

All eight source hashes listed in the donor note matched. This reviewer did
not rerun its reported 37 policy tests, three node tests or four-theorem axiom
audit. The note accurately limits their interpretation and does not grant
authority from policy-hash equality.

A useful future extension is to relate governed parameter movement to
worst-case service/risk exposure with explicit units and a proved sensitivity
bound. The existing trajectory accumulator alone cannot supply that relation,
particularly across discontinuous liquidation/eligibility boundaries. This
remains a mathematical-design task, not a new assumed payoff field.

## Remaining promotion boundary

The next meaningful contract connects authenticated free funds, exact service
occurrences and position/claim ownership to reservation, delivery, earned
claims, payment, cancellation, refund and recovery. It must preserve these
terms across policy changes and prove finite-width arithmetic for the actual
implementation. The current research arithmetic supplies reusable pieces for
that work. It does not establish sufficient demand, honest Oracles, operator
liveness, beneficial token prices, selected token rights or whole-program
value safety.

## Supplement: universal cumulative carry companion

The parent subsequently implemented
[ServiceFeeCarryV1.lean](../../lean-mathlib/Proofs/ServiceFeeCarryV1.lean),
SHA-256 `daa4c35881dd50111bd6a8d7fc23744be2cc49ff0c231c970027982a8ff179ef`.
This supplement records independent verification of that frozen successor.
The earlier section's bounded-check-only status describes the initial review
checkpoint; the carry results below now also have a compiled universal Lean
derivation. The reviewer did not edit the new proof.

Let `P(F)=sum_i floor(F*w_i/D)`, `M(F)=sum_i (F*w_i mod D)`,
`C(F)=F-P(F)` and `m=ws.length`. The actual source defines all three quantities
from a finite `List Nat` of weights. It does not store the claimed partition
or its preservation in an assumed witness.

| Theorem | Universal statement and premises |
| --- | --- |
| `quotient_remainder_identity` | `D*P(F)+M(F)=F*sum(ws)`, including Lean's total natural division/remainder convention at zero. |
| `remainders_lt_count` | `M(F)<D*m` when `D>0` and the list is nonempty. |
| `payouts_le_fees` | `P(F)<=F` when `D>0` and `sum(ws)=D`. |
| `owned_partition` | `P(F)+C(F)=F` under the same full-weight premises. |
| `carry_scaled` | `D*C(F)=M(F)` under the same premises. |
| `carry_lt_claimant_count` | `C(F)<m` under the same premises; nonemptiness is derived from positive full weight. |
| `payouts_monotone` | `P(F)<=P(F+W)` for all natural `F,W,D` and weight lists. |
| `incremental_carry_identity` | `P(F+W)-P(F)+C(F+W)=W+C(F)` for positive denominator and full fixed weights. |
| `incremental_payout_bound` | `P(F+W)-P(F)<=W+(m-1)` under the same premises. |

The proof chain is direct. List induction lifts the per-weight Euclidean
division identity; the positive denominator and complete weight sum bound
payouts by fees. Natural subtraction is justified by that bound. Sum-of-
remainders accounting and cancellation give the strict carry bound. The
incremental identity then follows from two owned partitions and payout
monotonicity, which ensures the natural difference represents actual growth.
No theorem assumes its own desired preservation result.

The model's “claimant count” is precisely the number of weight rows. It includes
zero weights and does not authenticate distinct beneficiaries. A tighter
positive-weight-count bound is a possible extension; it is unnecessary for
the validity of the current row-count bound. The theorem also supplies no
finite-width multiplication/division proof for Rust or a publication consumer.

Independent fixed challenges additionally establish:

- The old-carry identity at `F=1,W=1,D=2,ws=[1,1]` holds by computation.
- The bound is tight at `F=3,W=1,D=4,ws=[1,1,1,1]`: incremental payout 4
  equals `W+(m-1)`.
- Incomplete weights do not satisfy the same bound: `F=10,D=4,ws=[1]`
  gives carry 8 and list length 1. This input violates the required full-weight
  premise, so it is a premise-breaking control, not a theorem counterexample.

The accepted interpretation remains cumulative, uncapped allocation under
one fixed weight policy, with old carry reserved for that policy. Two separate
calls `fee_partition(1,(1,1),2)` each assign `(0,0,1)`, while a cumulative call
at fee total 2 assigns `(1,1,0)`. Reclassifying the two already assigned
per-occurrence residues requires separate authority and semantics. The new
theorem does not authorize that reclassification, change weights, or spend
reserve atoms owned under another policy.

### Independent compile, trust audit and semantic mutant

The following commands ran under the same pinned Lean 4.27.0, with the
`lean-mathlib` directory selecting its toolchain:

```bash
lean -DwarningAsError=true Proofs/ServiceFeeCarryV1.lean
lean -DwarningAsError=true /tmp/zenodex-v3-service-carry-independent01/audit.lean
lean -DwarningAsError=true /tmp/zenodex-v3-service-carry-independent02/mutant.lean
```

Original compilation and the audit/challenge copy passed. The copy consists
of the exact original source prefix, nine appended `#print axioms` commands
and the three fixed computational challenges. Its SHA-256 is
`600d9e68b1c2142cdb8dc1775035381de877d05cae3a2a785d6a62fb36628f13`.
The axiom output has SHA-256
`d1d00c72cb9cb9267b629a134b4d604a58caa96765eb53474a1dc815dccb6d4a`:

- `remainders_lt_count` uses `[propext]`.
- `carry_lt_claimant_count` and `incremental_payout_bound` use
  `[propext, Classical.choice, Quot.sound]`.
- The other six use `[propext, Quot.sound]`.

No `sorryAx`, custom axiom or import widening appeared. Standard
`Classical.choice` is explicitly retained in the trust account; no claim of
choice-free proofs is made. The heuristic scanner's solver-tactic flag was
reviewed: those calls close arithmetic after the quotient/remainder,
induction and monotonicity facts are exposed.

The source mutant changes only the `carry` definition body:

```lean
-- Original
def carry (F D : Nat) (ws : List Nat) : Nat := F - payouts F D ws
-- Temporary mutant
def carry (F D : Nat) (ws : List Nat) : Nat := 0 * (F - payouts F D ws)
```

All original theorem headers and all independent challenge statements remain
byte-identical. The mutant uses every original argument, so its rejection is
not an unused-variable/linter failure. The fixed incremental challenge at
`F=1,W=1,D=2,[1,1]` fails with `decide` reporting the proposition false. Since
the true new carry is already zero in this case, the omitted resource is
exactly the one old carry atom. The original owned-partition proof and carry
example also fail. The surviving candidate was never edited to accommodate
the mutant.

This is one semantic failure family. An earlier `carry := 0` probe also
produced unused-variable diagnostics; its files/logs remain in the first
packet. The clean successor supplies the reported semantic result. Its
mutant source SHA-256 is
`4815fef10a5b70469df0ac0a6a8de30f112618ac9b99cf83e022ee00912b66c2`;
the decisive output SHA-256 is
`3cc3e0a6a325f40d17d455d497822ad3cfa209a7f16bde0099b664ac60b373fa`.
The source/command/header checks are retained in
`zenodex-v3-service-carry-independent02/receipt.json`, SHA-256
`6045bd3e5ab5ef5033dcece1404843d6c1532e0221b735da6f01edc76d170947`.
The original/audit/initial-probe receipt SHA-256 is
`8756d20a06cde72d3c802f689fa051a0f1e11e03cca10b1c6a13555f93fa60c5`.

No mathematical blocker was found in these nine universal statements. The
parent's separate Python/reference binding test was not part of this proof
review or its claimed evidence. A runtime consumer must establish the fixed
policy, exact cumulative fee source, reserved-carry ownership and original
claim identities before applying this accounting relation.
