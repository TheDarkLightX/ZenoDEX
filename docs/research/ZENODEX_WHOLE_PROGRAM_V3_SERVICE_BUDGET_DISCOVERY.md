# V3 service budgets and finite-token incentives

Date: 2026-09-05. Status: `RESEARCH_MODEL_AND_SCOPED_ARITHMETIC_PROOF`.
Authority: none. No fee percentages, reward rights, token issuance, eligibility
policy, publisher capability or release promotion are selected.

The useful design sequence is ordinary LP fees, a finite explicitly funded
campaign with complete claims and refunds, then comparison against standardized
liquidity-service procurement. Hosts, reporters and provers need their own
funded availability commitments during fee droughts. Risk capital and existing
claims remain separately owned. A finite deflationary zDEX supply is compatible
with these funding sources; it does not make them affordable by itself.

This packet supplies an executable per-asset model, seven numerical failure
controls, and a universal integer floor theorem. It does not establish a
complete incentive-compatible mechanism. The earlier [SPOT/FARM discovery](ZENODEX_WHOLE_PROGRAM_V3_SPOT_FARM_DISCOVERY.md)
recovers existing lifecycle implementations and genuine policy gaps. The
parallel [funding comparison](ZENODEX_LP_AND_SERVICE_REWARD_FUNDING_COMPARISON_20260905.md)
supplies external protocol comparisons; its separate claims and evidence remain
separate from this local model.

## 1. Game Surface

Alice trades or borrows; Bob supplies liquidity or risk capital; hosts,
reporters, challengers, provers and keepers supply distinct services. A sponsor
can fund a finite campaign. A coalition can occupy several of these roles and
governance seats simultaneously. Governance and agents propose constrained
commands; ZenoLedger retains ordering and publication authority. Neither a
budget model nor AutoGov observation supplies a writer capability.

### Recovered ownership and cashflow boundaries

These are donor contracts and inspected implementations, not twelve completed
lane qualifications. Amounts in different assets cannot be added as though
they were one spendable balance.

| Lane or service | Existing source and owner | Consequence for service funding |
| --- | --- | --- |
| `ASSET_TRANSFER`, custody | Existing depositors and claimants own transferred/backing assets. | A transfer, custody receipt or principal deposit creates no protocol revenue. External-finality and complete-source obligations remain in V3. |
| `SPOT_LIQUIDITY` | Pool principal and LP fee entitlements are distinct from the designated protocol fee occurrence; existing swap/liquidity and fee kernels are recovered in the SPOT/FARM review. | LP gross fees are not net profit after inventory loss, adverse selection and costs. Already-owned LP fees cannot be allocated again to hosts, rewards or burn. |
| `FARM_INCENTIVES` | Aggregate reward-index/vault donors and separate local-testnet activity rewards exist. Their claimant and eligibility contracts differ. | A new finite service campaign needs per-owner escrow, earned debt, cancellation and terminal carry ownership. The present proposal does not silently select one donor's policy. |
| `ZDEX_TOKENOMICS` | `ZDEXFeeDestinationV1` names BUYBACK, QUALIFIED_HOST_POOL, TREASURY, PROOF_REWARDS, COVER_RESERVE and LP_REBATES. The fee core allocates one already-charged occurrence and retains a named residue. | Destination allocations are disjoint claims. An assigned burn reserve cannot also back service obligations. Candidate basis-point settings are unapproved. |
| `ZUSD_MONETARY` / fee staking / hosts | `zusd_monetary_bridge._route_mint_fee` assigns the host share, then routes the remainder to active fee stakes or the protocol reserve. `zusd_liability_cover` reconciles wallet, DEX, perps and those fee-pool liabilities. | Those routed host/staker atoms are already owned. The monetary kernel retains issuance and monetary burn. A general service budget cannot mint zUSD or recycle these liabilities as fresh fee income. |
| Stability Pool / liquidation | `compute_liquity_v1_liquidation_partition` divides debt offset and received collateral; principal consumed for debt offset and collateral received are different assets and obligations. | Deposit principal is risk capital. Received collateral includes recovery of value surrendered; the entire receipt is not service revenue or risk-free yield. Eligibility, finality and loss allocation require their actual monetary contracts. |
| `PERPS_MARKET` / insurance | `updates.py` derives insurance as initial insurance + fee income - claims paid. A liquidation penalty updates both fee-pool and fee-income views. | Those fields do not represent separate freely spendable pots. Existing loss-cover capital and claims cannot be promised again as LP rewards. |
| `ORACLE_MARKET` | The local budget verifier separates query rewards, reporter/dispute bonds, slashes and fee splits. `verify_economic_security_envelope` checks reward affordability relative to supplied budgets and supplied cost/risk estimates. | Bonds remain principal until an authorized final slash. An arithmetic envelope does not establish funded provenance, external truth, realized attack cost or reporter honesty. Query fees and an explicit liveness reserve are candidate funding sources. |
| `PROOF_REWARDS` | The V3 policy-blocked lane retains empty reserves/tasks/nullifiers and rejects all six unsupported capabilities. | A proof-reward fee destination is not a completed payment lifecycle. A proposed funded task must bind exact work, claimant, unique occurrence, acceptance and unfinished-work refund. |
| `SEALED_AUCTION`, `STRATEGY_ESCROW` | Bid deposits and user execution budgets have existing owners; this review does not re-audit those lifecycles. | User principal and unspent strategy limits remain refundable/claimable. Only an independently authorized service fee or subsidy may enter a campaign budget. |
| `EXTERNAL_CUSTODY`, `GOVERNANCE_MIGRATION` | Backing assets and historical claims retain their versioned ownership; governance changes pass existing constrained command boundaries. | No reserve rebasing, migration or policy update can erase old ownership merely to make a new service budget appear feasible. |

The accepted buyback architecture keeps quote reserve and burned zDEX separate:

```text
available_quote = old_buyback_reserve + designated_fee_allocation
quote_spent = min(available_quote, governed_command_cap, authenticated_route_safe_limit)
new_buyback_reserve = available_quote - quote_spent
new_zdex_supply = old_zdex_supply - zdex_received_and_burned_from_that_occurrence
```

Its existing governed minimum, arithmetic and route guards still apply. A zero
or rejected purchase does not prove strict deflation in that epoch. Purchased
atoms committed to exact burn cannot also pay LPs. Releasing previously minted
treasury zDEX does not mint supply, but can increase circulating supply. This
packet neither chooses such a release nor promises price appreciation.

### Explicit epoch state

For each asset `a`, require a complete partition of physical assets by ownership:

```text
A[a] = principal[a] + earned_claims[a] + contract_escrow[a]
       + risk_reserve[a] + buyback_quote_reserve[a] + free[a]
```

These are disjoint ownership tags on physical assets. They are not a sum of an
asset balance and a second copy of its matching liabilities. Active contract
escrow includes that contract's earned-but-not-yet-paid portion until it is
split at settlement; `earned_claims` denotes other separately held claims.
Completeness and authenticated provenance are premises of the model. Calling an
unowned or omitted liability `free` would invalidate its application.

Settled, uniquely identified fee receipts are partitioned under their pinned
policy once. Explicit subsidy transfers name the asset and original funder.
For each eligible campaign, freeze its policy, service definition, term,
claimants/positions and payment cap before measuring the rewarded service.
Accepting a contract moves its entire maximum payment from `free` to escrow.
Service evidence may earn at most that cap. Payout consumes an earned claim
once; cancellation stops future accrual and preserves existing claims.

For a contract's **original** funded cap `K`, cumulative earned amount `E` and
cumulative paid amount `P`, require `0 <= P <= E <= K`. At terminal settlement:

```text
provider_owed = E - P
original_funder_refund = K - E
remaining_physical_escrow = K - P
provider_owed + original_funder_refund = remaining_physical_escrow
```

The model function deliberately takes the original cap, not the current escrow
balance. For `K=10,E=4,P=3`, it returns `(1,6)` over the seven remaining atoms.
Refund recipient authentication, once-only execution and historical claims are
required future lifecycle implementation, not established by this equation.

## 2. Attack Query

Can a participant gain by generating its own activity, changing eligibility,
reusing collateral, selling a worse service, or manipulating an admissible
governance observation? Can the system appear funded by counting a liability or
one fee occurrence twice? Can a terminal path strand an earned claim or refund?

| Failure family | Concrete model/refuter | Required closure or explicit premise |
| --- | --- | --- |
| Principal subsidy | Physical 100, principal owed 100, reward payment 1 leaves cover short by 1. | Reserve services only from authenticated unencumbered funding; stress loss reserves remain protected. |
| Activity unlocks subsidy | One fee atom makes a previously unavailable two-atom subsidy claimable. | A fee-only marginal bound says nothing about unrelated subsidy release. Freeze eligibility or separately analyze the whole unlocking policy. |
| Claim-weight manipulation | Existing reward pool 10; usage changes from zero to sole claimant after paying one fee atom, yielding 9 before other costs. | Prior volume and open eligibility cannot be silently substituted for fixed weights. Treat split identities and all coalition roles together. |
| Double fee promise | Fee 10, burn promise 6, service promise 6 leaves 2 unfunded. | One occurrence, one exhaustive allocation with explicit remainder. |
| Old carry release | Two half-share cumulative floors pay 0 at fee total 1 and 2 at total 2. | The additional payment includes an old atom. Preserve its ownership and account for the change in carry; do not call it new fee revenue. |
| Greedy scope drift | Indivisible service lots `(units,cost)=(6,6),(10,11)`, demand 10: price-per-unit greedy costs 17, optimum costs 11. | The exact unit-lot selector is only for interchangeable one-unit lots; heterogeneous cover needs a different exact algorithm and proof. |
| Bid markup | One unit, budget 10; Alice costs 1 and Bob asks 10. Alice wins at asks 1 and 9; pay-as-bid utility rises by 8. | Minimum reported ask-cost does not imply truthful bidding, minimum social cost, competition or resistance to coalition supply withholding. |

These are evaluated mathematical comparison/omission controls. Test comments
using “mutant” refer to those counterfactual equations; no production source
mutation campaign or executable market transaction was run.

Adverse selection can make a service unprofitable even with positive gross
fees. A liquidity lease therefore needs an agreed service metric, asset/pool
and price-range subject, continuous availability rule, capital lock, expiry,
bounded breach remedy and disputed-service recovery. A caller-provided position
identifier is not an ownership or disjoint-collateral witness. Capital can leave
after expiry; funded rewards alone establish no retention theorem.

AutoGov's historical donor specifies bounds, step limits, cooldown,
anti-oscillation, a persistent trajectory budget and an authority denylist.
Its payoff definition that values only out-of-envelope outcomes does not rule
out profitable in-envelope choices. Research must also examine reward/volume
signals controlled by beneficiaries, observer bias, policy changes around an
eligibility cutoff, fee diversion and repeated small moves. Future policy
changes preserve old claims. Irreversible burn decisions need a distinct
funding horizon from reversible, not-yet-earned service spending. The separate
parent AutoGov replay/proof packet owns current implementation evidence.

## 3. Bounded Model

### Three concrete candidate contracts

All options preserve the ordinary LP trading-fee baseline. None requires new
inflationary reward issuance or invents an entitlement from token holdings.

| Candidate | Funding and allocation | Ownership, lifecycle and limitation |
| --- | --- | --- |
| A: past-fee liquidity-service procurement | A named fraction of already earned, unencumbered protocol revenue funds fixed-term identical service lots. Select the lowest reported asks with canonical ID tie-breaks, within the existing budget. | Reserve each accepted lot's payment cap before service starts. Earn only verified service, pay once, refund unearned cap to the original funding reserve at cancellation/expiry. The supplied exact algorithm proves reported-cost optimality only for independent identical units. |
| B: finite bootstrap campaign | An explicit sponsor transfers a finite existing-asset budget to the same kind of funded service escrow before enrollment. | No unfunded replenishment, automatic mint or promise of perpetual return. Funding provenance, end condition, earned claims and refundee are fixed. Sponsor assets may be an approved existing reward asset; user principal, risk backing and previously committed buyback funds are unavailable. |
| C: capped fixed fee participation | Freeze a service entitlement `min(C, floor(l*F/D))`, with `D>0,0<=l<=D`, an exact fee source and an independently owned burn allocation. | The theorem below limits one fixed aggregate entitlement. Service verification, coalition aggregation, carry ownership and no subsidy/weight/cap change are separate obligations. It does not certify general usage rewards or an individual hold-to-earn right. |

The recommended research sequence begins with B after recovering the applicable
ordinary fee contract: funding and terminal feasibility can be checked before
an adaptive market is added. Compare A using verified standard service units
and actual reported costs. C is an arithmetic constraint for selected contracts,
not a substitute for an economic game. Governance still must select service
eligibility, source asset/owner, affordability horizon and permissible policy
parameters; the numerical test domain supplies no such selection.

### Quiet volume and stress

Let each service's already accepted maximum unpaid obligation be `L[a,i]` and
its escrow be `E[a,i]`. Require `L[a,i] <= E[a,i]` per asset and contract.
New service caps must satisfy `sum(new_caps[a,i]) <= free[a]` before acceptance.
Current principal or a future fee forecast cannot relax this inequality.

In a zero-volume epoch with no free reserve, a positive paid-host minimum is
unaffordable even if deposits are large. The available choices are an explicit
finite liveness reserve, voluntary service with no promised payment, reduced
service admission, or the corresponding governed recovery/terminal behavior.
An unbounded stream of positive fixed costs cannot be covered by a finite
reserve with zero income. Stress recovery cannot spend capital backing earlier
loss obligations on new incentives. Real third-party demand, service costs and
risk premia are external economic inputs still to be measured; the model
produces no APR, demand estimate or sustainability verdict.

### Universal fixed-entitlement result and carry boundary

The Std-only Lean file proves, for all natural `F,W,l,D,C` with `D>0,l<=D`:

```text
floor(l*(F+W)/D) <= floor(l*F/D) + W
0 <= min(C,floor(l*(F+W)/D)) - min(C,floor(l*F/D)) <= W
```

The separate monotonicity theorem makes the natural subtraction an actual
nonnegative increment. The upper-bound proof uses multiplication/division
monotonicity and the exact identity `(x+D*W)/D=x/D+W`.

A conditional self-wash corollary follows only if the incremental fee entering
this exact pool is `W`, the coalition incurs cost at least `W` before this
entitlement, and all its other incremental returns and losses have been
accounted for. Fixed eligibility, rate, cap and claim scope are required.
Recaptured LP/host/proof fees, altered weights, another subsidy, market P&L or
an old unaccounted claim break that premise. The result does not establish
general no-profitable-trading or coalition strategyproofness.

For independently floored fixed weights `n_i` summing to `D`, define cumulative
carry `R(F)=F-sum_i floor(n_i*F/D)`. Then:

```text
total_payout_increment = W + R(F) - R(F+W)
0 <= R(F) < number_of_weights
```

The parent-owned [ServiceFeeCarryV1.lean](../../lean-mathlib/Proofs/ServiceFeeCarryV1.lean)
is the separate universal carry proof and has its own review/evidence subject.
Its nine universal statements derive the complete quotient/remainder identity,
monotonicity, reserved carry bound and exact incremental resource identity from
the actual weight list. Thus incremental payout is at most `W + (m-1)` for
`m` weight rows summing to positive D. Here m counts rows, including zero
weights; it does not authenticate distinct people. The bound is tight for
four equal rows, `F=3,W=1,D=4`, where payout grows by four atoms.
Crucially, this cumulative carry is reserved under the same entitlement policy.
It is different from per-occurrence residue already assigned to another owner.
Recomputing a cumulative floor cannot seize that owner's earlier residue.
The two-half-share control illustrates a possible accounting interpretation;
it does not authorize retroactive reallocation of the existing fee core.

The companion passed independent Lean 4.27 compilation and a nine-theorem
axiom audit with only `propext`, `Quot.sound` and `Classical.choice`. The
reviewer's definition-only carry-discard mutant failed the unchanged accounting
challenge. The retained [formal companion test](../../tests/formal/test_lean_service_fee_carry_v1.py)
adds 108 evaluations of the actual Lean definitions against independent exact
`Fraction` calculations and the Python research partition. It includes
`2^128-1` atom inputs, explicit per-occurrence/cumulative ownership separation,
the tight bound and an executed carry-discard source mutation. Its four tests
passed in 6.04 seconds; scoped Ruff and mypy passed. No finite-width runtime
or production refinement is inferred from these natural-number evaluations.

```bash
python3 -m pytest -q tests/formal/test_lean_service_fee_carry_v1.py
python3 -m ruff check tests/formal/test_lean_service_fee_carry_v1.py
python3 -m mypy --cache-dir=/dev/null tests/formal/test_lean_service_fee_carry_v1.py
```

Carry proof SHA-256:
`daa4c35881dd50111bd6a8d7fc23744be2cc49ff0c231c970027982a8ff179ef`.
Companion test SHA-256:
`bfe4952bb4073ed872165a2e5a84322fd95d2177de275a994603d7c4355ea2c7`.
The independent review's carry supplement identifies its own exact replay and
mutation artifacts; the integration parent owns the additional test above.

## 4. Evidence Lane

The executable [research model](../../tools/tokenomics/lp_service_budget_v1.py)
and [tests](../../tests/tools/test_lp_service_budget_v1.py) use exact integers.
The Lean file [ServiceFeeBudgetFloorV1.lean](../../lean-mathlib/Proofs/ServiceFeeBudgetFloorV1.lean)
imports only `Std`. Local checks passed:

| Check | Exact scope and result |
| --- | --- |
| Pytest | 11 tests passed; protected buckets, quiet funding refusal, oversubscribed fee split, earned/refund boundary, live/tight/capped entitlement, subsidy/weight/carry controls, disjoint unit lots, affordability, exact numeric types. |
| Deterministic enumeration | 4,100 fee partitions (`F=0..24,D=1..8`, two nonnegative shares summing at most D); 2,925 terminal triples (`K=0..24,0<=P<=E<=K`). |
| Independent small procurement oracle | 1,280 cases: four identical-unit lots, each price `0..3`, quantity `0..4`; exhaustive subsets independently minimize total ask then sorted IDs. |
| Z3 4.15.4 | 157 UNSAT queries. Each query has unbounded nonnegative integer F,W,C; coefficients cover `D=1..16,l=0..D` plus `D=10000,l in {0,1,2500,9999,10000}`. Three-second per-query timeout; UNKNOWN/SAT fails the replay. This solver family is coefficient-bounded; the Lean theorem is universal. |
| Lean 4.27.0 | Four universal theorems and live/boundary/carry examples pass. `floor_growth_le` uses `propext`; the other three use `propext,Quot.sound`. No `sorryAx` or project axioms. |
| Python quality | Scoped Ruff and mypy pass. |

Replay commands:

```bash
python3 -m pytest -q tests/tools/test_lp_service_budget_v1.py
python3 tools/tokenomics/lp_service_budget_v1.py
python3 -m ruff check tools/tokenomics/lp_service_budget_v1.py tests/tools/test_lp_service_budget_v1.py
python3 -m mypy --follow-imports=silent tools/tokenomics/lp_service_budget_v1.py
cd lean-mathlib
lean --version
lean Proofs/ServiceFeeBudgetFloorV1.lean
```

The directory's `lean-toolchain` pins 4.27.0, actual compiler commit
`db93fe1608548721853390a10cd40580fe7d22ae`. The initial `lake env lean` attempt
stopped because the sparse tree lacks `external/mathlib4`; direct pinned Lean
checked the Std-only source without installation or a full build. No runtime
refinement, RISC0 build, new remote work or full assurance gate was run.

The exact local replay output SHA-256 is
`890261a20ab34b34429bc14c4500196f0de10a8872d693f03db70e97d246be70`.
Its solver library SHA-256 is
`56d9977b9276bcb8cda9973a14058fcaa9f3bfee14ed57408b9faacd76d4d8f3`.
The independent [review](ZENODEX_SERVICE_BUDGET_INDEPENDENT_REVIEW_20260905.md)
replayed the model and theorem subject. That reviewer contributed the terminal
parameter clarification, carry identity and pay-as-bid interpretation control;
its stated independence limits remain visible.

| Implemented research subject | SHA-256 |
| --- | --- |
| `tools/tokenomics/lp_service_budget_v1.py` | `b7d81fa74c77efae33f7561d42aa6976a7f52dcc4690c873a1dc2b4a496ea7e5` |
| `tests/tools/test_lp_service_budget_v1.py` | `c10cde8388ca3f5b6c7769dfbc6c2c1c371858163fec97d25ac9d351bc10fe9d` |
| `lean-mathlib/Proofs/ServiceFeeBudgetFloorV1.lean` | `942c536b3d5d074e52b93bef97b5ba4d08a49bcaa3297d8e452a97eeb903e1e8` |

## 5. Promotion Boundary

This model demonstrates budget feasibility under explicit complete-ownership
inputs, useful failure families and a scoped arithmetic theorem. It does not
prove truthful auctions, service delivery, collateral uniqueness, Oracle truth,
market demand, net LP profitability, legal classification or product completion.
No existing runtime source, generated gate, journal, active profile or token
policy was changed by the research packet.

Before implementation, recover the final intended policy and settle only its
genuine gaps: service/eligibility definition; authorized funding asset and owner;
term and early-exit remedy; allocation/cap/horizon; original-funder and carry
ownership; drought/recovery behavior. Then connect authenticated state and
service evidence to per-owner liabilities, total typed rejection, finite-width
refinement, exact once-only effects, historical claims and the existing publisher.
Those obligations cannot be replaced by selecting numbers in a test.

### Source pins for recovered constraints

Donors were read in the V3 tree while parent integration advanced; HEAD at final
source inventory was `7d0123033c5a0d4e3da68ed497303fb260988829`. These hashes,
not that moving HEAD alone, identify the inspected constraints. Historical
claims in donors were not replayed or promoted by their presence here.

| Source | SHA-256 |
| --- | --- |
| `docs/FIRE_REVENUE_SURFACE_ATLAS.md` | `ba9ac7ca950562eae24ceefee2c9468449780b1cfacf4779a410463edb403837` |
| `docs/research/ZDEX_HYPERDEFLATION_V1_20260821.md` | `dcf7209eccab9e022950053ff5e1fdb85ededdb20410123697ea94ce653554f9` |
| `docs/research/ZDEX_ATOMIC_BUYBACK_ARCHITECTURE_DECISION_20260828.md` | `730ff45ab198de16c13789760ddb3eca58638c6f3a8819a4e8cbd1dbdbee3bf2` |
| `src/core/zdex_fee_allocation_types_v1.py` | `b29490205c099e5f38812a71555c65d20b5de1c333425c22ed2d4fbe392d50df` |
| `src/core/zdex_fee_allocation_v1.py` | `8f976781349e31ae9fd3c48b8534ae4fbfe74e8ce33e6b62c6a627c8109bad84` |
| `src/core/zusd_liability_cover.py` | `bfc2e4a2188e9ce84c198cba2c5bd010dccaa4bb0bf2c1f6f0ef523dd0d47ae8` |
| `src/core/zusd_liquidation_partition.py` | `13d5a8384d5443af0c6b62fa66d453a0dedd77f7560c0cd0dae039fe830018c4` |
| `src/integration/zusd_monetary_bridge.py` | `8a0c49e3a78b31c92910c08c33dec5ff4a3b8fca2196249c8be5275c4ae7f9d5` |
| `src/core/perp_v2/updates.py` | `485ab0e762e702e5ed15b5668f69e02cb6b82c0c4b16f29bd5ec6186b9730c93` |
| `src/core/oracle_economic_security.py` | `3c7f22435f1c8f632558f27e8539aa7790a9c14a183de4a8eeeecd1c90c868fc` |
| `docs/ZENO_ORACLE_TOKEN_BUDGET_V1.md` | `3508a993c99130349814bdd055d8cd300a8207e44458cc42044c8f0c961d391b` |
| `src/core/proof_rewards_policy_blocked_lane_v1.py` | `67e87330f8ad9464efc28053a677761dd64de9d85c99ee896707cbe98f38bdad` |
| `docs/AUTOGOVNEXT_GAME_THEORY_AND_MECHANISM_DESIGN.md` | `d9c20574722aa9bf22ced7dc3188cdd4b7d70e23c6c98f91bd8032cc623b96e5` |
| `tools/tokenomics/pro_rata_budget.py` | `b46abf921e977dbe147a23f7dce89071cd1320b9a8bf981c5d7b4d212dc15fc4` |
| `lean-mathlib/Proofs/RevenueSurfaceSafety.lean` | `5956492db206c49c242596ff450f4baed76d5fa4fd82c99ee5a1a781c5cb926c` |
