# Tokenomics review reconciliation with Opus

Date: 2026-09-05. Status: `REVIEWED_RESEARCH_AND_SOURCE_RECONCILIATION`.
Authority: none. This note records independently checked corrections to the
Opus synthesis and its later fee-rounding report. It selects no token rights,
fee constants, rounding change or production activation.

## Findings to retain

The strongest shared research direction remains funded service compensation,
an explicitly finite bootstrap budget and measured incremental net revenue.
The [service-budget packet](ZENODEX_WHOLE_PROGRAM_V3_SERVICE_BUDGET_DISCOVERY.md)
and [protocol comparison](ZENODEX_LP_AND_SERVICE_REWARD_FUNDING_COMPARISON_20260905.md)
give the contracts, alternatives and current evidence. LP fees, host/proof/
Oracle work, Stability Pool capital, loss reserves and buyback spending have
different owners and obligations. Capturing additional value can enlarge an
available budget only after its ownership, costs and required compensation
are established. Each resulting atom still has one final destination.

The host-service evidence in Opus's untracked candidate router is shape-checked
and committed while its authentication is an explicit shell/proof premise.
That is an unclosed prerequisite before mounting. No static runtime caller
was found in the inspected roots, and that candidate router is absent from
the V3 integration subject. Its proposed percentages are not active V3 policy.
A second caller-supplied digest or verifier-profile field alone would not close
the authentication obligation. Reuse authenticated source facts where possible;
bind exact service, beneficiary, fee occurrence and pinned policy before payment.

## Corrections that affect decisions

| Claim | Reviewed disposition |
| --- | --- |
| Burn fraction always equals allocation share divided by revenue multiple. | This simplification needs compatible time, supply and price conventions, plus actual expenditure equal to that allocation. The exact realized relation below includes execution price and actual spend. |
| Six million monthly releases against a 70M launch float require 7.2% annual burn. | The donor's 7.2% uses a 1B initial total-supply denominator. The same 72M annualized token flow is about 102.86% of the 70M initial float. The 50-month release example also cannot support sixty full release months. These remain unapproved donor assumptions. |
| High deflation and a healthy valuation are arithmetically incompatible. | Neither threshold was defined. A precise incompatibility result requires explicit bounds, a fixed horizon and the actual execution/budget assumptions. The algebra does not approve replacing the user's objective. |
| A negative fixed-revenue price derivative excludes a death spiral. | It establishes a comparative-static result. Revenue, liquidity, costs, policy changes, delays and market feedback remain outside it. Neither stability nor collapse was demonstrated. |
| Captured leakage is non-rivalrous funding. | Incremental net surplus can help preserve baseline budgets. Once captured, the money remains rivalrous, owned and subject to alternative uses. A Pareto or novelty claim needs further evidence. |
| Hosts and stakers have no claim transition. | The existing zUSD adapter implements both. Two unchanged positive lifecycle tests passed with explicit development Oracle and clock premises. This does not qualify generalized V2 staking or the monetary lane through V3's restricted publisher. |
| Buyback execution does not exist. | Legacy node purchase/burn execution and later typed V3 buyback transitions exist. Their release and publication contracts differ; the legacy treasury-allocation fallback cannot satisfy V3's same-occurrence purchase-and-exact-burn requirement. |
| The protocol collects zero on every feasible trade in the cited pool. | The older experiment stopped at an input of 9000 atoms and tested leg-one extraction. That endpoint is not the kernel's feasibility bound. The newer twelve-case report is a bounded observation. |
| The fee example proves undocumented overcharging or a live defect. | Ceiling total fee, floor protocol share and the LP remainder are explicitly specified and conserved. Relative rounding can be large at small atomic inputs; economic severity and disclosure need the chosen asset, decimals, client and admitted profile. |

For one quote asset and horizon, let Q be actual all-in purchase expenditure,
B acquired-and-burned tokens, R realized revenue, S the explicitly chosen
reference supply, and P the chosen mark price. With positive denominators:

```text
execution_price = Q / B
revenue_multiple = P * S / R
realized_spend_share = Q / R
burn_fraction = B / S
burn_fraction = realized_spend_share / revenue_multiple * P / execution_price
```

Prior saved budgets, refunds, caps and settlement timing can separate actual
spend from the current revenue allocation. Already minted vesting releases
change the selected circulation measure; they do not mint total supply.
External market statistics in the Opus reports were not promoted by this review.

## Concrete remaining obligations

The specified [CPMM fee contract](../../src/kernels/dex/cpmm_swap_v8.yaml)
permits floor-rounded protocol extraction to be zero. Any incentive or liveness
policy that requires positive extraction must use the actual integer amount
and its admitted domain. The positive-extraction premise in the
[perps incentive draft](../derivatives/PERP_INCENTIVES_V1.md) therefore remains
a composition obligation. No rounding policy was changed to satisfy it.

The inspected legacy quote serializer conveys gross input and net output but
does not expose a separate rounded-fee/effective-rate field. Trace the selected
client's actual display and signed minimum-output contract before concluding
whether disclosure is adequate. The Tau native transaction fee cap is a
different field from an AMM fee limit.

Host attribution also needs its actual policy. A user-nominated integrator and
a provider paid for certified service are different contracts. Sender-bound
claim payment does not by itself establish earlier service delivery. Existing
authorized reserve withdrawal must be reconciled with any blanket claim that
discretionary movement is impossible; it is not arbitrary caller authority.

V3's mounted isolated pipeline still admits one ASSET transfer occurrence.
Source reachability in the legacy node or monetary adapter does not promote
the remaining lane gates, deployment mediation or production safety.

## Evidence and preserved subjects

Three bounded reviews independently checked the equations, source reachability
and rounding claims. Thirteen exact `Fraction` arithmetic controls passed.
Two unchanged positive zUSD lifecycle tests passed in 0.95 seconds. The rounding
review inspected source and derived integer relations without executing swaps
or a vulnerability reproduction. These reviews added no runtime changes.

| Retained review | SHA-256 |
| --- | --- |
| `ASTRA_REVIEW_OPUS_TOKENOMICS_MATH.md` | `5f5abb49b2f3f97e3d2071d3ecd8f70731300070736ca6af478530e740598f63` |
| `ASTRA_REVIEW_OPUS_TOKENOMICS_SOURCES.md` | `acc7b15d9e29a55b11bf743153a449d3ace66a7e8df7427f825ce90bbb8e37c6` |
| `ASTRA_REVIEW_OPUS_FEE_ROUNDING.md` | `efa33b286c22a5e6d5cae29a13d2babcfb0fd93fc38bc62dc4663d1902d63df4` |

The original inputs, detailed reviews and positive-test log are retained in
`zenodex-v3-opus-tokenomics-review01.tar.gz`, 118,796 bytes, SHA-256
`cccc9218cf054f1a722c2257a952603db016b1327dbb6710913417867abda559`.
Its twelve regular members passed byte verification. The manifest SHA-256 is
`9597f697da53a92e07ac525a56d512fe37116788ea68499c2a807a34a78f7354`.
Source hashes bind applicability. A separate exact-source snapshot retains
twenty reviewed files across the two checkouts and records ten checked absence
cells: `zenodex-v3-opus-tokenomics-source-snapshot01.tar.gz`, 284,416 bytes,
SHA-256 `e1dddbc5052d3a0f3f42e79bd886decc4668c174111b66dc0c31cbea0ff813c6`.
Each present file matched its reviewed hash before retention, and every regular
archive member matched its original bytes. This preserves the untracked router
subject without modifying it. Transitive dependencies, full historical replay
and deployment remain unqualified.

No new Lean, ESSO, RISC0 or deployment claim follows from these three reviews.
The separately compiled reward/carry theorems retain their own evidence packet.
No remote work, fee change, reward activation or monetary migration occurred.
