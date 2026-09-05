# PulseX reward funding: source review dated 2026-09-05

Status: advisory mechanism research. No trading, transactions, policy selection, runtime edits, deployment claims or return estimates.

## 1. Game surface and observed mechanics

The participants are swap users, LPs, farmers, INC buyers/holders, PLSX holders, the farm owner, fee-converter owner and authorized callers, the configured fee recipient, frontend operators and PulseChain validators. The central distinction is between a swap user's asset payment and newly issued INC. A farmer's sale realizes value only because another participant buys or holds the reward token.

The official [PulseX page](https://pulsex.com/) describes noninflating PLSX, fee-funded purchase/burn, and INC farm rewards with decreasing inflation. Its [FAQ](https://pulsex.com/faq/) retains prelaunch supply language, and its generic fee percentages do not establish the current configuration. The official [launcher metadata](https://app.pulsex.com/version.json) links to the server repository and v1.1.5. The inspected [v1.1.5 source](https://gitlab.com/pulsechaincom/pulsex-server/-/tree/e5733524b69ef3e394132e00b49663a784ee8f97) is commit `e5733524b69ef3e394132e00b49663a784ee8f97`, dated 2026-07-15. Its main frontend file identifies both factories and explicitly distinguishes their fees.

All state observations below use chain 369, block **27,467,034**, hash `0x25deca4b037f07d380ca5383ec96ddb19006b3f9eb5a9d78364c50517106dd66`, timestamp **2026-09-05 09:39:25 UTC**, through the [official public RPC](https://rpc.pulsechain.com), whose address is documented in the [official mainnet repository](https://gitlab.com/pulsechaincom/pulsechain-mainnet/-/tree/873716af). These are retained RPC observations with an explicit provider trust premise, not independently verified storage proofs.

| Item | Source and observed state | Economic meaning |
|---|---|---|
| PLSX | `0x95B303987A60C71504D99Aa1b13B4DA07b0790ab`; `owner()` is zero; 18 decimals; total supply `141323072911745.720637853591562000` | The source contains owner-only minting, but the observed zero owner disables that authority under the inspected ownership code. Voluntary and converter burns reduce supply. |
| INC | `0x2fa878Ab3F87CC1C9737Fc071108F904c0B0C95d`; total supply `56081951.692453651195653169`; owner is MasterChef | INC minting is separate from PLSX. No lifetime supply cap was found in the inspected token/farm source. |
| MasterChef | `0xB2Ca4A66d3e57a5a9A12043B6bAD28249fE302d4`; rate `300000000000000` atoms/sec = **0.0003 INC/sec** | Nominal 25.92 INC/day, or 9,460.8 per 365 days if the rate and eligibility persist. This extrapolation is not a promised issuance schedule. |
| Farm control | Owner `0x2e8440f1839847af6566ef718dae48e17c0744df` has no code at this block; 19 configured pools, 8 positive weights, total weight 9,500 | Owner can add pools, change weights, and set the rate within the setter's 1 INC/sec cap. No automatic decay, mandatory monotone decrease, fixed end date or onchain token-holder allocation process was found in this control path. |

Sources: [PLSX verified-source response](https://api.scan.pulsechain.com/api/v2/smart-contracts/0x95B303987A60C71504D99Aa1b13B4DA07b0790ab), [INC verified-source response](https://api.scan.pulsechain.com/api/v2/smart-contracts/0x2fa878Ab3F87CC1C9737Fc071108F904c0B0C95d), [MasterChef verified-source response](https://api.scan.pulsechain.com/api/v2/smart-contracts/0xB2Ca4A66d3e57a5a9A12043B6bAD28249fE302d4). Constructor metadata records an initial 1 INC/sec rate; this review does not reconstruct every subsequent change.

The converter's declared starting-supply constant is `143116599865548.702043417022404109` PLSX. Its difference from the observed supply is approximately 1.7935 trillion PLSX. That constant is not an independently replayed genesis allocation, and the difference does not attribute every burn to fee-funded purchases.

**V1/V2 constant-product fee ownership.** Both inspected pair designs charge 0.29% on swap input. V1 assigns fee-related pool growth to its fee recipient, with integer rounding; its LP compensation therefore relies on another source, including INC for eligible staked positions. V2's fee-minting rule corresponds to a nominal 0.22% LP share and 0.07% protocol/converter share. Fees accumulate through reserve growth and LP-share accounting; these percentages are not immediate transfers from every swap. The official frontend describes the same distinction. Sources: [V1 pair source](https://api.scan.pulsechain.com/api/v2/smart-contracts/0x1b45b9148791d3a104184Cd5DFE5CE57193a3ee9), [V2 factory and embedded pair source](https://api.scan.pulsechain.com/api/v2/smart-contracts/0x29eA7545DEf87022BAdc76323F373EA1e707C523), [pinned frontend](https://gitlab.com/pulsechaincom/pulsex-server/-/blob/e5733524b69ef3e394132e00b49663a784ee8f97/pkg/app/dist/static/js/main.fad65d76.js).

The eight positive-weight farms all reference V1 pairs and hold nonzero staked LP balances. They include INC/WPLS and INC/PLSX, at pool IDs 8 and 9. The owner-controlled registry could change; the farm contract itself does not enforce a permanent V1-only rule.

**The converter does more than burn.** Current fee recipients are V1 `0xd46bd969d995a122ad5b803a45d309021a647b87` and V2 `0xd6ca7ee047a6f45d20d2962e4394e070cf27724f`. Both are proxies selecting implementation `0x5f02fbb0f8d924e9b67c7daae523ff51175699f9`. Both currently have `devCut=1429`, `BOUNTY_FEE=10`, `anyAuth=false`, and the same nonzero owner. The source uses basis points and takes the bounty after the recipient's cut. For a converted PLSX balance A, the current successful burn branch computes:

```text
dev = floor(A * 1429 / 10000)
bounty = floor((A - dev) * 10 / 10000)
burn = A - dev - bounty
```

Before integer rounding, this is **14.29%** to the configured recipient, **0.08571%** to the caller and **85.62429%** burned. These are fractions of converted PLSX, not exact fractions of original swap value; conversion trades incur their own costs. Authorized callers perform conversion when current authorization restrictions allow it. The nonzero owner can alter settings and upgrade the implementation. The configured recipient is `0x3239713576e11082cf9b9cda9b77468ea644c682`; its ultimate use is not specified by these contracts. Source: [current converter implementation](https://api.scan.pulsechain.com/api/v2/smart-contracts/0x5f02fbb0f8d924e9b67c7daae523ff51175699f9).

**What creates demand or a claim?** PLSX has an observed mechanism for fee-funded market purchases and supply destruction. Holding it does not by itself redeem LP reserves or a personal fee distribution in the reviewed contracts. INC has transfer, burn, permit and voting/delegation interfaces, and is an input to two rewarded LP pairs. Its delegation interface alone does not establish governance over the currently code-empty farm owner. No automatic INC-holder entitlement to PLSX burns, swap-fee revenue, fixed redemption value or mandatory third-party purchase was found in the reviewed token/farm/converter path. An LP token, by contrast, represents a proportional reserve claim. Any additional third-party staking, collateral or application use requires its own contract and demand analysis; it is not established here.

**Other services.** Converter callers receive the explicit bounty above. The configured recipient gets a separate cut, but this review cannot equate that payment with audited host, developer or insurance expenditure. PulseChain transaction senders pay gas in PLS independently of the swap fee; the pinned [Go-Pulse execution source](https://gitlab.com/pulsechaincom/go-pulse/-/blob/a224d91967a31c2c3080a8f75784d8de13c80b7b/core/state_transition.go) credits the execution fee recipient with gas-used times the effective tip, excluding the base fee. Consensus rewards and validator costs were not fully audited. No equivalent of ZenoDEX's zUSD monetary kernel, stability pool, proof market or separately paid external oracle service is implemented in the inspected pair/farm/converter contracts. Pair cumulative prices are an AMM observation, not a separately funded external reporting network. Frontend/RPC hosting costs remain outside the identified contract payment guarantees.

## 2. Attack query and demand interpretation

The useful question is whether rewards buy economically useful service after the participant's costs and the protocol's external revenues are accounted for. A farm rewards capital-time according to weights; it need not reward incremental trading demand or execution quality. A beneficiary may supply liquidity primarily for emissions and leave when subsidies fall.

A generic defensive deviation condition is: reward proceeds and rebates exceed all genuinely paid fees, execution losses, gas and capital/risk costs, without adding the intended service. Testing this requires bounded actors, controlled self-trade accounting and an independent service-quality oracle; no attack campaign was run.

Calling INC a token that must be sold forever overstates the source evidence. Ongoing issuance can dilute an unchanged holding's percentage of supply, but the observed rate is far below the original rate and can change again. Holders may retain, burn or use INC; market prices depend on demand as well as issuance. Conversely, depositing INC to earn more INC is primarily reward-dependent demand unless another service or revenue source supports it. The inspected contracts do not establish that external demand will absorb reward sales. No price trend, return or inevitable collapse is inferred.

## 3. Bounded model and ZenoDEX opportunities

Use integer amounts per asset and explicit epoch ownership. Keep these flows separate:

| Flow | Source | What the payment represents |
|---|---|---|
| LP fee compensation | Actual swap-user fees | Payment for liquidity/execution service and borne trading risk |
| LP withdrawal | LP-owned pool assets | Return of capital, not protocol revenue or yield by itself |
| Proof/oracle/operator fees | Explicit service fees or an allocated share of realized revenue | Payment for verified delivery, availability and operating cost |
| Stability-pool liquidation proceeds | Collateral acquired against extinguished debt/principal | Capital conversion and possible gain/loss, not wholly fee income |
| Insurance payment | Prefunded risk capital/premiums under a defined claim rule | Loss compensation; the reserve and the claimant liability cannot both be spent |
| Bootstrap farm subsidy | Finite owned inventory or an external sponsor's funded budget | Time-limited subsidy with a depletion rule |
| zDEX purchase-and-burn | An explicitly owned residual fee allocation | A competing use of surplus, followed by exact occurrence-linked destruction |

A candidate budget identity is, per asset: realized fees plus separately owned subsidy funding equal service obligations plus owned reserve additions plus designated purchase/burn spending plus refunds/residue. Borrowed principal, collateral, LP principal and unpaid claimant balances are excluded from discretionary fee revenue. zUSD issuance and monetary burns remain inside the existing collateralized monetary kernel.

Finite zDEX can coexist with recurring LP payments denominated in assets users actually pay. A fixed finite inventory cannot fund an unbounded constant stream of positive atom rewards without replenishment. Market-purchased zDEX can be distributed or burned, with each occurrence assigned one terminal destination. A second uncapped reward token moves the subsidy/demand question to its holders; it does not supply external cash flow.

Research opportunities, with no novelty claim:

- Compare rewards for verified usable depth, uptime and execution quality against capital-weighted emissions. Include withdrawal/terminal liabilities and oracle cost in the comparison.
- Compare a finite, declining launch budget plus revenue-funded steady-state compensation against permanent emissions. Stress zero volume, reward-token price shocks and sudden liquidity exit.
- Compare a rule that buys/burns only after bounded service obligations and risk reserves are funded against a fixed gross-revenue burn share. Measure the tradeoff in liquidity, solvency and token purchases.
- Keep oracle/proof/host service procurement separate from risk-capital compensation. Require delivered-service evidence and explicit recovery when a provider disappears.

These ideas must be compared with existing mechanisms. [Uniswap's protocol-fee system](https://github.com/Uniswap/protocol-fees/blob/main/README.md) already combines fee collection and token burn. [Curve's DAO design](https://docs.curve.finance/assets/pdf/whitepaper_curvedao.pdf) uses capital-time gauges and governance weights. [Liquity V2](https://docs.liquity.org/v2-faq/bold-and-earn) funds stability-pool yield from borrower interest and distinguishes liquidation gains; its [liquidity-incentive governance](https://docs.liquity.org/faq/staking) directs a separate share of borrower interest. [Liquity V1's finite reward distribution](https://docs.liquity.org/liquity-v1/faq/lqty-distribution-and-rewards) and [frontend reward sharing](https://docs.liquity.org/liquity-v1/faq/frontend-operators) provide further precedents. [Chainlink's billing interface](https://docs.chain.link/data-feeds/api-reference#getbilling) explicitly separates oracle payments and available payment funding. These are precedents, not adopted ZenoDEX parameters.

Compare candidate mechanisms at equal initial capital and matched user order flow: usable depth/slippage, external fee revenue net of all service cost, LP risk-adjusted net outcome, subsidy depletion, dilution by token, oracle/proof/host availability, liquidation shortfall, loss-bearing capital and exit latency, self-generated-volume reward sensitivity, governance concentration, and zero-volume survival. No benchmark has been run, so superiority is unestablished.

## 4. Evidence lane

Official docs, an official source release and bounded read-only chain queries were inspected. No model checking, economic simulation, contract compilation, storage-proof verification, full transaction history or deployment-wide audit occurred. All successful queried deployed bytecode matches against the explorer-provided bytecode were exact for PLSX, INC, MasterChef, the V1 pair, V2 factory and converter implementation. This is a consistency check between endpoints, not independent provider consensus or our own source-to-bytecode proof.

Explorer verification labels are **Sourcify partial match** for PLSX/INC/MasterChef and the inspected V1/V2 pair/factory source, using Solidity 0.8.12 or 0.5.16. The fee-converter implementation and inspected V2 proxy are labeled **fully verified**, using Solidity 0.8.9. Labels and raw responses are retained; their provenance remains an external premise.

Retained local files include raw explorer JSON, decoded source views, the pinned official frontend, launcher metadata, public RPC inputs/results, block header/code and source hashes. `manifest.json` inventories their bytes. One farm RPC attempt timed out before retaining results; its bounded retry retained all 32 intended active-farm calls without errors. The web text-fetch tool could not render the explorer APIs, so public HTTPS source reads were performed through an approved read-only shell fetch.

## 5. Promotion boundary and remaining gaps

This review supports the stated source and pinned-state observations. It does not establish honest governance, immutable future converter parameters, sustainable prices, a sufficient reward budget, profitable LP participation, production safety, deployment completeness, novelty or superiority.

Scope is PulseX V1/V2 constant-product pairs, their observed farm and fee-converter path. The current frontend also exposes stable-swap functionality; its separate fees and service contracts were not audited, so the 0.29% statement is not a universal claim about every PulseX route. External INC applications, actual fee-recipient spending, all validator compensation, historical allocation changes and organic-versus-circular buyer demand remain unmeasured. The launcher's opaque `version` field differs from the resolved server-tag commit and was not a valid server Git ref; no frontend rebuild correspondence is claimed.

## Retained evidence identity

The source note was retained unchanged in the research archive. This repository
copy adds only this evidence-identity section. The original note SHA-256 is
`93c9e646be2474f772b423aad9cbcf06806e0d97b6503a94b8cd96e8a1f700e8`.
Archive `pulsex-mechanism-research-20260905.tar.gz` is 555,776 bytes with SHA-256
`1cd2fe3c308c11846274af85927d62a9b448ee19809aab6c59c0f996a6d2d203`.
Its `manifest.json` SHA-256 is
`c6f16291204b2ac4a81c18c5fe8e7dd0c78ca6112a50e0a4138e63ab334aa503`.
The manifest inventories 37 files; seven retained consistency checks passed.
This establishes local artifact consistency under the stated RPC and source
provenance premises. It grants no runtime or publication authority.
