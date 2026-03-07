# Confidential Features: User-Facing Use Cases

This document explains the confidential-extension and sealed-bid features in plain language.

## What this feature is

ZenoDEX has a beta-stage confidential execution surface for cases where users do not want to reveal everything to the market before the trade or auction finishes.

It has two main parts:

1. **Confidential extensions**
- Private trading logic can run inside an attested trusted execution environment (TEE).
- The extension provider can keep its code private.
- The DEX still requires a deterministic receipt before accepting the result.

2. **Sealed-bid auctions**
- Users commit to a bid first without revealing the bid details.
- They reveal later during a bounded reveal window.
- If they do not reveal, the system can slash their bond so the auction cannot be griefed for free.

## Why a normal user would care

These features are about **execution quality** and **information leakage**.

In ordinary public trading:
- large traders show their hand,
- bots can react to visible intent,
- auctions can be gamed if bids are visible too early,
- private strategy providers have no clean way to sell execution logic without exposing it.

Confidential extensions and sealed bids reduce those problems.

## Main use cases

### 1. Better execution for large trades

Use this when:
- the order is large enough that public intent would move the market,
- the trader wants private routing or risk logic,
- a premium execution provider has an edge but does not want to open-source the strategy.

Why it helps:
- less information leakage before execution,
- better protection against copy-trading and adverse selection,
- the provider can charge for use without revealing the code.

### 2. Token launches and batch sales

Use this when:
- a project wants a cleaner primary sale,
- public bids would cause undercutting or auction sniping,
- fairness matters more than continuous-time speed.

Why it helps:
- users can submit a bid once,
- the market does not see the bid price immediately,
- the auction clears in a deterministic batch instead of a timing race.

### 3. Private RFQ or institutional flow

Use this when:
- a desk or treasury wants quotes without broadcasting full interest,
- size or strategy sensitivity makes a public path unattractive,
- execution quality matters more than maximum decentralization at every step.

Why it helps:
- the user avoids exposing the full trade setup,
- the provider can run custom logic privately,
- accounting and payment are still auditable.

### 4. Solver and strategy marketplaces

Use this when:
- a routing or market-making team has a proprietary model,
- they want to monetize it directly inside the DEX flow,
- they do not want the edge copied immediately.

Why it helps:
- TEE receipts let the DEX meter usage,
- providers can be paid for execution assistance,
- users get better execution without needing to trust opaque API behavior blindly.

## When not to use it

This is not the right default for every interaction.

Do **not** use it when:
- the user only wants a normal retail swap,
- latency has to be as low as possible,
- the value of privacy is smaller than the extra complexity,
- the user needs fully public, fully transparent execution at every step,
- the use case requires encrypted on-chain state rather than private off-chain execution.

For routine swaps, the normal public DEX path is simpler and usually better.

## What the user experience should feel like

For a user, this should not feel like “using cryptography.”
It should feel like:

- “I can ask for private execution help without leaking my strategy.”
- “I can join a fair auction without showing my bid too early.”
- “If people spam the auction and disappear, they pay for it.”
- “I can understand what was checked, even if the strategy code stays private.”

## Trust and privacy model in plain language

### What is private
- bid details before reveal,
- extension source code,
- some execution logic and routing preferences.

### What is still auditable
- whether the output came from an approved TEE measurement,
- whether the receipt was fresh and replay-safe,
- whether fees and balances were conserved,
- whether the auction flow followed the allowed phases,
- whether terminal hazard states were closed properly.

### What this does not promise
- It does not make everything private on-chain.
- It does not eliminate all trust.
- It does not guarantee the economics are perfect for every auction shape.
- It does not mean every user should always choose the confidential path.

## Best audience for the first release

The best early users are:
- large traders,
- launch teams running batched sales,
- institutions using private execution assistance,
- strategy providers selling execution intelligence,
- research and pilot markets where fairness and leakage control matter.

## Related technical docs

- `docs/CONFIDENTIAL_FEATURES_BETA_RUNBOOK.md`
- `docs/CONFIDENTIAL_EXTENSIONS_TEE_SMPC.md`
- `docs/SEALED_BID_DISASTER_STATE_CATALOG.md`
