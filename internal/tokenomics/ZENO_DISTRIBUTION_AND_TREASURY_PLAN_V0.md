# ZENO Distribution And Treasury Plan V0

Status: internal planning gate. This is not legal, tax, compensation, securities,
custody, governance, or launch advice.

## Allocation Reading

The current internal candidate uses a `1,000,000,000 ZENO` supply:

| Bucket | Percent | Tokens |
| --- | ---: | ---: |
| Founder / original R&D | 15% | 150,000,000 |
| Core team / future contributors | 10% | 100,000,000 |
| DAO / protocol treasury | 25% | 250,000,000 |
| Ecosystem, LP, solver, operator, proof incentives | 25% | 250,000,000 |
| Community / retroactive airdrop / testnet users | 10% | 100,000,000 |
| Security, audits, bug bounties, insurance reserve | 5% | 50,000,000 |
| Liquidity bootstrap / market making | 5% | 50,000,000 |
| Strategic partners / investors / chain partners | 5% | 50,000,000 |

If Trevor is the founder/original R&D recipient, the founder allocation is
`150,000,000 ZENO`, subject to the same internal vesting discipline as the model:
12-month cliff, 50-month duration, and no initial unlock. Entity, tax, securities,
and compensation treatment remain counsel/accounting questions.

## Vesting Cadence

The `50-month` duration is an internal conservative parameter, not a statute or
external rule. The checker currently requires insider and strategic allocations
to vest for at least 48 months. The candidate uses 50 months because it gives
integer monthly releases across all insider-like buckets:

| Bucket | Tokens | 50-month monthly release |
| --- | ---: | ---: |
| Founder / original R&D | 150,000,000 | 3,000,000 |
| Core team / future contributors | 100,000,000 | 2,000,000 |
| Strategic partners / investors / chain partners | 50,000,000 | 1,000,000 |

A weekly or monthly drip is acceptable as a mechanism design choice if it keeps
the cliff, total duration, transfer limits, tax/accounting treatment, and resale
policy explicit. For example, the candidate can be implemented as:

```text
12-month cliff -> monthly drip for 50 months
```

or:

```text
12-month cliff -> weekly drip over an equivalent 50-month release window
```

Weekly vesting needs a deterministic remainder rule because 50 calendar months
do not always divide cleanly into a whole number of weeks. The usual safe shape
is equal weekly releases with any integer remainder released in the final period.

Founder vesting should not be the operating-runway plan. Domain purchases,
hosting, testnet operations, audits, legal review, and contractor bills should
come from explicit treasury, ecosystem, security, or liquidity-bootstrap budgets
with receipts and spending caps.

## Burn-Indexed Insider Drip

A burn-indexed drip is feasible as an internal design candidate, but it should
be modeled as an unlock accelerator rather than an automatic sale mechanism.
The clean shape is:

```text
base_release_epoch = scheduled insider drip
eligible_burn_epoch = organic protocol-fee ZENO burned in the measurement window
extra_release_epoch <= min(extra_release_cap, burn_share_cap * eligible_burn_epoch)
total_release_epoch = base_release_epoch + extra_release_epoch
```

The accelerator must preserve the cliff. It can speed up the post-cliff drip
only after the protocol has already produced eligible burns.

Candidate safety rule:

```text
extra_release_epoch <= 25% of eligible_burn_epoch
```

This keeps the accelerator subordinate to the burn. If `100,000 ZENO` is
eligible-burned in a window, at most `25,000 ZENO` of extra insider unlock can be
created by that burn window. The exact percentage should be tested, disclosed,
and counsel-reviewed before activation.

Eligible burn should exclude:

- wash volume;
- related-party or insider-funded round trips;
- subsidized market-maker volume used only to manufacture burns;
- treasury-funded buys where the treasury is effectively paying to unlock
  insiders;
- manual burns unrelated to protocol-fee revenue;
- burns from routes, pools, venues, or counterparties selected to steer users.

The burn signal should use a lagged trailing window, for example 30, 60, or 90
days. A lag reduces the value of short-term manipulation and gives governance
time to freeze the accelerator if the burn input looks corrupted.

Attack query:

```text
Value(extra_release_from_manipulated_burn)
  > CostToGenerateEligibleBurn + ExpectedPenalty + FutureValueLost
```

The mechanism should reject the design until the modeled attack is unprofitable
under bounded assumptions. At minimum, the release cap, anti-wash filter,
related-party exclusion, lag, audit log, and emergency freeze need to be in the
manifest.

Promotion boundary: this is a counsel-gated candidate. It does not authorize
insider sales, remove affiliate/control-person resale limits, or change tax
treatment. It only defines a possible formula for when additional founder, team,
or strategic tokens become unlocked.

## Steem Analogue

Steem handled long-term alignment through Steem Power. Users could power up
liquid STEEM into non-transferable influence, then power down back into liquid
STEEM through equal weekly withdrawals. Current Steem developer docs describe
power down as 13 equal weekly payments, starting one week after initiation. The
Steem whitepaper frames Steem Power as a 13-week vesting commitment.

Useful lesson for ZENO: a delayed exit schedule can align governance and reward
influence with longer-term participation. The burn-indexed accelerator uses a
different mechanism: it keeps insider allocations on a vesting schedule and
allows only capped extra unlocks from lagged eligible protocol-fee burns.

## Core Team Selection

The 10% core team pool should not be granted by social proximity. It should be a
role-based contributor pool with cliffs, vesting, milestones, and clawback or
termination rules where legally available.

Suggested internal subdivision:

| Function | Share of team pool | Tokens |
| --- | ---: | ---: |
| Protocol engineering and settlement | 25% | 25,000,000 |
| Formal methods, proofs, verification | 25% | 25,000,000 |
| Security, incident response, release engineering | 15% | 15,000,000 |
| Tau Net integration, wallet, custody, infra | 15% | 15,000,000 |
| Product, UI, docs, developer experience | 10% | 10,000,000 |
| Future hiring reserve | 10% | 10,000,000 |

Core team role: maintain the protocol, close proof gaps, run releases, build
wallet and UI safety surfaces, operate security response, support integrators,
and execute governance-approved roadmaps. Core team members should not have
unbounded custody over the DAO treasury.

## Stake Distribution Paths

The stake-distribution problem should use the ecosystem and community buckets.
The XP ledger can support eligibility scoring, while token movement stays in a
separate capped distribution program.

The candidate model now makes this a checked boundary. XP, levels, leagues, and
OG status must be non-transferable, non-redeemable for tokens, and have no cash
value. Any fee discount, feature waiver, airdrop, or activity-mined token payout
must sit in a separate budgeted program with counsel review and abuse controls.

Admitted internal paths:

- activity-mined distribution from capped non-wash DEX receipts;
- retroactive testnet and proof-user airdrops from snapshot receipts;
- bonded proof-mining rewards;
- bonded oracle/watcher/operator rewards;
- LP-duration incentives with age, non-wash, and cap gates;
- security bounty and audit rewards;
- liquidity bootstrap under explicit market-making or pool-depth rules.

Forbidden or excluded low-risk shapes:

- XP directly redeemable for ZENO;
- route, token, venue, pool, or counterparty-specific boosts;
- passive revenue share or yield boost from XP, league, level, or OG status;
- full DAO treasury live funding into one immature wallet path.

## Treasury Custody

The DAO/protocol treasury bucket is `250,000,000 ZENO`. It should be modeled as
a governed reserve with staged live-wallet funding.

Current assumption:

```text
TauNetThresholdCustodyMature = false
```

Consequence: full live treasury funding is disabled. The internal custody gate
allows at most `5,000,000 ZENO` in a live treasury wallet while Tau Net threshold
custody is unproven. Single disbursements are capped at `1,000,000 ZENO`, epoch
disbursements at `2,000,000 ZENO`, with a `5-of-7` signer model and a 48-hour
timelock.

This is deliberately conservative because attackers will target wallets,
signers, deployment scripts, and governance controls when the DEX core is hard.

## Operating Runway And Sales

The project can reserve a small, explicit operating runway from non-founder
buckets. A low-risk internal shape is:

- domain, hosting, CI, testnet infrastructure, and compliance costs from the
  DAO/protocol treasury operations sub-budget;
- security audits, bug bounties, and incident response from the security bucket;
- LP depth, market-maker contracts, and launch liquidity from the liquidity
  bootstrap bucket;
- contributor work, proof work, solver work, and operator incentives from the
  ecosystem bucket.

Any treasury sale or conversion should be budgeted before execution, capped per
epoch, logged with purpose and receipt metadata, and run through the treasury
custody boundary. While Tau Net threshold custody is unproven, the live wallet
cap remains `5,000,000 ZENO`, with a `1,000,000 ZENO` single-disbursement cap and
`2,000,000 ZENO` epoch-disbursement cap.

Tokens earned by an account from proof mining, operating, oracle reporting,
watcher work, or protocol fees are different from founder/original R&D vesting.
They should be liquid only after the relevant reward program says they are
earned, transferable, and claimable. Resale still depends on the token's final
legal classification, exchange access, sanctions/KYC restrictions where
applicable, tax reporting, and any insider, affiliate, lockup, or market-abuse
policy that applies to that account.

Operational rule:

```text
earned_work_reward_claimable(account, reward)
and no_active_lockup(account, reward)
and transfer_allowed_by_program(reward)
-> account may transfer or sell at its own risk under applicable law
```

This rule covers earned work rewards. It does not unlock founder vesting early.

## Evidence Lane

Replay:

```bash
python3 tools/check_zeno_treasury_custody_boundary.py \
  internal/tokenomics/ZENO_TREASURY_CUSTODY_BOUNDARY_V0.json
python3 tools/check_tokenomics_reward_safety_envelope.py \
  internal/tokenomics/ZENO_TOKENOMICS_REWARD_SAFETY_ENVELOPE_V0.json
python3 tools/check_burn_indexed_unlock_accelerator.py \
  internal/tokenomics/ZENO_BURN_INDEXED_UNLOCK_ACCELERATOR_V0.json
python3 -m pytest -q tests/tools/test_check_zeno_treasury_custody_boundary.py
```

Related gates:

```bash
python3 tools/check_tokenomics_candidate_model.py \
  internal/tokenomics/ZENO_TOKENOMICS_CANDIDATE_MODEL_V0.json
python3 tools/check_zeno_economic_games_boundary.py \
  internal/tokenomics/ZENO_ECONOMIC_GAMES_BOUNDARY_V0.json
python3 tools/check_covered_user_interface_boundary.py \
  internal/covered_user_interface/COVERED_USER_INTERFACE_BOUNDARY_V0.json
```
