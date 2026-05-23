# ZENO Tokenomics Candidate Model V0

Status: internal research gate. This is a candidate-model validator for a
1,000,000,000 ZENO supply design. It uses the eight-bucket draft allocation as
the current internal candidate. It is not a public assurance claim, launch
clearance, legal conclusion, or secondary-market value claim.

## Candidate Allocation

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

The current internal unlock model starts with 70,000,000 ZENO circulating
through non-insider buckets, a 7% launch float. The checker now rejects a
candidate with launch circulation above 8%. Insider and strategic buckets have a
12-month cliff and 50-month duration. The 50-month duration is an internal
candidate parameter chosen to exceed the 48-month insider minimum and produce
exact integer monthly releases across the founder, team, and strategic partner
buckets. A weekly drip can be substituted after a deterministic remainder rule is
specified and tested.

The model can later add a burn-indexed unlock accelerator. The safe candidate
shape is capped extra unlock from lagged, eligible, organic protocol-fee burns.
It must exclude wash volume, related-party burns, treasury-funded self-unlocks,
and route/pool/venue-specific steering. It also must preserve the cliff and
remain inactive until counsel and governance gates pass.

## Game Surface

Players:

- allocation recipients with launch unlocks and vesting schedules;
- value-moving operators, oracle reporters, and proof miners;
- protocol treasury and reserve controllers funding rewards, rebates, buybacks,
  and cover spend;
- external reviewers, including counsel, who remain outside the replay model.

Actions:

- allocate fixed supply across categories;
- unlock an initial fraction and then vest linearly by month;
- fund operating runway only from explicit treasury, security, ecosystem, or
  liquidity-bootstrap budgets;
- pay bounded epoch rewards and other value-capture spend from a funded budget;
- grant value-moving roles only with bonded downside and delayed withdrawal.
- keep XP, levels, leagues, and OG status non-transferable and separate from
  token distributions.

Timing:

1. Candidate supply and allocations are fixed.
2. Launch preconditions are checked.
3. Epoch value-capture caps are checked against funded budget.
4. Value-moving roles are checked for bond, slash, reward, and withdrawal-delay
   constraints.

## Attack Query

The validator searches for structural candidate failures:

```text
public_launch_allowed
or allocation_total != 1_000_000_000
or epoch_spend_cap > funded_epoch_budget
or insider_extra_release > burn_share_cap * eligible_burn
or manipulated_burn_unlock_profit > 0
or XPTransferable
or XPRedeemableForTokens
or value_moving_role_with_authority_and_no_bond
or DefectGain > SlashAmount + FutureValueLost
```

Any satisfying row rejects the candidate. The bounded model treats counsel
review, public launch readiness, and market-value claims as explicit non-claims.

## Bounded Model

The replay uses integer token amounts and basis points. It validates:

- exact 1,000,000,000 total supply;
- exact eight-bucket draft distribution by allocation ID and amount;
- unique allocation IDs and exact allocation sum;
- launch circulation at or below 8%;
- bounded initial unlocks under a manifest policy cap;
- insider cliff and vesting-duration minimums;
- integer initial unlock and monthly linear vesting amounts;
- required launch preconditions, including counsel review;
- the covered user interface boundary gate for self-custody, user initiation,
  objective parameters, fixed disclosed fees, and no trade recommendations;
- the economic-games boundary gate for XP, benefits, activity-mined
  distributions, bonded work rewards, and forbidden game shapes;
- the reward-safety envelope gate for bounded activity-mined distributions,
  wash-trade costs, funded budgets, and XP non-entitlement;
- the burn-indexed unlock accelerator gate for capped post-cliff acceleration
  from lagged eligible burns;
- the treasury custody boundary gate for staged funding, threshold signing,
  timelocks, spending caps, signer controls, and Tau Net wallet maturity;
- the gamification policy: XP is non-transferable, not redeemable for tokens,
  has no cash value, and cannot create an automatic discount or feature-waiver
  entitlement without a separate budgeted counsel-gated program;
- internal-only launch status with `public_launch_allowed = false`;
- funded epoch value-capture spend caps;
- fee-split basis points totaling at most 10,000;
- required value-moving roles: `oracle_reporter`, `proof_miner`, and `operator`;
- bonded downside for each value-moving role.

The first-pass role condition is:

```text
DefectGain <= SlashAmount + FutureValueLost
```

The role has enough slashable or foregone value in the bounded model to cover
the declared maximum one-epoch defect gain.

## Evidence Lane

Replay command:

```bash
python3 -m pytest -q tests/tools/test_check_tokenomics_candidate_model.py
```

Direct manifest command:

```bash
python3 tools/check_tokenomics_candidate_model.py internal/tokenomics/ZENO_TOKENOMICS_CANDIDATE_MODEL_V0.json
python3 tools/check_tokenomics_reward_safety_envelope.py internal/tokenomics/ZENO_TOKENOMICS_REWARD_SAFETY_ENVELOPE_V0.json
python3 tools/check_zeno_treasury_custody_boundary.py internal/tokenomics/ZENO_TREASURY_CUSTODY_BOUNDARY_V0.json
```

The test suite covers an accepted 1B internal candidate and rejects allocation
sum drift, public-launch enablement before counsel review, unbonded
value-moving authority, role reward caps above budget, short insider vesting,
launch float above the policy cap, transferable XP policy, missing launch
preconditions, and public-claim promotion.

The reward-safety envelope checks the current bounded fee-gated identity reward
and pro-rata reward budget examples against wash-trade and funded-budget
constraints. It is a mechanism-modeling input for internal review.

## Promotion Boundary

This artifact can support internal iteration on tokenomics parameters. It does
not support a claims-registry entry, public launch, legal clearance, secondary
market value statements, or a complete economic-security claim.

Promotion would require a fixed production candidate manifest, counsel review,
broader mechanism-security modeling, launch-governance review, and live
settlement integration evidence.
