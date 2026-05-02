# Zeno Oracle Production Gates

Status: build plan for the public Oracle MVP.

This document turns the Zeno Oracle MVP design into release gates. The goal is
to avoid a common oracle failure pattern: shipping a convenient price feed first
and adding safety receipts later. Zeno Oracle should ship in the opposite order:
consumer-bound receipts first, broader public reporting later.

## Release Principle

```text
ProductionOracleRead :=
  AcceptedReadReceipt
  and CriticalActionBinding
  and ReplayVerifierPasses
  and ReporterIncentivesLive
```

Plain English: a production oracle read is not just a number. It is a number
plus a receipt, a binding to the consuming action, a replay path, and a live
economic surface for reporters and challengers.

## Gate 0: Design Snapshot

Purpose: publish the high-level public contract without exposing internal
proof-search machinery or unreleased implementation details.

Required before moving on:

- public MVP design document exists;
- non-claims are explicit;
- critical reads are receipt-based;
- token incentive surfaces are listed;
- uncertainty math is specified at the first concrete level.

Current public entry point:

- `docs/ZENO_ORACLE_MVP_DESIGN.md`

## Gate 1: Canonical Object Format

Purpose: make every oracle object hash-stable and replayable.

Required public artifacts:

- canonical `QuerySpec` format;
- canonical `ReportSigningPayload` format;
- canonical `Report` format;
- canonical `AggregateReceipt` format;
- canonical `AcceptedReadReceipt` format;
- canonical `ConsumerActionReceipt` format;
- deterministic JSON or binary canonicalization rules;
- positive vectors and malformed negative vectors.

Acceptance rule:

```text
ObjectAccepted -> CanonicalHashMatches and SchemaValid and DomainValid
```

The important part is `DomainValid`: schema validation alone cannot prove that
a query, report, or read is semantically safe.

## Gate 2: Local Replay Verifier

Purpose: let a user recompute why a read was accepted.

The verifier should accept a receipt bundle and return one of:

| Status | Meaning |
| --- | --- |
| `accepted` | every required receipt and dependency replayed cleanly |
| `rejected` | at least one required check failed |
| `inconclusive` | dependency, toolchain, or environment data is missing |

Required behavior:

- fail closed on missing dependencies;
- fail closed on unsupported receipt types;
- fail closed on dependency order violations;
- fail closed on receipts that are not reachable from the terminal read/action
  closure;
- fail closed on stale or open disputes;
- fail closed on weak evidence for critical consumers;
- fail closed on mismatched query IDs, value hashes, or action IDs;
- preserve raw machine-readable failure reasons.

Non-goal: the replay verifier does not decide whether a market price is
philosophically true. It decides whether a specific receipt satisfies the
declared policy.

## Gate 3: Reporter Binary

Purpose: make reporting easy enough that ordinary users can participate.

The first user-facing binary should support:

- key generation and key import;
- reporter registration preview;
- bond requirement preview;
- query discovery;
- source adapter configuration;
- report signing;
- report submission;
- expected reward preview;
- dispute/slash status display;
- local dry-run mode.

The binary should never hide risk from the reporter. Before a reporter submits,
it should display:

```text
required_bond
slash_exposure
query_reward_budget
expected_reward
dispute_window
source_policy
reporting_frequency
```

## Gate 4: Token Incentive Safety

Purpose: make the permissionless-human reporting model economically coherent.

Required surfaces:

- reporter bond;
- query reward budget;
- reporter reward;
- dispute bond;
- slash settlement;
- fee split into reporter reward, treasury, and burn.

Minimum safety laws:

```text
RewardPaid <= QueryBudgetRemaining
SlashPaid <= ReporterBondAvailable
DisputeSlashPaid <= DisputeBondAvailable
ReporterShare + TreasuryShare + BurnShare <= FeePaid
```

These are budget laws, not token-price promises. They prevent the oracle from
creating liabilities larger than verified balances.

## Gate 5: Critical ZenoDEX Adapter

Purpose: connect the Oracle to ZenoDEX without letting a raw report leak into
settlement, liquidation, minting, or trigger execution.

Required adapter behavior:

- every critical call takes an accepted read receipt ID;
- every critical call takes a consumer-action receipt ID;
- the action receipt binds the consumer module, action kind, query ID, value
  hash, epoch/window, freshness policy, and evidence class;
- feature flags can disable oracle-backed critical actions globally;
- devnet `O2` reads are rejected unless the module explicitly declares a devnet
  mode.

The adapter should expose a small predicate to downstream modules:

```text
OracleUseOK(action, receipt_bundle) -> bool
```

No downstream module should reconstruct Oracle policy by hand.

## Gate 6: Public Testnet

Purpose: run the first live-but-limited oracle economy.

Required properties:

- at least three independent reporter identities for `median_3`;
- documented source policy for the first pair;
- bounded query reward budgets;
- live dispute window;
- public replay verifier;
- public incident procedure;
- no production settlement dependency until replay health is stable.

The first official pair can be `AGRS/ZDEX`, but the pair should be treated as a
test of the full receipt system, not just a price feed.

## Gate 7: Production Candidate

Purpose: decide when a critical consumer can safely depend on Zeno Oracle.

Minimum required evidence:

- replay verifier passes on fresh and historical receipt bundles;
- stale, weak, disputed, malformed, and misbound bundles reject;
- reporter binary can run from a clean install;
- token budget, bond, reward, dispute, and slash accounting have replay tests;
- ZenoDEX critical adapter rejects raw values and wrong-receipt reuse;
- public docs explain what is proved, what is checked, and what is assumed.

## Current Next Build Target

The next concrete implementation target is:

```text
zenodex-oracle verify <bundle>
```

The current public shell for that target is:

```text
python3 tools/zenodex_oracle.py verify <bundle>
```

To generate a minimal local sample bundle:

```text
python3 tools/zenodex_oracle.py sample-bundle --output /tmp/oracle-bundle.json
python3 tools/zenodex_oracle.py verify /tmp/oracle-bundle.json
```

It should verify a local receipt bundle and produce stable JSON:

```json
{
  "status": "accepted",
  "query_id": "sha256:...",
  "read_receipt_id": "sha256:...",
  "consumer_action_receipt_id": "sha256:...",
  "evidence_class": "O3",
  "checked_at_epoch": 123,
  "not_claimed": [
    "does_not_claim_true_market_price",
    "does_not_claim_source_honesty",
    "does_not_claim_production_network_live"
  ]
}
```

The first implementation can be local-only. Network submission, reporter
registration, token settlement, and public dispute governance can then attach to
the same receipt format.
