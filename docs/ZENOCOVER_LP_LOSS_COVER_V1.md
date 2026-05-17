# ZenoCover LP Loss Cover V1

ZenoCover's current public replay artifact is the FIRE `lp_loss_cover_v1`
bundle under:

```text
docs/fire_registry/devnet_v1/lp_loss_cover_v1/
```

The covered payoff is:

```text
payoff = N * min(max(HODL_T - LPV_T - D, 0), Cap)
```

The holder receives a capped payment when the final hold value exceeds final LP
value by more than the deductible. The writer posts the certified upper bound as
collateral before settlement.

Run the ZenoCover-facing replay gate with:

```bash
python3 tools/check_zenocover_lp_loss_cover.py --pretty
```

The checker validates the registry bundle hashes, object/instance/lock binding,
runtime certificate hash, proof-tree certificate binding, canonical replay
input, persisted bundle binding, and final settlement deltas. The checked-in
bundle currently settles with `holder_delta = 30`, `writer_delta = -30`,
`artifact_upper = 80`, and `writer_posted = 80`.

## Reserve Solvency Gate

The reserve-solvency checker consumes a manifest with a reserve balance,
existing locked reserve, minimum surplus, and one or more LP-cover bundle
positions:

```bash
python3 tools/check_zenocover_reserve_solvency.py path/to/reserve-manifest.json
```

For each active position, it replays the LP loss-cover bundle and adds the
certified `writer_collateral_required` amount to active obligations. The reserve
passes only when:

```text
existing_locked + active_required_collateral + min_surplus <= reserve_balance
```

The default checked-in LP loss-cover bundle contributes `80` units of active
required collateral.

This is a local FIRE replay claim for one capped LP-loss cover object. It does
not price premiums, admit live market witnesses, prove oracle truth, implement a
production claims workflow, prove portfolio-wide actuarial solvency, or
generalize to every possible protection product.

## Attack Query Simulation Gate

The internal attack-query gate composes the replayed reserve-solvency model, the
claim-verifier model, and the reserve-withdrawal model:

```bash
python3 tools/check_zenocover_attack_queries.py \
  internal/zenocover/ATTACK_QUERY_MANIFEST_V0.json
```

The cross-surface sweep checks bounded sequences where a withdrawal and a
worst-case authorized payout may occur in either order. It rejects manifests
where an accepted withdrawal can leave the reserve below the policy
`min_reserve_after_payout`, where the aggregate payout cap already violates the
policy floor, or where active withdrawal liabilities are lower than replayed
collateral requirements. This is a deterministic attack-query harness, not an
actuarial model or production operations process.

## Legal and Regulatory Boundary

This replay artifact is not a product launch, public offering, regulated risk
product, underwriting program, claims-handling process, or user-facing purchase
flow. It is a deterministic replay surface for one capped LP-loss object.

Any public or production ZenoCover offering must complete counsel-led legal and
regulatory review before user sale, market launch, or external marketing. The
minimum release dossier must include jurisdiction-by-jurisdiction classification,
licensed-carrier or other approved operating-model analysis, reserve and capital
treatment, consumer disclosure review, sanctions/AML review, tax/accounting
review, oracle and basis-risk disclosure, and a written go/no-go record from
qualified counsel.

The current safe operating assumption is software-only and self-custodial. A
user runs, compiles, or interprets the software themselves and directly signs any
transaction they choose to make. The project does not take custody, control user
keys, operate a pooled reserve, collect premiums, make personalized financial
recommendations, select or recommend cover terms, act as a broker or
intermediary, promise payouts, or tell users what to do with funds.

The state-of-the-art research and supervisory read is consistent with that
boundary. DeFi risk-transfer papers are still wrestling with actuarial,
liquidity, oracle, verification, governance, and regulatory problems. Insurance
supervisory sources treat parametric and blockchain-enabled protection products
as use-case-specific classification questions that require jurisdictional,
solvency, market-conduct, and consumer-protection review. The current public
artifact therefore stays a replayable software artifact. There is no current
insurance company, underwriting program, premium collection path, or user-facing
purchase flow.
