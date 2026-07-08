# Adversarial Hardening Pokayoke Packet

Date: 2026-07-05

Status: research obligation matrix with a fail-closed checker.

## Claim Scope

This packet records a first-pass adversarial hardening matrix for ZenoDEX
network scaling work. It names actor thought experiments, disaster states,
mechanism-design updates, side-channel and covert-channel reductions, and the
evidence lanes required before any stronger claim.

It does not promote a production security claim. It does not claim absence of
unknown disasters, side channels, or covert channels. It does not give advisory
models or subagents authority over settlement, state roots, or public claims.

Replay command:

```bash
python3 tools/check_adversarial_hardening_pokayoke_matrix.py --json
```

Primary artifacts:

- `tools/adversarial_hardening_pokayoke_matrix.json`
- `tools/check_adversarial_hardening_pokayoke_matrix.py`
- `tests/test_check_adversarial_hardening_pokayoke_matrix.py`

## Game Surface

The matrix uses named actors so adversarial work stays concrete:

- Alice: honest trader or position holder.
- Bob: liquidity provider.
- Mallory: adversary who can submit malformed inputs, collude, censor, replay,
  observe metadata, and exploit timing.
- Sequencer: ordering and inclusion actor.
- Proof aggregator: recursive proof aggregation actor.
- Oracle reporter: bonded data source actor.
- Governance operator: policy and release actor.

Each scenario records players, actions, information sets, timing, state, and
payoff. The required shape follows the mechanism-design rule:

```text
GameSurface + AttackQuery + BoundedModel + EvidenceLane + PromotionBoundary
```

## Attack Queries

The current matrix covers eight high-severity queries:

1. Stale quote reuse and boundary MEV.
2. Median3 oracle reporter collusion.
3. Proof-mining duplicate reward and claim replay.
4. Perps or zUSD critical action using stale or wrong oracle state.
5. Cross-shard watcher metadata as a covert finality channel.
6. Production config disabling a required verifier or bridge.
7. Advisory model or subagent output trying to authorize settlement.
8. Recursive lifecycle packet replay, stale aggregate roots, or malformed child
   receipt closure.

The common mechanism condition is:

```text
DefectGain <= DetectionProbability * SlashAmount + FutureValueLost
```

For deterministic guards where bad transitions reject before commit:

```text
AttackGain <= 0 after reject-is-no-op
```

## Pokayoke Closure

The matrix requires every high-severity scenario to include:

- Mallory as an actor.
- A named disaster state.
- At least one construction or guarded-transition control.
- `reject_is_no_op`.
- `side_channel_budget`.
- `covert_channel_budget`.
- A non-production evidence lane.
- A scenario-specific promotion boundary.

Control classes include typed state binding, canonical transcripts, authority
binding, bonded downside, receipt-DAG closure, evidence-class binding,
value-at-risk tiers, release-config ratchets, resource budgets, advisory-model
sandboxing, and Pokayoke interlocks.

## Side And Covert Channels

The matrix treats these as explicit channels, not vague residual risk:

- public error classes and diagnostic shape;
- quote age, batch boundary, and partial-fill metadata;
- reporter timing and aggregate participation hints;
- verifier timing and mutation-distance hints;
- liquidation threshold search information;
- watcher status timing, posting order, and metadata fields;
- startup logs and production profile details;
- model confidence, trace order, and generated receipt-like fields.

The reduction strategy is to bind authority to canonical receipts, keep public
reject classes stable, redact sensitive detail from public responses, bound
metadata bits, reject unknown production config fields, and publish verifier
evidence rather than advisory traces.

## Mechanism Updates

The matrix pushes these mechanism-design constraints:

- Quote and settlement certificates must bind state, profile, batch identity,
  and nonce before any state mutation.
- Critical oracle feeds need value-at-risk tiers for quorum, freshness,
  reporter independence, and bonded downside.
- Proof-mining rewards must be keyed by canonical proof identity, verifier
  profile, and payout nonce.
- Perps and zUSD oracle authorizations must bind the consumed oracle value to
  position, collateral, vault, and risk-parameter roots.
- Cross-shard finality claims must depend on canonical receipts and quorum
  roots, with observer metadata kept non-authoritative.
- Production profiles must reject weaker flags, malformed booleans, fixture
  modes, faucet modes, missing verifier contracts, and path lookup.
- Advisory systems may rank candidates only. Verifier gates decide settlement
  authority and claim promotion.

## Recursive Lifecycle Admission Thought Experiment

Plain thought experiment, with no LMQL dependency:

```text
Actors:
  Alice expects recursive proof-backed settlement to finalize.
  Bob supplies liquidity or downstream balance exposure.
  Mallory controls malformed packet input and may replay stale child receipts.
  Sequencer chooses packet ordering within modeled limits.
  Proof aggregator builds recursive lifecycle packets.
  Governance operator configures verifier and profile policy.

Mallory move:
  Submit a recursive lifecycle admission packet whose internal fields are
  self-consistent, but whose post_state_root, feature_suite_hash, aggregate
  asset-delta root, or child receipt set belongs to a stale ledger context.

Disaster state:
  ZenoLedger or Tau admission accepts recursive proof evidence under the wrong
  ledger context, then advances checked height or emits app-hash evidence.

Required PokaYoke closure:
  The packet checker validates internal obligations.
  The ledger admission path binds packet roots to the actual header and proof
  metadata.
  Missing, malformed, or stale packets reject before checked height advances.
  Public reject classes remain stable enough not to leak mutation-distance
  details.
```

Current evidence for this scenario:

```bash
python3 -m pytest tests/integration/test_zeno_ledger_recursive_lifecycle_admission.py -q
python3 -m pytest tests/tools/test_check_recursive_lifecycle_admission.py -q
```

This is scoped evidence. It does not prove that all recursive proof aggregation
side channels or RISC0 soundness assumptions are closed.

## LMQL Feasibility

LMQL does not inherently require a local LLM. Its documented backend model can
target hosted or local backends. For ZenoDEX, the safer operating mode is:

```text
LMQL scenario generator
  -> JSON candidate thought experiments
  -> schema checker
  -> deterministic matrix checker
  -> targeted replay, fuzz, SMT, Lean, ESSO, RISC0, or Tau evidence
```

LMQL should be optional. The no-LMQL matrix is the source of truth because it is
plain JSON plus a deterministic checker. LMQL can help generate additional
Alice/Bob/Mallory cases by filling structured fields such as:

```text
actor_capabilities
pre_state
mallory_action_sequence
disaster_state
side_channel
covert_channel
reject_is_no_op_hook
promotion_requirement
```

Required LMQL guardrails:

- run with a fixed prompt template and pinned model/backend;
- emit JSON only, never direct code changes;
- reject outputs that fail the matrix schema;
- treat duplicate or low-novelty scenarios as no-ops;
- forbid `production_ready`, settlement authority, or claim promotion labels;
- record backend, prompt hash, model name, and output hash;
- require deterministic local evidence before any scenario becomes more than a
  hypothesis.

Potential LMQL query shape:

```text
Given the existing matrix schema and a target surface, generate one new
Mallory-centered scenario. Output JSON with id, actors, game_surface,
attack_query, bounded_model, disaster_state, controls, side_channels,
covert_channels, mechanism_update, game_theory_condition, evidence_lane, and
promotion_boundary. Never claim production readiness.
```

If a local LLM is available, LMQL can use it for private iteration. If not, a
hosted backend is acceptable for low-sensitivity scenario generation. Do not
send secrets, private keys, unpublished exploit details, or private production
configuration to a hosted model.

## Evidence

Validated in this packet:

```bash
python3 tools/check_adversarial_hardening_pokayoke_matrix.py --json
python3 -m pytest -q tests/test_check_adversarial_hardening_pokayoke_matrix.py
python3 -m pytest -q tests/test_zenodex_oracle_collusion_bound.py
python3 -m pytest tests/integration/test_zeno_ledger_recursive_lifecycle_admission.py -q
```

This evidence validates coverage obligations and non-claim boundaries. It is
not runtime proof that the named disasters are closed across all production
paths. The oracle collusion bound also covers the median3 value-at-risk subcase:
if two controlled reporters can own the median, expected bonded downside plus
future value loss must cover the declared action value-at-risk with the
configured margin.

## Residual Risk

- Runtime gates still need negative replay evidence for each scenario family.
- Side-channel budgets need scoped measurements or static field audits.
- Hidden beneficial ownership among reporters remains partly off-chain.
- Network-layer traffic analysis is outside this packet.
- Scaling work must repeat this matrix at each new sharding, batching,
  sequencer, watcher, or proof-aggregation boundary.

## Next Frontier

Promote one scenario at a time from obligation matrix to runtime evidence:

1. Add or identify the negative replay for the bad trace.
2. Prove or test reject-is-no-op.
3. Bind the same control to a Tau, ESSO, Lean, RISC0, replay, or deterministic
   checker artifact.
4. Update the claim registry only after the local evidence exists.
