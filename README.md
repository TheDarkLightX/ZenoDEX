<p align="center">
  <img src="assets/branding/zenodex/zenodex_full_transparent_1024.png" alt="ZenoDEX" width="360">
</p>

# ZenoDex

ZenoDex is a high-assurance, production-candidate decentralized exchange and
token-economics stack for Tau Network. It uses a hybrid model: deterministic
Python computes operational state, while Tau Language specs, ESSO kernels, Lean
proofs, and replayable certificates check the safety boundaries around
settlement.

This README is the front door. Detailed assurance evidence lives in the linked
docs, proof files, kernels, and replay scripts.

## Current Status

This checkout is a **high-assurance, production-candidate DEX implementation
with scoped correct-by-construction safety lanes**. The strongest value-moving
surfaces are backed by deterministic functional core code, replayable
certificates, Lean proofs, ESSO kernels, Tau specs, and explicit claim
boundaries. Full live-production readiness still depends on deployment gates,
oracle-network evidence, external audit, and live proof operations.

```text
bounded spot / UPBA assurance: high, production-candidate
CBC posture: scoped to lanes with runtime verifier / proof-gate binding
general protocol architecture: production-candidate with scoped open gates
full live production readiness: open deployment, oracle, audit, and live-proof gates
```

Correct-by-construction means the claim is tied to a concrete lane where invalid
states are blocked by constructors, runtime verifiers, proof gates, or committed
certificate checks. The README avoids treating that as a blanket guarantee for
every future feature or unbounded search space.

Current high-signal status:

- **UPBA v1 bounded price-grid path** is integrated into runtime, docs, tests,
  claims registry, the spot evidence gate, and the spot proof gate.
- **DHAI** is currently `81 / 100`, level `L3_STRONG_BOUNDED_DISASTER_HARDENING`.
- **Core closed disaster axes** are currently `29/29` under the bounded public
  replay lane, with a larger `125`-axis inventory tracked as search backlog.
- **ZenoOracle devnet disaster harness** covers `17/17` promoted local oracle
  disaster states under the verifier shell.
- **Risc0 state proofs** exist as an opt-in restricted TauSwap transition lane.

Run live local status checks from the current checkout with:

```bash
python3 tools/permissionless_assurance.py status
python3 tools/check_claims_registry.py
```

## Quick Start

Install the runtime and test dependencies:

```bash
pip install -r requirements.txt
```

Clone Tau dependencies if you want to run Tau-backed checks locally:

```bash
mkdir -p external
cd external
git clone https://github.com/IDNI/tau-lang.git
git clone https://github.com/IDNI/tau-testnet.git
cd ..
```

Start the local API and UI:

```bash
PERPS_API_ENABLED=true ZUSD_API_ENABLED=true DEMO_API_TOKEN=sekret \
  python3 -m src.integration.api_server

cd tools/dex-ui
npm install
VITE_DEMO_MODE=false \
  API_PROXY_TARGET=http://127.0.0.1:8000 \
  VITE_API_TOKEN=sekret \
  npm run dev -- --host 127.0.0.1 --port 5173
```

## Key Features

- **Spot DEX core**: deterministic CPMM settlement, LP accounting, bounded
  integer arithmetic, and replayable settlement checks.
- **UPBA v1**: uniform-price batch auction lane for scoped single-pool exact-in
  full-fill batches with bounded price-grid evidence.
- **Perpetuals and zUSD**: epoch funding, bounded insurance modeling, synthetic
  stablecoin components, and risk gates.
- **ZenoOracle**: devnet oracle pipeline, signed reports, aggregate reads,
  consumer profiles, and critical-action mapping.
- **Proof-carrying optimization**: route, settlement, and batch certificates bind
  solver output to deterministic verifiers.
- **Confidential extensions**: sealed-bid and TEE/FHE private-compute surfaces,
  kept behind explicit experimental boundaries.
- **Permissionless hosting**: rootless local-node and operator tooling for
  reproducible deployment experiments.

## UPBA v1 Status

The newest spot-clearing lane is the UPBA v1 bounded price-grid path:

- `src/core/uniform_batch_price_grid_table.py` recomputes every candidate in a
  configured bounded price grid.
- `src/integration/dex_engine.py` can require complete UPBA price-grid evidence
  before accepting a UPBA certificate.
- `src/integration/upba_production_config.py` exposes the strict helper
  `make_upba_v1_bounded_price_grid_engine_config()`.
- `lean-mathlib/Proofs/UniformBatchOptimality.lean` proves the bounded-grid
  weak-optimality theorem used by the claim.
- `tools/run_spot_evidence.sh` and `tools/run_spot_proof_assurance_gate.sh`
  exercise the runtime and proof lane.

The scoped claim is:

```text
single-pool exact-in full-fill UPBA
+ bounded integer price grid
+ complete table evidence
+ deterministic runtime verifier
+ strict engine config
+ focused Python tests
+ Lean bounded-grid optimality proof
```

Open UPBA work:

- exact-out support;
- partial-fill optimality;
- multi-hop and multi-pool clearing;
- LP add/remove exclusion or a separate safe batch lane;
- fair order-inclusion policy;
- oracle / mark-price separation;
- batch-boundary MEV modeling;
- Tau Tables integration once Tau Tables is available;
- zkVM proof support for the UPBA transition.

## Architecture

ZenoDex uses a layered assurance model:

1. **Functional core**: small deterministic settlement and math code under
   `src/core/`.
2. **Domain state**: balances, pools, LP tables, nonces, and canonical state
   roots under `src/state/`.
3. **Integration shell**: parsing, signature policy, certificates, Tau gates,
   oracle authorization, and API surfaces under `src/integration/`.
4. **Verified kernels**: ESSO models and generated/reference adapters under
   `src/kernels/` and `generated/`.
5. **Proof layer**: Lean theorem files under `lean-mathlib/Proofs/`.
6. **Replay gates**: focused test, fuzz, proof, and evidence scripts under
   `tests/` and `tools/`.

Value-moving decisions should follow this pattern:

```text
raw input
-> parsed / typed domain object
-> deterministic functional-core result
-> certificate or proof witness
-> runtime verifier
-> state transition
```

## Trust Model and Verification

The goal is: verify the transition, then accept the state.

Users and operators can verify ZenoDex at several levels:

- **Full replay**: run a node and recompute blocks, state commitments, and DEX
  transitions.
- **Header and commitment checks**: verify signed headers, `state_hash`, and
  `app_hash` across independent nodes.
- **Certificate checks**: verify route, settlement, batch, and proof packets
  against canonical commitments.
- **ZK / validity proofs**: verify a succinct proof that a committed transition
  was executed correctly, when the deployment profile requires such proofs.

Tau Testnet Alpha currently provides signed blocks, state commitments, and
optional DHT-bound state proofs. The concrete Risc0 lane in this repo proves a
restricted TauSwap transition subset:

- `CREATE_POOL`
- `SWAP_EXACT_IN`
- restricted transaction shape and native sync semantics

Reference docs:

- [docs/tau_state_proof_v1.md](docs/tau_state_proof_v1.md)
- [docs/tau_state_proof_risc0_tauswap_v1.md](docs/tau_state_proof_risc0_tauswap_v1.md)
- [docs/tau_testnet_state_proof_patch.md](docs/tau_testnet_state_proof_patch.md)
- `zk/state_proof_risc0/`

## How ZK Proofs Can Scale ZenoDex

The useful pattern is proof-carrying execution:

```text
pre_state_commitment + tx_or_batch_commitment + program_id
  -> proved execution
  -> post_state_commitment
```

A prover runs the transition once, produces a validity proof, and publishes that
proof with the block or settlement artifact. Validators, light clients, bridges,
and indexers can verify the short proof instead of replaying the whole
transition.

The current Risc0 lane proves a Rust zkVM guest that mirrors a supported DEX
transition subset. It does not prove arbitrary Python execution directly. The
practical expansion path is:

```text
Python functional core as reference
-> deterministic Rust/zkVM guest or generated kernel
-> parity tests and certificates
-> succinct validity proof for clients
```

This enables:

- light clients that verify signed headers plus `state_hash` / `app_hash` plus a
  state proof;
- bridge contracts or bridge agents that accept ZenoDex state only when a proof
  binds to a finalized committed state;
- rollup-style batching, where many trades are folded into one proven state
  transition;
- proof-carrying UPBA solvers, where complex price discovery is proposed
  off-chain and verified by a small deterministic checker;
- future private witness lanes, when a circuit can hide selected witness data
  while proving the public state transition.

Hard requirements:

- deterministic integer semantics;
- canonical serialization for public inputs;
- fixed circuit / program ids governed like consensus code;
- data availability for state and transactions clients need to audit;
- fail-closed behavior when a required proof is missing or bound to the wrong
  state;
- parity tests proving the zk guest and Python reference produce identical
  commitments on the supported domain.

Near-term ZK expansion target:

1. Extend the Risc0 guest toward UPBA v1 bounded-grid settlement.
2. Bind the UPBA certificate, price-grid table root, pre-state hash, batch
   commitment, and post-state hash into the proof journal.
3. Add recursive or batched proofs after single-batch proof generation is
   stable.
4. Make proof requirement a deployment profile.

## Assurance Snapshot

<!-- BEGIN GENERATED:ASSURANCE_RELEASE_SNAPSHOT -->
The pinned release replay for the release tree dated `2026-04-10` was green:

- acceptance TCB: `361 passed`, `99.4%` branch coverage
- critical gate: `735 passed, 1 skipped`, `99%` branch coverage
- release gate: `passed end to end`
- mutation gate: `7 killed, 0 survived, 0 inconclusive`
- fuzz gate: `11 passed`
- snapshot recovery: `19 passed`
- Tau syntax: `62/62`
- Tau traces: `1/1`

This is historical release evidence for the pinned release tree. It is not a live statement about the current checkout.
For live status on the current checkout, run `python3 tools/permissionless_assurance.py status`.

Important derivatives note:

- The published v1.1 funding-rate formal claim is now the decomposed one:
  `funding_rate_market_v1` for phase/state transitions plus
  `funding_rate_settlement_witness_v1_1` for settlement arithmetic, both in the release-backed assurance lane.
- The monolithic `funding_rate_market_v1_1` kernel remains useful as a parity/reference artifact, but it is not part of the published formal release claim.
- `funding_rate_market_v1` and `curve_selection_market_v1` remain `disputed` in the claims registry for settlement authorization semantics and should not be treated as authorization-complete public settlement guarantees.
- The bounded TLC/TLA+ claim surface is summarized in [docs/TLA_CLAIM_SUMMARY.md](docs/TLA_CLAIM_SUMMARY.md) and release-checked via `python3 tools/render_tla_claim_summary.py --check`.

Release vocabulary:
- `release-backed`: included in the current published formal/public assurance claim
- `public replay`: reproducible from a clean checkout plus the documented external toolchains via the shipped replay/checker surface
- `authorization-complete`: safe to treat as a public settlement-authorizing guarantee without extra trusted environment inputs
- `disputed`: intentionally excluded from stronger public authorization claims until the witness/auth lane is trust-complete

More detail:
- [docs/ASSURANCE_RELEASE_SNAPSHOT.md](docs/ASSURANCE_RELEASE_SNAPSHOT.md)
- [docs/PUBLIC_ASSURANCE_REPLAY.md](docs/PUBLIC_ASSURANCE_REPLAY.md)
- [docs/TLA_CLAIM_SUMMARY.md](docs/TLA_CLAIM_SUMMARY.md)
- [docs/ASSURANCE_GLOSSARY.md](docs/ASSURANCE_GLOSSARY.md)
- [docs/claims_registry.yaml](docs/claims_registry.yaml)
<!-- END GENERATED:ASSURANCE_RELEASE_SNAPSHOT -->

Replay commands are documented in
[docs/PUBLIC_ASSURANCE_REPLAY.md](docs/PUBLIC_ASSURANCE_REPLAY.md).

## Disaster Hardening

Current bounded disaster-hardening metric:

```text
DHAI = 81 / 100
level = L3_STRONG_BOUNDED_DISASTER_HARDENING
hardness_subscore = 100.0 / 100
assurance_subscore = 72.6 / 100
```

The public replay lane currently reports:

- `29/29` closed core disaster axes;
- `29/29` closed core axes mapped to proof schemas;
- `17/17` closed ZenoOracle devnet disaster states;
- `65/65` closed MacOS scout witnesses;
- `43 -> 0` reachable MacOS scout witnesses after hardening.

Detailed evidence:

- [docs/DISASTER_HARDNESS_ASSURANCE_METRIC.md](docs/DISASTER_HARDNESS_ASSURANCE_METRIC.md)
- [docs/DISASTER_STATE_COVERAGE.md](docs/DISASTER_STATE_COVERAGE.md)
- [docs/STATEFUL_DISASTER_STATE_WITNESSES.md](docs/STATEFUL_DISASTER_STATE_WITNESSES.md)
- [docs/STATEFUL_RELEASE_GUARDRAILS.md](docs/STATEFUL_RELEASE_GUARDRAILS.md)

## Zeno-Style Tokenomics

The name ZenoDex references Zeno-style convergence: a rule can keep applying
smaller steps while approaching a floor.

```text
S_{n+1} = F + r (S_n - F)
```

`S_n` is supply after step `n`, `F` is the floor, and `0 < r < 1` is the
remaining fraction. Every finite step stays above the floor, and the sequence
approaches the floor as the number of steps grows.

Ledger reality is discrete. Amounts are integers in base units, so the protocol
uses deterministic rounding and dust accounting rather than infinite decimal
precision or repeated redenomination. The high-safety recommendation is `18`
base-unit decimals for protocol tokens and LP shares, plus explicit dust
accounting where fractional ideal math would otherwise disappear.

Related docs:

- [docs/TOKEN_VERSIONS.md](docs/TOKEN_VERSIONS.md)
- [docs/TOKEN_GOVERNANCE.md](docs/TOKEN_GOVERNANCE.md)
- [docs/ALGORITHMS.md](docs/ALGORITHMS.md)

## Risk Profiles

ZenoDex organizes specs into risk-based profiles:

- **Tier 1 / Recommended**: lowest-risk deterministic bounded rules.
- **Tier 2 / Medium**: more aggressive tokenomics and feature combinations.
- **Tier 3 / High**: experimental or dynamic designs.

Start with:

- `src/tau_specs/recommended/`
- [docs/TAU_SPECS_PROFILES.md](docs/TAU_SPECS_PROFILES.md)
- `src/tau_specs/RISK_TIERS.md`

## Repository Layout

- `src/core/`: deterministic DEX math and settlement core.
- `src/state/`: state tables, canonical roots, balances, pools, LPs, nonces.
- `src/integration/`: API, engine shell, certificates, Tau and oracle bridges.
- `src/tau_specs/`: Tau specifications and recommended profiles.
- `src/kernels/`: ESSO models and proof-oriented kernels.
- `lean-mathlib/Proofs/`: Lean proof artifacts.
- `tools/`: evidence gates, operator scripts, replay tools, and UI.
- `tools/dex-ui/`: Vite + React frontend.
- `docs/`: protocol notes, assurance docs, papers, and roadmaps.
- `tests/`: unit, integration, property, formal, and replay tests.
- `external/`: Tau dependencies, usually git-ignored locally.
- `zk/`: Risc0 state-proof implementation.

## Important Docs

System and assurance:

- [docs/SPECIFICATION.md](docs/SPECIFICATION.md)
- [docs/SECURITY_POSTURE.md](docs/SECURITY_POSTURE.md)
- [docs/PUBLIC_ASSURANCE_REPLAY.md](docs/PUBLIC_ASSURANCE_REPLAY.md)
- [docs/claims_registry.yaml](docs/claims_registry.yaml)
- [docs/PRODUCTION_GATE.md](docs/PRODUCTION_GATE.md)

UPBA and spot:

- [docs/UPBA_V1_EVIDENCE_BOUNDARY.md](docs/UPBA_V1_EVIDENCE_BOUNDARY.md)
- [docs/UPBA_TAU_TABLES_DESIGN_SPEC.md](docs/UPBA_TAU_TABLES_DESIGN_SPEC.md)
- [docs/UPBA_V1_CERTIFICATE.md](docs/UPBA_V1_CERTIFICATE.md)
- [docs/ALGORITHMS.md](docs/ALGORITHMS.md)

Oracle, perps, and zUSD:

- [docs/ZENO_ORACLE_MVP_STATUS.md](docs/ZENO_ORACLE_MVP_STATUS.md)
- [docs/ZENO_ORACLE_CRITICAL_ACTION_MAP.md](docs/ZENO_ORACLE_CRITICAL_ACTION_MAP.md)
- [docs/derivatives/PERP_SOTA_ROADMAP.md](docs/derivatives/PERP_SOTA_ROADMAP.md)
- [docs/ZUSD_TAU_WALLET.md](docs/ZUSD_TAU_WALLET.md)

State proofs:

- [docs/tau_state_proof_v1.md](docs/tau_state_proof_v1.md)
- [docs/tau_state_proof_risc0_tauswap_v1.md](docs/tau_state_proof_risc0_tauswap_v1.md)
- [docs/tau_testnet_state_proof_patch.md](docs/tau_testnet_state_proof_patch.md)

Operations:

- [docs/PERMISSIONLESS_HOSTING.md](docs/PERMISSIONLESS_HOSTING.md)
- [docs/RC1_SCOPE.md](docs/RC1_SCOPE.md)
- [docs/RC1_READINESS.md](docs/RC1_READINESS.md)

## Tests and Evidence Gates

Common local checks:

```bash
python3 tools/check_claims_registry.py
pytest -q tests/core/test_uniform_batch_clearing.py \
  tests/core/test_uniform_batch_optimality.py \
  tests/core/test_uniform_batch_price_grid_table.py \
  tests/integration/test_dex_engine_uniform_batch_certificate.py
```

Spot evidence:

```bash
bash tools/run_spot_evidence.sh
bash tools/run_spot_proof_assurance_gate.sh
```

Production-style local gate:

```bash
bash tools/prod_gate.sh --skip-docker --skip-ui
```

Tau syntax and traces:

```bash
bash tests/tau/test_specs_syntax.sh
python3 tools/recommended_tau_smoke.py
```

## Current Limits

Open work before a full live-production claim:

- production Oracle network evidence;
- live reporter/proof economics settlement;
- external audit;
- production code signing and release transparency;
- broader zkVM proof coverage beyond the current restricted TauSwap lane;
- exact-out UPBA and partial-fill UPBA;
- multi-hop UPBA and routing-generator completeness;
- snapshot and migration replay for all production state surfaces.

## License

See [LICENSE](LICENSE).
