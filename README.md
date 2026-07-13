# ZenoDEX

<p align="center">
  <img src="assets/branding/zenodex/zenodex_full_transparent_1024.png" alt="ZenoDEX logo" width="320">
</p>

ZenoDEX is a high-assurance, production-candidate decentralized autonomous
exchange for Tau Network. It uses a hybrid model: deterministic Python computes
operational state, while Tau Language specs, ESSO kernels, Lean proofs, and
replayable certificates check the safety boundaries around settlement.

This README is the front door. Detailed assurance evidence lives in the linked
docs, proof files, kernels, and replay scripts.

## Contents

- [Install And Load The Current Testnet](#install-and-load-the-current-testnet)
- [Why The Name ZenoDEX?](#why-the-name-zenodex)
- [Current Status](#current-status)
- [Assurance Snapshot](#assurance-snapshot)
- [Design Principles](#design-principles)
- [Core Features](#core-features)
- [Features](#features)
- [Quick Start](#quick-start)
- [ZenoLedger Node Operations](#zenoledger-node-operations)
- [Public Testnet Direction](#public-testnet-direction)
- [Repository Layout](#repository-layout)
- [Documentation](#documentation)
- [License](#license)

## Install And Load The Current Testnet

Use the latest operator bundle when you want to run ZenoDEX locally without
cloning the full repository. It starts the DEX UI, ZenoLedger local nodes, a
local Tau test node, Zeno Oracle, and the stdlib API on your machine.

Prerequisites: Docker Desktop or Docker Engine with compose v2, Python 3.11+,
and Chrome or Chromium if you want browser smoke checks.

Download, verify, and extract the current release:

```bash
ZENODEX_VERSION=0.1.22

curl -L -o "zenodex-operator-${ZENODEX_VERSION}.tar.gz" \
  "https://github.com/TheDarkLightX/ZenoDEX/releases/download/v${ZENODEX_VERSION}/zenodex-operator-${ZENODEX_VERSION}.tar.gz"
curl -L -o SHA256SUMS \
  "https://github.com/TheDarkLightX/ZenoDEX/releases/download/v${ZENODEX_VERSION}/SHA256SUMS"

sha256sum -c --ignore-missing SHA256SUMS

tar -xzf "zenodex-operator-${ZENODEX_VERSION}.tar.gz"
cd "zenodex-operator-${ZENODEX_VERSION}"
```

Clone the Tau local-testnet dependency. Tau is fetched by the tester and is not
redistributed inside the ZenoDEX operator bundle.

```bash
mkdir -p external
git clone https://github.com/IDNI/tau-testnet.git external/tau-testnet
```

Start and load the local testnet:

```bash
python3 tools/zenoctl.py testnet local up \
  --out-dir ./local-testnet \
  --engine docker \
  --ui-port 18081 \
  --health-timeout 240
```

Open the UI:

```text
http://127.0.0.1:18081
```

Run the live feature check:

```bash
python3 tools/zenoctl.py testnet local smoke \
  --out-dir ./local-testnet \
  --engine docker \
  --browser auto
```

Stop the stack while preserving local state:

```bash
python3 tools/zenoctl.py testnet local down \
  --out-dir ./local-testnet \
  --engine docker
```

The local stack exposes only a loopback nginx port by default. The browser uses
relative `/api/*` calls; nginx injects backend tokens server-side.

Native launcher track: release builds now include a Linux `zenodex` launcher,
and CI builds Linux, macOS, and Windows launcher artifacts. The launcher is the
future one-command path:

```bash
zenodex local-testnet up
```

It supplies a default local state directory, checks prerequisites, can fetch the
pinned Tau local-testnet dependency, and delegates to the existing checked
`zenoctl.py` orchestration. See
[docs/NATIVE_INSTALLER_PLAN.md](docs/NATIVE_INSTALLER_PLAN.md).

Latest release page:
[github.com/TheDarkLightX/ZenoDEX/releases/tag/v0.1.22](https://github.com/TheDarkLightX/ZenoDEX/releases/tag/v0.1.22).
Full local-testnet details:
[docs/LOCAL_TESTNET_QUICKSTART.md](docs/LOCAL_TESTNET_QUICKSTART.md).

## Why The Name ZenoDEX?

Zeno of Elea posed paradoxes about motion and division. In the Dichotomy
paradox, reaching a goal requires first going halfway, then halfway through
the remaining distance, then halfway again. Modern mathematics resolves this
with limits; a countably infinite sequence of shrinking steps sums to a finite
total.

The analogy applies directly to tokenomics and protocol accounting. A supply
schedule can approach a floor forever without crossing it:

```text
S_{n+1} = F + r(S_n - F)
```

Where:

```text
S_n = total supply after step n
F   = supply floor
r   = remaining fraction per step, with 0 < r < 1
```

The closed form is:

```text
S_n = F + r^n(S_0 - F)
```

For every finite `n`, `S_n > F`, while `S_n` approaches `F` as `n` grows. The
total burn remains bounded:

```text
S_0 - S_n = (1 - r^n)(S_0 - F) <= S_0 - F
```

Steps can be unbounded while the cumulative burn stays finite. That is the
core Zeno analogy.

Real ledgers add an integer constraint. A token may be displayed with
decimals; committed balances are integer base units. Once an ideal real-valued
change falls below one base unit, the protocol must define a deterministic
dust policy.

ZenoDEX therefore uses:

- integer base units
- explicit supply floors
- deterministic rounding
- explicit dust accounting
- bounded arithmetic proofs

For protocol tokens and LP shares, the practical target is `18` base-unit
decimals plus explicit dust accounting. If an ideal transfer is `T*` and the
ledger rounds down to `t` base units at decimal scale `d`, the rounding error is
bounded by one base unit:

```text
0 <= T* - t / 10^d < 10^(-d)
```

Convergent tokenomics stay deterministic on real ledgers. The protocol
approaches a floor without floating point arithmetic, implicit precision
upgrades, or ambiguous rounding.

## Current Status

```text
public-testnet candidate
high-assurance functional core
Tau Net handoff adapter available
production mainnet readiness gated by validator-network hardening and live-value deployment
```

## Assurance Snapshot

<!-- BEGIN GENERATED:ASSURANCE_RELEASE_SNAPSHOT -->
The pinned release replay for the release tree dated `2026-04-06` was green:

- acceptance TCB: `385 passed`, `98.8%` branch coverage
- critical gate: `1424 passed`, `99%` branch coverage
- release gate: `passed end to end`
- mutation gate: `5 killed, 2 inconclusive`
- fuzz gate: `58 passed`
- snapshot recovery: `17 passed`
- Tau syntax: `60/60`
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

## Design Principles

**Invalid states must be unrepresentable. Correct-by-construction design
eliminates bad states at the type level; tests confirm the behavior that
remains.**

## Core Features

### High-Assurance Core

ZenoDEX keeps consensus-critical logic small, deterministic, and replayable.
The core avoids floating point arithmetic, uses canonical serialization, and
commits state through reproducible roots. Complementary evidence includes Lean
proofs, Tau specs, ESSO kernels, property tests, replay receipts, fuzzing, and
adversarial simulations. ZenoLedger v0 provides the replayable testnet layer
that makes this evidence independently verifiable across machines.

Proof-backed and evidence-backed areas include:

- CPMM integer arithmetic and invariant checks
- canonical ordering and candidate selection surfaces
- settlement replay validation
- **Zeno Oracle:** freshness checks, reporter lifecycle replay,
  token-settlement replay, and fail-closed malformed-input handling
- zUSD collateral and redemption math
- perps funding and margin boundaries
- **ZenoProof:** evidence registry and verifier checks
- FIRE settlement receipts, verifier rules, and budget-safety claims
- Certified Financial Math Object payoff, collateral, and fixed-point bridges
- **ZenoLedger:** headers, checkpoints, watcher attestations, mirror roots, and
  Tau handoff packets

This is a high-assurance public-testnet candidate. It exceeds conventional
prototype rigor. Production value deployment still requires operational
hardening and fresh release evidence.

### Batch Clearing And Mechanism Design

Continuous markets force a latency race over ordering, observation time, and
inclusion. ZenoDEX moves key surfaces to deterministic batch mechanisms.

Uniform Price Batch Auction (UPBA) is the target clearing architecture for
reducing intra-batch ordering games. Under true uniform clearing, execution
depends on the admitted order multiset and the clearing certificate, instead
of an arbitrary sequence of individual swaps.

The current UPBA work is scoped:

```text
aggregate orders
compute or propose a uniform clearing result
verify certificate conditions deterministically
commit accepted result through ZenoLedger feature suites
```

UPBA reduces intra-batch ordering MEV. By itself it does not address
inclusion/exclusion games, batch-boundary timing, oracle timing, censorship,
or cross-domain latency; those surfaces are modeled separately.

The solver incentive model has a checked local payoff theorem. When the bounty
exceeds compute cost, the slash penalty is positive, and the verifier always
catches invalid submissions, honest solving strictly dominates idling or
submitting a bad solution. The bound is conditional on those assumptions and
does not claim that every production actor game is solved.

### ZenoEnergy Advisory Ranking Research

ZenoEnergy is an isolated research scorer for UPBA v2 candidate search. A
small energy/ranking model orders candidate settlements before deterministic
verification. The verifier remains the settlement authority:

```text
Model proposes; verifier decides.
```

**Headline result on bounded synthetic data.** The preferred 97-parameter
gap-weighted ranker reaches 100% top-10 recall on committed holdout and
cross-seed synthetic receipts, reduces mean verifier-winner position versus
hand energy, and records zero invalid accepts. Learned and hybrid orderings
average 1.008 verifier calls on the bounded synthetic run and 1.013 verifier
calls across a 3-seed by 3-candidate-count stress grid. The multi-family
adversarial suffix stress extends this to 944 verifier-invalid cases across 8
invalidity families with zero invalid accepts.

**Recent surfaces.** A runtime dominance-cover certificate prototype and a WES
bridge rank dominance-cover checker work while deterministic UPBA verification
remains authoritative. A dominance-prefix audit shows current learned and
hybrid rankers reaching a finite-list dominance-cover certificate after the
first checked candidate on the committed bounded run. The suffix-bound
early-stop certificate adds a deterministic unchecked-suffix objective bound;
declared-output-only bounds fail on injected high-output invalid suffixes,
while deterministic disqualifiers preserve the certificate.

**Curriculum and data.** A Julia negative-curriculum lane converts hard
negatives into sampling weights and a bounded epiplexity proxy so training can
prioritize rare deterministic disqualifiers while preserving verifier
authority. The first bounded rare-disqualifier curriculum ranker did not beat
the gap-weighted default, so the default stays promoted for research. The
data-scaling probe shows raw same-generator synthetic volume helps from small
budgets but saturates below the current checkpoint. The quality-selection
probe sharpens this: winner-bearing hard-batch selection beats raw
winner-bearing sampling at medium budgets, while tiny hard-only budgets can
overfocus on rare current-model misses. The ensemble probe adds six-member
advisory energy ensembles and Borda-style rank disagreement; it preserves
top-10 recall and zero invalid accepts but does not beat the current
checkpoint on mean verifier calls, so ensemble disagreement stays diagnostic
rather than a promoted default. The best-model registry pins the preferred
UPBA checkpoint and the three deterministically regenerated AutoTrader hard
synthetic models with sha256 hashes, so future experiments have stable
advisory baselines.

**Honest boundaries.**

- Production ranking remains gated by real or production-shadow replay.
- Ranking by low energy alone is not an optimality certificate (formal Lean
  counterexample at
  [docs/ZENO_ENERGY_ENERGY_ORDER_ALONE_FORMAL.md](docs/ZENO_ENERGY_ENERGY_ORDER_ALONE_FORMAL.md)).
- The epiplexity proxy can guide data selection only after heldout ranking
  metrics prove it helps.
- All of the above is bounded synthetic evidence. The replay tooling below
  cannot authorize settlement, change policy predicates, or turn synthetic
  fixtures into production evidence.

**Replay and promotion tooling.** The replay secret scanner catches obvious
key material before packaging. The source manifest builder packages real
replay reports with canonical hashes and secret-scan attestations. The replay
coverage profile checker rejects narrow real replay evidence before promotion.
The production evidence bundle then assembles source-manifested,
coverage-profiled UPBA and AutoTrader real replay reports and runs the
fail-closed advisory ranking promotion gate.

**References.**

- Model and results:
  [V0 spec](docs/ZENO_ENERGY_V0.md),
  [results](docs/ZENO_ENERGY_RESULTS.md),
  [paper](docs/papers/zenoenergy-v0/paper.md)
- Suffix bound:
  [main](docs/ZENO_ENERGY_SUFFIX_BOUND.md),
  [cross-seed](docs/ZENO_ENERGY_SUFFIX_BOUND_CROSS_SEED.md),
  [adversarial](docs/ZENO_ENERGY_SUFFIX_BOUND_ADVERSARIAL_STRESS.md),
  [family stress](docs/ZENO_ENERGY_SUFFIX_BOUND_ADVERSARIAL_FAMILY_STRESS.md)
- Dominance:
  [cover](docs/ZENO_ENERGY_DOMINANCE_COVER.md),
  [WES search](docs/ZENO_ENERGY_WES_DOMINANCE_SEARCH.md),
  [prefix audit](docs/ZENO_ENERGY_DOMINANCE_PREFIX.md)
- Curriculum and data:
  [negative curriculum](docs/ZENO_ENERGY_NEGATIVE_CURRICULUM.md),
  [curriculum ranker](docs/ZENO_ENERGY_CURRICULUM_RANKER.md),
  [data scaling](docs/ZENO_ENERGY_DATA_SCALING.md),
  [quality selection](docs/ZENO_ENERGY_QUALITY_SELECTION.md),
  [ensemble](docs/ZENO_ENERGY_ENSEMBLE.md),
  [best models](docs/ZENO_ENERGY_BEST_MODELS.md)
- Formal and theoretical:
  [energy-order-alone Lean counterexample](docs/ZENO_ENERGY_ENERGY_ORDER_ALONE_FORMAL.md),
  [epiplexity literature note](docs/ZENO_ENERGY_EPIPLEXITY_LITERATURE.md)
- Production gate and replay:
  [gate](docs/ZENO_ENERGY_PRODUCTION_GATE.md),
  [secret scan](docs/ZENO_ENERGY_REPLAY_SECRET_SCAN.md),
  [source manifest](docs/ZENO_ENERGY_REPLAY_SOURCE_MANIFEST_BUILDER.md),
  [coverage profile](docs/ZENO_ENERGY_REPLAY_COVERAGE_PROFILE.md),
  [evidence bundle](docs/ZENO_ENERGY_PRODUCTION_EVIDENCE_BUNDLE.md)

### ZenoProof, FIRE, And Certified Financial Math Objects

ZenoProof is the internal evidence registry and verifier layer. Its public
role is to connect checked evidence to replayable claims and verifier gates.
Mechanism details are intentionally kept out of the public README until the
release scope is finalized.

FIRE is the internal framework for turning financial mechanisms into checked
object packages: templates, instances, certificates, verifier receipts, replay
receipts, and settlement-authority predicates. FIRE proposals are
non-authoritative until they compile into accepted artifacts and pass the
FIRE verifier.

Certified Financial Math Objects are the financial instruments that FIRE is
meant to package. A live object should specify:

```text
formula + units + bounds + state transition + oracle policy
+ collateral rule + proof/certificate
```

The point is bounded liability, replayable settlement, and clear evidence
labels. A certified object may still be economically unwise or unprofitable;
the certification claim is about mechanical invariants such as payoff bounds,
collateral sufficiency, fixed-point rounding buffers, conservation, and
settlement replay.

## Features

- **Spot DEX:** deterministic CPMM execution, LP accounting, settlement replay,
  and state-root commitments.
- **UPBA:** uniform-clearing research with testnet feature-suite coverage for
  aggregate batch-auction verification.
- **ZUSD:** overcollateralized stablecoin mechanics, redemption, and
  collateral-ratio analysis.
- **Perpetuals:** epoch-based funding, margin checks, insurance boundaries, and
  liquidation research.
- **ZenoOracle:** freshness checks, reporter lifecycle replay, token-settlement
  replay, and fail-closed handling of malformed input.
- **ZenoProof:** evidence registry and verifier layer for replayable assurance
  claims. Mechanism details are intentionally withheld from the public README
  until release.
- **FIRE:** internal object pipeline with verifier receipts, proof-tree
  certificates, budget-safety checks, and replay gates for promoted financial
  mechanisms.
- **Certified Financial Math Objects:** formula-bound financial instruments
  with explicit units, payoff bounds, collateral rules, oracle policy, and
  proof or certificate bundles.
- **Confidential Extensions:** TEE-first confidential admission with experimental
  FHE sealed-bid verification surfaces.
- **Autotrader Policy Surface:** local deterministic controller checks over
  quote receipts, cadence, budgets, and rejected actions.
- **ZenoLedger:** replayable public-testnet candidate with watcher attestations,
  mirror roots, status roots, and Tau handoff.

## Quick Start

### Run A Real Local ZenoDEX Testnet

This is the recommended path for testers who want to exercise ZenoDEX locally
against live local nodes. It starts a Docker compose stack with ZenoLedger
writer/forwarder/read-only nodes, a local Tau test node, Zeno Oracle, the
stdlib API, nginx, and the DEX UI.

Prerequisites:

- Docker Desktop or Docker Engine with compose v2.
- Python 3.11+.
- Chrome or Chromium only if you want browser smoke checks.

Download, verify, and extract the current operator bundle:

```bash
ZENODEX_VERSION=0.1.22

curl -L -o "zenodex-operator-${ZENODEX_VERSION}.tar.gz" \
  "https://github.com/TheDarkLightX/ZenoDEX/releases/download/v${ZENODEX_VERSION}/zenodex-operator-${ZENODEX_VERSION}.tar.gz"
curl -L -o SHA256SUMS \
  "https://github.com/TheDarkLightX/ZenoDEX/releases/download/v${ZENODEX_VERSION}/SHA256SUMS"

sha256sum -c --ignore-missing SHA256SUMS

tar -xzf "zenodex-operator-${ZENODEX_VERSION}.tar.gz"
cd "zenodex-operator-${ZENODEX_VERSION}"
```

Clone the Tau local-testnet dependency. Tau is fetched by the tester and is
not redistributed inside the ZenoDEX bundle:

```bash
mkdir -p external
git clone https://github.com/IDNI/tau-testnet.git external/tau-testnet
```

Start the local multi-node testnet:

```bash
python3 tools/zenoctl.py testnet local up \
  --out-dir ./local-testnet \
  --engine docker \
  --ui-port 18081 \
  --health-timeout 240
```

Open the UI:

```text
http://127.0.0.1:18081
```

Run live feature checks:

```bash
python3 tools/zenoctl.py testnet local smoke \
  --out-dir ./local-testnet \
  --engine docker \
  --browser auto
```

Stop the stack while preserving state:

```bash
python3 tools/zenoctl.py testnet local down \
  --out-dir ./local-testnet \
  --engine docker
```

Fully reset the local chain, fixtures, and volumes:

```bash
python3 tools/zenoctl.py testnet local reset \
  --out-dir ./local-testnet \
  --engine docker \
  --force
```

Details and troubleshooting: [docs/LOCAL_TESTNET_QUICKSTART.md](docs/LOCAL_TESTNET_QUICKSTART.md).

### Developer Setup

Install Python dependencies:

```bash
python3 -m pip install --require-hashes -r requirements-dev.lock.txt
```

Production/container runtime installs use the smaller runtime lock:

```bash
python3 -m pip install --require-hashes -r requirements-core.lock.txt
```

Clone optional Tau dependencies under `external/`:

```bash
mkdir -p external
cd external
git clone https://github.com/IDNI/tau-lang.git
git clone https://github.com/IDNI/tau-testnet.git
cd ..
```

Run the local API and UI:

```bash
DEX_API_ENABLED=true ZENODEX_API_BEARER_TOKEN=sekret \
  python3 -m src.integration.api_server

cd tools/dex-ui
npm install
VITE_DEMO_MODE=false VITE_API_TOKEN=sekret \
  npm run dev -- --host 127.0.0.1 --port 5173
```

When a `zenoctl testnet local up` stack is running, the Vite dev server
auto-detects its loopback nginx port for `/api/*`. Set `API_PROXY_TARGET`
explicitly when you are wiring the UI to a manually started API server.

Run the broad Python test suite:

```bash
pytest tests/
```

Run Lean proofs:

```bash
cd lean-mathlib
lake build
```

Run the ZenoLedger public-testnet candidate builder:

```bash
python3 tools/zeno_ledger_make_public_testnet_bundle.py \
  --out-dir /tmp/zeno-ledger-public-testnet \
  --network-id zeno-ledger-devnet-0 \
  --chain-id zeno-ledger-devnet-0
```

## ZenoLedger Node Operations

Before starting a node, run the lightweight local preflight. These commands do
not need external network access and catch the common setup mistakes before an
operator opens ports or mirrors a bundle:

```bash
python3 tools/zeno_ledger_node.py --help
python3 tools/permissionless_assurance.py status
python3 tools/check_tau_supported_runtime_subset.py
pytest -q tests/tau/test_tau_spec_assurance.py
```

For a same-machine network rehearsal, run:

```bash
python3 tools/zeno_ledger_public_network_smoke.py \
  --out-dir /tmp/zeno-ledger-public-network-smoke \
  --network-id zeno-ledger-devnet-0 \
  --chain-id zeno-ledger-devnet-0
```

The node entrypoint wraps the same bundle and replay logic. Use it to build a
bootstrap bundle, run a follower/watcher node, and optionally serve node status
over HTTP:

```bash
python3 tools/zeno_ledger_node.py bootstrap \
  --out-dir /tmp/zeno-ledger-public-testnet \
  --network-id zeno-ledger-devnet-0 \
  --chain-id zeno-ledger-devnet-0 \
  --token-symbol tZENO

python3 tools/zeno_ledger_node.py sync \
  --base-url https://example.test/zeno-ledger-public-testnet/ \
  --out-dir /tmp/zeno-ledger-public-testnet-synced

python3 tools/zeno_ledger_node.py write-network-config \
  --bundle-root /tmp/zeno-ledger-public-testnet \
  --mirror-base-url https://example.test/zeno-ledger-public-testnet/ \
  --writer-url https://example.test:8787 \
  --out /tmp/zeno-ledger-public-testnet/public_network_config.json

python3 tools/zeno_ledger_node.py join-network \
  --config-url https://example.test/zeno-ledger-public-testnet/public_network_config.json \
  --node-id operator-b \
  --bundle-root /tmp/zeno-ledger-public-testnet-synced \
  --data-dir /tmp/zeno-ledger-node-b \
  --serve
```

The same public-testnet publish and join paths are available through the
operator wrapper:

```bash
python3 tools/zenoctl.py testnet publish-config \
  --bundle-root /tmp/zeno-ledger-public-testnet \
  --mirror-base-url https://example.test/zeno-ledger-public-testnet/ \
  --writer-url https://example.test:8787 \
  --out /tmp/zeno-ledger-public-testnet/public_network_config.json

python3 tools/zenoctl.py testnet join \
  --config-url https://example.test/zeno-ledger-public-testnet/public_network_config.json \
  --node-id operator-b \
  --serve
```

For a remote operator, use a join config to combine sync, replay, peer checking,
and serving when a public network config has not been published:

```bash
cat > /tmp/zeno-ledger-node-b.json <<'JSON'
{
  "schema": "zenodex.zeno_ledger.node_join_config.v0",
  "base_url": "https://example.test/zeno-ledger-public-testnet/",
  "bundle_root": "/tmp/zeno-ledger-public-testnet-synced",
  "node_id": "operator-b",
  "data_dir": "/tmp/zeno-ledger-node-b",
  "peer_urls": ["http://127.0.0.1:8787"],
  "serve": true,
  "host": "0.0.0.0",
  "port": 8788,
  "poll_seconds": 5,
  "enable_testnet_intake": true,
  "enable_testnet_faucet": true,
  "submit_peer_url": "http://127.0.0.1:8787"
}
JSON

python3 tools/zeno_ledger_node.py join \
  --config /tmp/zeno-ledger-node-b.json
```

The lower-level run command is still available when an operator wants to manage
each step manually:

```bash
python3 tools/zeno_ledger_node.py run \
  --bundle-root /tmp/zeno-ledger-public-testnet-synced \
  --node-id operator-a \
  --data-dir /tmp/zeno-ledger-node-a \
  --peer-watcher-attestation \
    /tmp/zeno-ledger-public-testnet-synced/bootstrap/watcher_attestations/bootstrap_range_1_5.json \
  --serve \
  --host 127.0.0.1 \
  --port 8787
```

ZenoLedger also has opt-in Risc0 proof-of-execution coverage for the current
ZenoDEX spot v1 guest subset. The real-proof smoke builds the guest with
`RISC0_FORCE_BUILD=1`, generates non-empty receipts, and verifies them through
the host CLI for an empty transition, faucet mint, create-pool, and
swap-exact-in. The receipt journal binds the state hash, transaction
commitment, pre-app hash, post-app hash, and block timestamp.

This is current local evidence for the restricted guest path. It does not yet
prove the full Python ZenoDEX runtime, multi-intent batches, exact-out,
multi-hop routing, production prover performance, or validator-network
readiness.

After the node has verified its bootstrap bundle, a local operator can append
testnet DEX transactions into the node-local live ledger:

```bash
python3 tools/zeno_ledger_node.py append \
  --data-dir /tmp/zeno-ledger-node-a \
  --tx /path/to/testnet_tx.json \
  --time-ms 1778731000000

python3 tools/zeno_ledger_node.py pull-live \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url http://127.0.0.1:8787

python3 tools/zeno_ledger_node.py check-peers \
  --data-dir /tmp/zeno-ledger-node-b \
  --peer-url http://127.0.0.1:8787

python3 tools/zeno_ledger_node.py serve \
  --data-dir /tmp/zeno-ledger-node-b \
  --host 127.0.0.1 \
  --port 8788 \
  --peer-url http://127.0.0.1:8787 \
  --poll-seconds 5 \
  --submit-peer-url http://127.0.0.1:8787 \
  --enable-testnet-intake \
  --enable-testnet-faucet

python3 tools/zeno_ledger_node.py faucet \
  --data-dir /tmp/zeno-ledger-node-a \
  --to-pubkey 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \
  --asset 0x1111111111111111111111111111111111111111111111111111111111111111 \
  --amount 100000
```

This is the first public-node layer for ZenoLedger. The node bootstraps from a
bundle, verifies the ledger, emits a watcher attestation, and serves
`/health`, `/status`, `/features`, `/tokens`, `/network`, `/live`,
`/attestation`, and `/testnet-status`.

The `sync` command downloads only indexed JSON artifacts from a public HTTP
mirror and verifies every mirror hash before the node runs.

The public bundle ships a deterministic test-token catalog (`tZENO`, `tASSET0`,
and `tASSET1`) plus testnet-only faucet behavior for feature testing. The
faucet accepts canonical 32-byte test asset IDs, so operators can mint
throwaway assets for live test pools without touching release token policy.

Latest local shipment metadata is in
[`docs/LATEST_TESTNET_CHECKPOINT.md`](docs/LATEST_TESTNET_CHECKPOINT.md). The
current checkpoint builds the static DEX UI, executes the public-testnet
feature-suite bundle, and verifies the operator archive manifest before
sharing.

The `append` command writes post-bootstrap testnet DEX blocks under the node
data directory. The `pull-live` command fetches live block bodies from a peer
and accepts them only after local deterministic replay produces the same
header. A served node can also poll peer URLs with `--peer-url` and
`--poll-seconds`.

Testnet HTTP intake is disabled by default. `--enable-testnet-intake` opens
`POST /tx`, and `--enable-testnet-faucet` opens `POST /faucet` for bounded
fake-token minting. A follower can expose `POST /tx` and `POST /faucet` while
forwarding submissions to a designated writer with `--submit-peer-url`, then
follow the resulting live blocks by deterministic replay.

The `join` command wraps sync, replay, watcher attestation, optional peer
check, and optional serving into one JSON-configured operator flow. The
`check-peers` command compares network ID, chain ID, feature-suite hash, peer
height, and the common header hash before an operator trusts a peer. The
`write-network-config` and `join-network` commands let any operator join from
one published URL.

Live P2P block gossip and validator scheduling remain future network work.

## Public Testnet Direction

The next release target is a public-testnet v0 where the 3-node
multi-machine rehearsal graduates into an operator-facing network:

```text
seed operator publishes public_network_config.json
-> outside operators join from one URL
-> followers verify and replay before serving status or forwarding testnet txs
-> phones and browsers connect as clients or verify checkpoint bundles
```

The target is documented in
[docs/PUBLIC_TESTNET_V0_1_16_PLAN.md](docs/PUBLIC_TESTNET_V0_1_16_PLAN.md).
The first public testnet can keep one designated writer while opening node
launch and deterministic replay to outside operators. Rotating validators,
open P2P gossip, and production value remain later milestones.

Run the same-machine dual-operator rehearsal before copying to another
computer. The two-machine operator runbook is
`docs/ZENO_LEDGER_TWO_MACHINE_TESTNET.md`.

```bash
python3 tools/zeno_ledger_public_network_smoke.py \
  --out-dir /tmp/zeno-ledger-public-network-smoke \
  --network-id zeno-ledger-devnet-0 \
  --chain-id zeno-ledger-devnet-0

python3 tools/zeno_ledger_dual_operator_rehearsal.py \
  --out-dir /tmp/zeno-ledger-dual-operator \
  --network-id zeno-ledger-devnet-0 \
  --chain-id zeno-ledger-devnet-0
```

This builds two independent public-testnet bundles, checks their hashes match,
copies one bundle into a second operator directory, replays it, and emits a
combined two-watcher status report.

Run the copied-bundle rehearsal on a second machine:

```bash
python3 tools/zeno_ledger_operator_rehearsal.py \
  --bundle-root /path/to/copied/zeno-ledger-public-testnet \
  --operator-id operator-b \
  --out-dir /tmp/zeno-ledger-operator-b \
  --peer-watcher-attestation \
    /path/to/copied/zeno-ledger-public-testnet/bootstrap/watcher_attestations/bootstrap_range_1_5.json
```

The rehearsal succeeds when the second machine emits `ok=true`, an
`operator_attestation_hash`, and a `combined_testnet_status_hash` with
`combined_watcher_count=2`.

## Repository Layout

- `src/core/`: deterministic DEX, AMM, zUSD, perps, oracle, and confidential
  extension logic
- `src/state/`: state tables, state-root helpers, and canonical commitments
- `src/integration/`: API server, ZenoLedger, Tau handoff, snapshots, and
  verification adapters
- `src/kernels/`: generated/reference kernels and verified state machines
- `src/tau_specs/`: Tau Language policy specs
- `lean-mathlib/Proofs/`: Lean proof artifacts
- `zk/zrpf_risc0/`: bounded ZRPF structural proof and retained-replay profile
- `tools/`: operational scripts, replay helpers, feature-suite builders, and UI
- `docs/`: public specs, architecture notes, and release evidence
- `tests/`: unit, integration, replay, and assurance tests
- `experimental/` and `knowledge/`: discovery artifacts, simulations, and
  negative-knowledge records

## Documentation

- `docs/SPECIFICATION.md`
- `docs/ALGORITHMS.md`
- `docs/FIRE_MANIFESTO.md`
- `docs/derivatives/CERTIFIED_FINANCIAL_MATH_OBJECTS.md`
- `docs/TAU_ARCHITECTURE.md`
- `docs/TAU_LANGUAGE_CONSTRAINTS.md`
- `docs/ASSURANCE_RELEASE_SNAPSHOT.md`
- `docs/DISASTER_HARDNESS_ASSURANCE_METRIC.md`
- `docs/research/ZRPF_V3_CORRECT_BY_CONSTRUCTION_SPEC_20260710.md`
- `zk/zrpf_risc0/README.md`

## License

TBD
