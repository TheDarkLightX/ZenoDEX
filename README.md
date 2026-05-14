# ZenoDEX

ZenoDEX is a high-assurance, production-candidate decentralized autonomous
exchange for Tau Network. It uses a hybrid model: deterministic Python computes
operational state, while Tau Language specs, ESSO kernels, Lean proofs, and
replayable certificates check the safety boundaries around settlement.

This README is the front door. Detailed assurance evidence lives in the linked
docs, proof files, kernels, and replay scripts.

Current status:

```text
public-testnet candidate
high-assurance functional core
Tau Net handoff adapter available
production mainnet readiness gated by validator-network hardening and live-value deployment
```

ZenoLedger v0 runs ZenoDEX feature suites through a replayable mirror/watcher
workflow: independent machines rebuild the same headers, checkpoints,
feature-suite reports, watcher attestations, and status roots. A production
validator network, P2P availability layer, and live-value deployment are
separate release work.

**Invalid states must be unrepresentable. Correct-by-construction design
eliminates bad states at the type level; tests confirm the behavior that
remains.**

## Core Ideas

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
- oracle freshness and reporter lifecycle checks
- zUSD collateral and redemption math
- perps funding and margin boundaries
- ZenoProof evidence registry and verifier checks
- FIRE settlement receipts, verifier rules, and budget-safety claims
- Certified Financial Math Object payoff, collateral, and fixed-point bridges
- ZenoLedger headers, checkpoints, watcher attestations, mirror roots, and Tau
  handoff packets

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

### ZenoProof, FIRE, And Certified Financial Math Objects

ZenoProof is the internal evidence registry and verifier layer. Its public
role is to connect checked evidence to replayable claims and verifier gates.
Mechanism details are intentionally kept out of the public README until the
release surface is finalized.

FIRE is the internal framework for turning financial mechanisms into checked
object packages: templates, instances, certificates, verifier receipts, replay
receipts, and settlement-authority predicates. FIRE proposals are
non-authoritative until they compile into accepted artifacts and pass the
FIRE verifier surface.

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

## Quick Start

Install Python dependencies:

```bash
pip install -r requirements.txt
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
PERPS_API_ENABLED=true ZUSD_API_ENABLED=true DEMO_API_TOKEN=sekret \
  python3 -m src.integration.api_server

cd tools/dex-ui
npm install
VITE_DEMO_MODE=false API_PROXY_TARGET=http://127.0.0.1:8000 \
  VITE_API_TOKEN=sekret npm run dev -- --host 127.0.0.1 --port 5173
```

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

## License

TBD
