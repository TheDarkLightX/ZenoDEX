# ZenoDEX

ZenoDEX is a high-assurance decentralized exchange and token-economics stack
targeting Tau Net. The preferred release path is Tau Net because Tau Language
can express policy, governance, and protocol constraints directly. ZenoLedger
v0 gives the project an independent replayable testnet path while Tau Net
integration matures.

Current status:

```text
public-testnet candidate
high-assurance functional core
Tau Net handoff adapter available
production mainnet readiness still gated by public operations hardening
```

ZenoLedger v0 can run ZenoDEX feature suites through a replayable
mirror/watcher workflow. Independent machines can rebuild the same headers,
checkpoints, feature-suite reports, watcher attestations, and status roots.
This is decentralized replay and verification. A production validator network,
peer-to-peer availability layer, signer-governance process, and live value
deployment remain separate release work.

ZenoDEX uses one public product name. Older internal fixtures may still contain
legacy module identifiers for compatibility with historical test bodies. Public
documentation and user-facing surfaces should use `ZenoDEX`.

**Invalid states must be unrepresentable. Tests confirm behavior. CBC creates
the shape where bad states cannot be expressed.**

## Core Ideas

### High-Assurance Core

ZenoDEX keeps consensus-critical logic small, deterministic, and replayable.
The core avoids floating point arithmetic, uses canonical serialization, and
commits state through reproducible roots. Lean proofs, Tau specs, ESSO kernels,
property tests, replay receipts, fuzzing, and adversarial simulations are used
as complementary evidence.

Proof-backed and evidence-backed areas include:

- CPMM integer arithmetic and invariant checks
- canonical ordering and candidate selection surfaces
- settlement replay validation
- oracle freshness and reporter lifecycle checks
- zUSD collateral and redemption math
- perps funding and margin boundaries
- ZenoLedger headers, checkpoints, watcher attestations, mirror roots, and Tau
  handoff packets

The repository should be read as a high-assurance public-testnet candidate. It
is stronger than a conventional prototype, and production value deployment
still needs operational hardening and fresh release evidence.

### Batch Clearing And Mechanism Design

Continuous markets create an unsolvable latency race for participants competing
over ordering, observation time, and inclusion. ZenoDEX responds by moving key
surfaces toward deterministic batch mechanisms.

Uniform Price Batch Auction (UPBA) is the target clearing architecture for
reducing intra-batch ordering games. In a true uniform-clearing model,
execution depends on the admitted order multiset and the clearing certificate,
rather than on an arbitrary sequence of individual swaps.

The current UPBA work is scoped:

```text
aggregate orders
compute or propose a uniform clearing result
verify certificate conditions deterministically
commit accepted result through ZenoLedger feature suites
```

UPBA reduces intra-batch ordering MEV. It does not by itself solve
inclusion/exclusion games, batch-boundary timing, oracle timing, censorship, or
cross-domain latency. Those surfaces are modeled separately.

The solver incentive model has a checked local payoff theorem: if the bounty
exceeds compute cost, the slash penalty is positive, and invalid submissions are
always caught by the verifier, honest solving is strictly better than idling or
submitting a bad solution. That is a useful mechanism-design bound with explicit
assumptions, not a blanket claim that every production actor game is solved.

### ZenoLedger

ZenoLedger v0 is the liveness and replay layer for the public-testnet candidate.
It is designed to keep ZenoDEX testable while Tau Net integration is not ready
or if a Tau-side rule change blocks a ZenoDEX adapter.

ZenoLedger provides:

- independent local execution
- canonical headers, bodies, and checkpoints
- deterministic rejection receipts
- watcher attestations over verified ranges
- mirror indexes over published artifacts
- public testnet status roots
- feature-suite coverage reports
- Tau Net handoff packets

Build the current public-testnet candidate:

```bash
python3 tools/zeno_ledger_make_public_testnet_bundle.py \
  --out-dir /tmp/zeno-ledger-public-testnet \
  --network-id zeno-ledger-devnet-0 \
  --chain-id zeno-ledger-devnet-0
```

The generated launch manifest records:

```text
Tau release preference: Tau Net
current Tau mode: handoff adapter available
testnet liveness dependency: ZenoLedger
testnet token scope: zeno_ledger_testnet
release token scope: tau_net_exclusive
```

The core feature suite currently covers:

- spot bootstrap
- Tau app bridge spot path
- zUSD
- perps
- oracle freshness
- oracle reporter lifecycle and token-settlement replay
- UPBA
- proof mining
- autotrader policy surface
- confidential TEE/FHE alpha verifier surfaces

Latest focused ZenoLedger evidence from this workspace:

```text
pytest -q tests/integration/test_zeno_ledger_profile.py \
  tests/integration/test_zeno_ledger_v0.py \
  tests/integration/test_zeno_ledger_tau_export.py \
  tests/integration/test_zeno_ledger_verify_cli.py

80 passed in 393.97s
```

## Features

- **Spot DEX:** deterministic CPMM execution, LP accounting, settlement replay,
  and state-root commitments.
- **UPBA:** uniform-clearing research and testnet feature-suite coverage for
  aggregate batch-auction verification.
- **ZUSD:** overcollateralized stablecoin mechanics with redemption and
  collateral-ratio analysis.
- **Perpetuals:** epoch-based funding, margin checks, insurance boundaries, and
  liquidation research.
- **ZenoOracle:** oracle freshness checks, reporter lifecycle replay,
  token-settlement replay, and fail-closed malformed-input handling.
- **Confidential Extensions:** TEE-first confidential admission and experimental
  FHE sealed-bid verification surfaces.
- **Autotrader Policy Surface:** local deterministic controller checks around
  quote receipts, cadence, budgets, and rejected actions.
- **ZenoLedger:** replayable public-testnet candidate, watcher attestations,
  mirror roots, status roots, and Tau handoff.

## Why The Name ZenoDEX?

Zeno of Elea posed paradoxes about motion and division. In the Dichotomy
paradox, reaching a goal requires first going halfway, then halfway through the
remaining distance, then halfway again. Modern mathematics resolves this with
limits: a countably infinite sequence of shrinking steps can sum to a finite
total.

The analogy matters for tokenomics and protocol accounting. A supply schedule
can approach a floor forever without crossing it:

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

The number of steps can be unbounded while the total amount burned is finite.
That is the core Zeno analogy.

Real ledgers add an integer constraint. A token can be displayed with decimals,
but committed balances are integer base units. Once an ideal real-valued change
falls below one base unit, the protocol must define a deterministic dust policy.

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

This keeps convergent tokenomics deterministic on real ledgers. The protocol
can keep approaching a floor without floating point arithmetic, implicit
precision upgrades, or ambiguous rounding.

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
- `experimental/` and `knowledge/`: discovery, simulations, and negative
  knowledge artifacts

## Documentation

- `docs/SPECIFICATION.md`
- `docs/ALGORITHMS.md`
- `docs/TAU_ARCHITECTURE.md`
- `docs/TAU_LANGUAGE_CONSTRAINTS.md`
- `docs/ASSURANCE_RELEASE_SNAPSHOT.md`
- `docs/DISASTER_HARDNESS_ASSURANCE_METRIC.md`

## License

TBD
