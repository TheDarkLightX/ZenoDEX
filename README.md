<p align="center">
  <img src="assets/branding/zenodex/zenodex_full_transparent_1024.png" alt="ZenoDEX" width="360">
</p>

# ZenoDex

ZenoDex is a decentralized exchange (DEX) and token-economics stack for Tau Network. It uses a **hybrid model**: Python computes operational state, while **Tau Language specs validate invariants** and settlement rules.

## Pinned Release Snapshot

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

Replay commands are documented in [docs/PUBLIC_ASSURANCE_REPLAY.md](docs/PUBLIC_ASSURANCE_REPLAY.md).

## Stateful Witness Coverage

The stateful assurance lane is stronger than ordinary code-coverage reporting.
Code coverage says which branches ran. Witness coverage records that specific
dangerous semantic states were constructed, rejected, and kept as replayable
receipts.

The important check is not only whether a branch executed. It is whether
attack-shaped multi-step states such as stale settlement replay, repaired quote
drift, route canonicalization drift, and attestation time drift still fail
closed.

Current stateful snapshot for the deep lane as of `2026-04-08`:
- deep gate: `108 passed, 1 warning in 1135.88s`
- dangerous surfaces: `10/10 witnessed`
- reached-but-unwitnessed surfaces: `0`
- unique ranked witnesses: `18`
- hotspot count: `10`

These are not just ten concrete examples. The count is organized around
dangerous protocol surfaces and witness families: each witnessed surface can
cover many concrete action sequences, payload mutations, stale-state variants,
and boundary cases. The important assertion is that the selected high-risk
stateful families in the current release lane were reachable by the harness and
were rejected in replayable form.

This is not just a measurement of execution breadth. It is a replayable corpus
of dangerous reject states. If line coverage stayed high but one of the
critical witnesses disappeared, that would still be a serious regression.

More detail:
- [docs/PUBLIC_ASSURANCE_REPLAY.md](docs/PUBLIC_ASSURANCE_REPLAY.md)
- [docs/STATEFUL_DISASTER_STATE_WITNESSES.md](docs/STATEFUL_DISASTER_STATE_WITNESSES.md)
- [docs/STATEFUL_RELEASE_GUARDRAILS.md](docs/STATEFUL_RELEASE_GUARDRAILS.md)

## Current Assurance Shape

The public assurance case in this repo is organized as a shape, not as a single monolithic proof.

The review path is:

1. **Functional core**: the consensus-critical execution path stays small and deterministic.
   - examples: `src/core/split_routing_dispatch.py`, `src/core/batch_clearing.py`
2. **Verified kernel layer**: bounded arithmetic and contract surfaces are expressed as ESSO kernels.
   - examples: `src/kernels/dex/exact_*`, `src/kernels/dex/settlement_*`
3. **Replayable certificate layer**: Python build/verify packets bind runtime outputs to canonical witnesses.
   - examples: `src/integration/exact_in_route_certificate.py`
   - `src/integration/exact_out_route_certificate.py`
   - `src/integration/settlement_end_to_end_certificate_packet.py`
4. **Machine-checked proof layer**: Lean proofs justify the canonical winner and settlement packet shells.
   - examples: `lean-mathlib/Proofs/ZenoDEXExact*.lean`
   - `lean-mathlib/Proofs/ZenoDEXSettlement*.lean`
   - `lean-mathlib/Proofs/ZenoDEXUniqueCanonicalWinnerEverywhere.lean`
5. **Public regression layer**: focused core, integration, and formal tests keep the shipped surfaces replayable.

At the promoted bounded runtime scope shipped here, the current assurance shape supports these top-level claims:

- batch-clearing validity
- unique canonical winner for the shipped exact-in / exact-out routing lanes
- exact fee-aware accounting
- value-aware settlement safety
- proof-carrying optimizer certificates
- anti-fragmentation by theorem
- non-commutativity quarantine
- oracle divergence safety
- liquidation spiral containment
- cross-layer replay parity

This is the sense in which the repo argues for a **correct-by-construction** posture:

- objective and tie-break relations are explicit
- winner selection is reduced to replayable canonical witnesses
- settlement acceptance is bound to replayable end-to-end certificates
- functional-core edits are backed by kernels, proofs, or bounded trusted-model checks before adoption

Scope limit:

- this is a claim about the shipped, bounded, replayable surfaces in this tree
- it is not a claim that every future heuristic or every unbounded search family is already universally proved

## Disaster-State Coverage

The current checkout has a green bounded disaster-state replay receipt covering
`29` named disaster-state families. An axis is a scenario family, not one
concrete state; each family is backed by one or more replay commands that
exercise concrete inputs, sequences, boundary cases, or proof/certificate
artifacts.

```text
selected_axis_count = 29
unreachable_count = 29
failed_count = 0
inconclusive_count = 0
```

That is the current positive claim. A broader exploratory plan now names `125`
candidate what-if axes, but the public checkout does not justify a 125-axis
guarantee yet. The remaining `96` axes are still search inventory until their
commands are refreshed, their skipped external-tool lanes are split out, or
their checks are promoted into replayable proof/certificate lanes.

This is a bounded replay claim, not an exhaustive proof over all possible future
states. The detailed axis list, replay commands, interpretation, and residual
backlog are in [docs/DISASTER_STATE_COVERAGE.md](docs/DISASTER_STATE_COVERAGE.md).
The Lean proof receipt
[disaster_trace_lifting_v1.json](lean-mathlib/proof_receipts/disaster_trace_lifting_v1.json)
records the reusable theorem shape for turning a harness/barrier/simulation
certificate into a named unreachability claim. That proof strengthens how
promoted axes can be justified; it does not by itself raise the replayed
29-family count.

The proof layer has also been extended with reusable theorem schemas and
adapters:

- [AMMIntegerRuntimeBridge.lean](lean-mathlib/Proofs/AMMIntegerRuntimeBridge.lean)
  connects ideal CPMM quote facts to integer-runtime receipts, including
  no-overdelivery and bounded rounding envelopes.
- [DisasterAntichainBasis.lean](lean-mathlib/Proofs/DisasterAntichainBasis.lean)
  captures the pattern where a small rejected basis of forbidden traces rules
  out a larger bad trace family.
- [ForbiddenTraceMinor.lean](lean-mathlib/Proofs/ForbiddenTraceMinor.lean)
  captures the pattern where every bad trace embeds a forbidden motif, and
  motif rejection or guard blocking lifts through that embedding.
- [NoFreeResourceTraceLedger.lean](lean-mathlib/Proofs/NoFreeResourceTraceLedger.lean)
  captures the pattern where accepted traces cannot create protected resources
  outside the safe ledger cone, and budget claims cannot exceed total or prefix
  spend bounds.
- [ZenoDEXDisasterSchemaInstantiations.lean](lean-mathlib/Proofs/ZenoDEXDisasterSchemaInstantiations.lean)
  binds those schemas to small ZenoDEX-shaped budget and forbidden-motif
  adapters for future replay receipts.
- [CertificateGluing.lean](lean-mathlib/Proofs/CertificateGluing.lean)
  captures cross-surface consistency: if local certificates glue into one
  compatible global section, accepted bundles cannot also witness the named
  global bad state.

Those theorems make future disaster-state promotion cheaper and more rigorous,
but they remain schemas until instantiated against concrete quote, settlement,
oracle, signer, reward, and routing objects. The receipt is
[aristotle_runtime_disaster_gluing_2026-04-28.md](lean-mathlib/proof_receipts/aristotle_runtime_disaster_gluing_2026-04-28.md).
The forbidden-minor receipt is
[forbidden_trace_minor_2026-04-28.md](lean-mathlib/proof_receipts/forbidden_trace_minor_2026-04-28.md).
The no-free-resource receipt is
[no_free_resource_trace_ledger_2026-04-28.md](lean-mathlib/proof_receipts/no_free_resource_trace_ledger_2026-04-28.md).
The adapter receipt is
[zenodex_disaster_schema_instantiations_2026-04-28.md](lean-mathlib/proof_receipts/zenodex_disaster_schema_instantiations_2026-04-28.md).
The closed-axis proof-schema map is checked by
[check_disaster_proof_schema_map.py](tools/check_disaster_proof_schema_map.py)
and currently maps all `29` closed axes to one or more proof-schema lanes.
The Lean-side mirror is
[ZenoDEXClosedAxisProofSchemaMap.lean](lean-mathlib/Proofs/ZenoDEXClosedAxisProofSchemaMap.lean);
the checker also rejects drift between the Python map used by the replay
tooling and the Lean-side enumeration.

The closed receipt is CI-ratcheted by
`.github/workflows/disaster-assurance-ratchet.yml`: a main-branch change fails
if any pinned closed axis becomes failed, skipped, inconclusive, or missing from
the current search inventory. The same workflow also checks critical Lean proof
artifacts for active placeholders and keeps the deployment posture tests on the
default API/resource-safety boundary.

If you want to review that claim directly, start with:

- `src/core/split_routing_dispatch.py`
- `src/integration/exact_in_route_certificate.py`
- `src/integration/exact_out_route_certificate.py`
- `src/integration/settlement_end_to_end_certificate_packet.py`
- `tests/core/test_split_routing_dispatch.py`
- `tests/integration/test_api_server_dex_api.py`
- `lean-mathlib/Proofs/ZenoDEXUniqueCanonicalWinnerEverywhere.lean`

## Why this repo exists
- **Formal correctness** for DEX settlement and tokenomics
- **Composable spec modules** (lego blocks) with explicit invariants
- **DAC-style ecosystem design** for sustainable, sticky economics

## Why the name “ZenoDex” (Zeno, Cantor, and “never running out”)
Zeno of Elea (5th century BCE) posed paradoxes about motion and division (e.g., the **Dichotomy**: to reach a goal you
must first go halfway, then half the remainder, etc.). The modern resolution is the idea of a **limit**: a *countably
infinite* sequence of shrinking steps can sum to a finite total (a convergent series).

In the late 19th century, Georg Cantor made “infinity” precise by distinguishing **sizes of infinite sets** (a ladder of
infinities): for example, the integers are *countably infinite* (ℵ₀), while the real numbers are *uncountably infinite*.
Zeno-style processes live in the “countably many steps” world; you don’t need larger infinities to get “infinitely many
steps with finite total change”.

### The token-supply analogy (what is true, and what is not)
You can model a deflation schedule like Zeno’s paradox: burn a **fraction of what remains above a floor** each step.

Let:
- `S_n` = total supply after step `n`
- `F` = supply floor (minimum supply you never burn below)
- `0 < r < 1` = “remaining fraction” per step

Define:
```text
S_{n+1} = F + r (S_n - F)
```
Then:
```text
S_n = F + r^n (S_0 - F)
```
So for every finite `n`, `S_n > F`, but as `n → ∞`, `S_n → F`. This is the precise sense in which you can have
“never actually run out” (never hit the floor in finitely many steps) while allowing arbitrarily many deflation steps.

What you **cannot** get from this math is “infinite tokens burned”: the total burn is bounded:
```text
S_0 - S_n = (1 - r^n)(S_0 - F) ≤ (S_0 - F)
```
So the *number of steps* can be infinite, but the *total amount burned* is finite.

### Where “infinite deflationary pressure” can be meaningful (and where it’s wrong)
“Deflationary pressure reaches infinity” is **not** a well-typed statement unless you define a quantity that can
diverge. For example, a derived metric like `-log(S_n - F)` or `1/(S_n - F)` grows without bound as `S_n` approaches `F`,
even though the supply itself stays finite and above the floor.

In real implementations, supply is **discrete** (there is a smallest unit), so Zeno-style “infinite steps” becomes:
eventually the computed burn rounds to zero, or a guard prevents burning below a floor.

**Nuance: “moving decimals forever” is math, not ledger reality.** In pure mathematics you can always write smaller
positive numbers (`0.1, 0.01, 0.001, …`) and they never hit zero. But ledgers store amounts as **integers of a base
unit**, so there is always a minimum positive quantity.

- Bitcoin amounts are integers of **satoshis**: `1 sat = 0.00000001 BTC` (8 decimals). You cannot represent
  `0.000000001 BTC` on-chain without changing the protocol’s unit system.
- Second-layer systems can introduce finer units (e.g., Lightning “millisats”), but at any given settlement layer the
  precision is still finite.

For protocol design, this is a feature: it forces every burn/mint rule to define deterministic behavior once the “ideal”
real-valued burn becomes less than 1 base unit (round-to-zero, carry dust, or fail-closed below a floor). That’s exactly
how you avoid accidental full depletion due to rounding.

**Can we “just upgrade” to add more decimals forever?** You can upgrade *occasionally*, but it is not a free way to get
infinite precision:
- Changing *display decimals* is cosmetic; it doesn’t create finer on-ledger units.
- Getting finer units requires a **redenomination / split** (rescaling every balance, every reserve, every LP share
  supply, and every price/risk/oracle quantity that is denominated in the token). That is a protocol migration with real
  risk and coordination cost.
- Making this “algorithmic” turns it into a built-in **rebase/split mechanism**. That can be made deterministic, but it
  still imposes integration complexity and adds an attack surface at every rescale boundary.

The high-safety alternative is: choose a sufficiently fine base unit up front and use explicit **dust accounting**
(carry fractional remainders in a separate integer accumulator) so the economics can keep “approaching a floor” without
needing perpetual unit-system upgrades.

**recommendation**: choose `d = 18` base-unit decimals (i.e., `1 token = 10^18` base units) for protocol tokens and LP
shares, plus explicit dust accounting.

Mathematical reasons / formal logic behind this choice:
- **Representation**: amounts are integers `a ∈ ℕ` base units, interpreted as real token amounts `A = a / 10^d`.
- **Deterministic rounding error bound**: if an “ideal” real-valued transfer/burn is `T*`, any deterministic rounding to
  base units (e.g., `t = floor(T* · 10^d)`) introduces error strictly less than one base unit:
  ```text
  0 ≤ T* - t/10^d < 10^(-d)
  ```
- **Zeno-style “many steps before rounding to zero”**: for a geometric approach-to-floor with delta
  `D_n = S_n - F = r^n (S_0 - F)`, a non-zero change remains representable while `D_n ≥ 10^(-d)`. The number of steps
  until you *must* round to zero is approximately:
  ```text
  N ≈ log((S_0 - F) · 10^d) / log(1/r)
  ```
  For the common “halving the remainder” case (`r = 1/2`): `N ≈ log2((S_0 - F) · 10^d)`. With `(S_0 - F) ≈ 10^9` tokens
  and `d = 18`, that’s about `log2(10^27) ≈ 90` non-zero halvings; for gentler decay like `r = 0.99`, it’s on the order
  of thousands of non-zero steps.
- **Safety tradeoff (why not arbitrarily large `d`)**: increasing `d` increases granularity but also scales up every
  integer quantity, which can stress fixed-width integer backends and AMM multiplications. A practical `d` should be
  “large enough that rounding is negligible” and “small enough that arithmetic stays safe”; `18` is a widely-used
  compromise that typically satisfies both.

### Can this be expressed in Tau Language?
Mostly yes, but not as real-number “limits”, and not with naïve 256-bit arithmetic.

Tau is a **constraint/specification** language over streams. In practice (and in this repo) it is used to validate
relationships and safety properties using **bounded bitvectors** and Boolean logic. That has two consequences:

1) **Decimals are not a native concept** in Tau. The “18 decimals” choice is best modeled as:
   - a UI/display convention, and/or
   - a small *parameter* (e.g., `d = 18`) that governance can restrict,
   while the actual ledger values are **integers in base units**.

2) **Full-precision arithmetic is usually external.** Large-token amounts (e.g., `10^9` tokens at `d=18` ⇒ `10^27` base
   units) exceed small bitvector widths. So the standard pattern is:
   - Python (or the execution layer) computes big-int results (burn, fee, amount_out, updated balances),
   - Tau validates that the provided results satisfy conservation/bounds/ordering constraints (often using hi/lo limb
     witnesses). See `src/tau_specs/protocol_token_v1.tau`.

What Tau *can* express cleanly is the **discrete Zeno behavior** that actually matters on-ledger:
- burn rules using integer division (implicit floors) and explicit supply floors (see `src/tau_specs/token_v2_percentage.tau`)
- “never go below floor” and “no negative balance” invariants
- deterministic dust policies (“round-to-zero”, or “carry dust” as an extra state variable), provided the dust/state
  representation fits the chosen bitvector/limb encoding.

What Tau generally *won’t* express directly is “keep adding decimals forever”: changing base units is a **redenomination
/ split** (rescaling every balance/reserve/share) and is best treated as an explicit, governed migration step with its
own validation constraints (not an automatic background process).

## Public Design Rules (Risk-Reducing by Design)
These are the explicit design constraints we follow to reduce risk for everyone involved and keep the protocol predictable and transparent.
- **No investment framing**: we do not present the token as an investment or promote price appreciation.
- **Deterministic economics**: fee splits, burns, and rebates are rule-bound and non-discretionary.
- **Bounded parameters**: all adjustable rates and caps are constrained by hard limits.
- **Time-delayed governance**: changes are time-locked and publicly visible before activation.
- **No discretionary custody**: the protocol does not take custody via an operator-controlled wallet or allow arbitrary fund movement. Liquidity providers do deposit assets into pools, but funds move only by deterministic rules (mint/burn LP shares, swap pricing, withdrawals) rather than by a privileged custodian.
- **Clear separation of layers**: off-chain computation proposes values, Tau specs validate them.
- **No special access**: no privileged order flow, no hidden switches, no private liquidity advantages.

## Ecosystem Overview (How the Specs Connect)
The system is a **graph of validators** rather than a single monolithic spec. Each module validates one slice of behavior and emits an `ok` signal. A composite policy spec ANDs those signals, and settlement only proceeds when **all** modules pass.

**Flow (left to right):**
1. **Inputs & Oracles** provide prices, volume/risk signals, and user intents.
2. **Core DEX math specs** validate swaps and reserves (`cpmm_v1.tau`, `swap_exact_in_v1.tau`, `swap_exact_out_v1.tau`).
3. **Tokenomics modules** validate fee splits, buybacks, burns, rebates, and rewards (e.g., `tokenomics_fee_split_32_v1.tau`, `tokenomics_buyback_floor_32_v1.tau`).
4. **Token state validation** enforces transfer/mint/burn conservation (`protocol_token_v1.tau`).
5. **Governance & parameter registry** constrain how rates/caps/floors can change (`revision_policy_v1.tau`, `parameter_registry_v1.tau`, `governance_timelock_v1.tau`).
6. **Composite policy** gates the step: `dex_step_ok = AND(all_ok_flags)`.
7. **Settlement** applies the state transition only if the composite policy passes.

## Trust Model / Verification (How users know nodes are honest)
The goal is **don’t trust a computer, verify a transition**.

### What "formally guaranteed" means in this repo
ZenoDex treats specs as the source of truth.

- **Formal specification**: DEX-critical rules are encoded as executable Tau specs (swap, settlement rails, tokenomics gates).
- **Evidence that specs execute**: we run trace-level execution tests against production spec sets (not just parsing).
  - Trace harness: `tools/tau_trace_harness.py`
  - Production trace test: `tests/tau/test_production_tau_traces.py`
- **Multiple versions with explicit tradeoffs**: some checks are Tau-only (more trust-minimized, can be slower), while others are proof-gated (small Tau gate plus external verified computation).
  - Profiles and budgets: `docs/TAU_SPECS_PROFILES.md`
  - Machine-readable mapping: `src/tau_specs/recommended/spec_profiles.json`

### What "cryptographically guaranteed" means in this repo
Cryptography provides authenticity and tamper evidence. Verification can be:

- **By replay**: verify signed headers and recompute the committed hashes by re-executing.
- **By proof**: verify a succinct proof bound to the committed state.

In Tau Testnet Alpha, the main integrity anchors are:
- **Signed blocks (PoA)**: block signatures can be verified with BLS keys.
- **State commitments**: `header.state_hash` commits to rules text and an accounts snapshot hash, and may include an application `app_hash`.
- **Optional state proofs**: a DHT record `state_proof:<state_hash>` can carry a ZK proof of the DEX transition (opt-in, fail-closed). In this repo, "state proof" means a proof of correct state transition, not a Merkle inclusion proof.

### What “verified computation” looks like on Tau Testnet Alpha (today)
Tau Testnet Alpha (`external/tau-testnet`) is a hybrid system:
- A Python node handles networking/storage and “extralogical” work (e.g., signature verification).
- A Tau program (rules) is intended to be the arbiter of validity; it can be executed via Docker.
- **Important:** runtime Tau evaluation is currently gated by a dev switch (`TAU_FORCE_TEST`). When it is enabled, the node
  runs a deterministic test validator path instead of actually executing Tau rules.

The testnet provides integrity anchors a verifier can check:
- **Signed blocks (PoA)**: blocks can be signed/verified with BLS keys (authority model).
- **Commitments**: block headers include a transaction `merkle_root` and a `state_hash`. The `state_hash` commits to the
  rules text plus an accounts snapshot hash, and can also include an optional ZenoDex state snapshot hash.
- **Fetchable snapshots (best-effort)**: nodes can publish a JSON payload under `tau_state:<state_hash>` containing the
  rules text and the committed accounts hash (and optional DEX hash). This supports syncing and cross-checking against
  the block header commitment.

### What a user can do
- **Strongest (full verification)**: run your own node and re-verify every block/transition (rules + signatures +
  state-hash recomputation). If a proposer lies, your node rejects the block.
- **Medium (header + commitment verification)**: verify signed headers and compare `state_hash` across multiple
  independent nodes; optionally fetch the `tau_state:<state_hash>` payload and confirm it matches the header commitment.
- **Weakest**: trust a single RPC/provider.

### What we still need for “light client” verification
If you want a browser/phone client to verify correctness without replaying execution, you typically need a proof
mechanism (e.g., fraud proofs or zk validity proofs). Tau Testnet Alpha mainline offers **replicable verification and
state commitments**. This repo additionally proposes an opt-in, DHT-bound state proof mechanism:

- **State proofs (optional)**: publish a proof envelope to the DHT under `state_proof:<state_hash>` and fail-closed when enabled.
  - Protocol: `docs/tau_state_proof_v1.md`
  - Tau Testnet patch (local, PR-ready): `docs/tau_testnet_state_proof_patch.md`
  - Risc0 implementation for TauSwap transitions (v1 scope): `docs/tau_state_proof_risc0_tauswap_v1.md` and `zk/state_proof_risc0/`
  - Local demo (requires Rust + Risc0 toolchain): `TAU_STATE_PROOF_RISC0=1 bash tools/run_tau_testnet_local_smoke.sh`

## Spec Risk Profiles
ZenoDex organizes specs into **risk-based profiles** so communities can choose the level of exposure they are comfortable with.
- **Tier 1 (Recommended)**: lowest-risk, deterministic, bounded rules.
- **Tier 2 (Medium)**: more aggressive tokenomics and features.
- **Tier 3 (High)**: experimental or highly dynamic designs.

Start with the **Recommended** profile: `src/tau_specs/recommended/`.

Then review the full tier rationale in `src/tau_specs/RISK_TIERS.md`, and explore:
- `src/tau_specs/risk_medium/`
- `src/tau_specs/risk_high/`

## Repository Layout
- `src/`: core implementation
  - `src/core/` DEX math (CPMM, sealed-bid, confidential extensions)
  - `src/state/` state transitions
  - `src/agents/` agent workflows
  - `src/tau_specs/` Tau specifications (recommended / risk_medium / risk_high tiers)
  - `src/integration/` API server, testnet bridge, attestation layer
  - `src/kernels/` ESSO-verified kernels (DEX, Python, Rust targets)
  - `src/exotic_state_machines/` experimental ESSO state machines
- `tools/`: operational scripts and tooling
  - `tools/dex-ui/` Vite + React frontend SPA
- `docs/`: protocol/spec notes and ecosystem design
  - `docs/derivatives/` perpetuals and zUSD specifications
- `tests/`: test scripts and spec checks
- `external/`: Tau dependencies (git-ignored)

## Perpetuals and Derivatives
ZenoDEX includes an epoch-based perpetual futures system with the following components:

- **Epoch-based funding**: funding rates settle per epoch, not continuously
- **Insurance fund**: bounded drawdown with deterministic rebalancing
- **Circuit breaker**: halts trading on extreme price moves
- **zUSD**: synthetic stablecoin used as margin collateral
- **Poka-yoke order confirmation**: typed-confirm interlocks for large positions

Specifications:
- Epoch safety: `docs/derivatives/PERP_EPOCH_SAFETY_V1.md`
- Incentive design: `docs/derivatives/PERP_INCENTIVES_V1.md`
- SotA roadmap: `docs/derivatives/PERP_SOTA_ROADMAP.md`
- zUSD design: `docs/derivatives/ZUSD_V1.md`

The UI provides a full perpetuals trading interface with market selection, order form, position management, collateral controls, and trade history.

## Confidential Extensions and Sealed-Bid Auctions
- Plain-language explainer: `docs/CONFIDENTIAL_FEATURES_USE_CASES.md`
- Operator beta runbook: `docs/CONFIDENTIAL_FEATURES_BETA_RUNBOOK.md`
- Experimental FHE alpha: `docs/FHE_SEALED_BID_ALPHA.md`
- **TEE-first confidential extensions**: attested sidecars can meter private routing / risk logic without exposing source code.
  - Runtime receipts: `src/core/confidential_extension_receipts.py`
  - Attestation bridge: `src/integration/confidential_attestation.py`
  - ESSO gate: `src/kernels/dex/confidential_extension_tee_gate_v1.yaml`
- **Sealed-bid private-state lane**: bounded commit/reveal auction with deterministic uniform-price settlement.
  - Experiment core: `src/core/sealed_bid_auction.py`
  - ESSO gate: `src/kernels/dex/sealed_bid_commit_reveal_gate_v1.yaml`
  - Additional non-public evaluation methods were used during development; they are not part of the public release surface.
- **Non-reveal bond kernel**: closes the free-griefing path for non-reveal bidders.
  - Accounting core: `src/core/sealed_bid_bonds.py`
  - ESSO gate: `src/kernels/dex/sealed_bid_non_reveal_bond_v1.yaml`
  - Additional non-public evaluation methods were used during development; they are not part of the public release surface.
- **Experimental FHE sealed-bid alpha**: bounded 8-bid planning surface for encrypted comparison / hidden-bid auction pilots.
  - Alpha planner: `src/core/fhe_sealed_bid_alpha.py`
  - ESSO gate: `src/kernels/dex/fhe_sealed_bid_alpha_gate_v1.yaml`
  - Tau guard: `src/tau_specs/recommended/fhe_sealed_bid_alpha_guard_v1.tau`
- **Disaster-state catalog**: explicit terminal hazards and their discharge actions.
  - Catalog doc: `docs/SEALED_BID_DISASTER_STATE_CATALOG.md`
  - Replay tool: `python3 tools/sealed_bid_disaster_catalog.py`

Who this is for:
- large trades that would leak too much intent on a public path
- batch auctions / token sales where hidden bids improve fairness
- private RFQ / institutional flow
- strategy providers who want to get paid for private execution logic

## Permissionless Hosting
- Operator guide: `docs/PERMISSIONLESS_HOSTING.md`
- Local Tau node + app bridge: `docs/tau_testnet_local_node.md`
- Static/IPFS frontend publisher: `bash tools/publish_ui_ipfs.sh`

Recommended posture:
- run the public path with a rootless container or Podman
- keep `TAU_NET_RPC` unset unless you intentionally want a remote fallback
- prefer a local Tau node over a managed RPC
- pin/mirror the static frontend independently of the API if you want globally replicable hosting

Useful operator commands:

```bash
# Optional local-node-first stack
docker compose -f docker-compose.yml -f docker-compose.permissionless.yml --profile local-node up -d

# IPFS/static release artifact + manifest
bash tools/publish_ui_ipfs.sh

# Rootless Linux service file + preflight
python3 tools/generate_operator_systemd.py --engine podman --local-node --out ~/.config/systemd/user/zenodex-operator.service
python3 tools/permissionless_operator_preflight.py --engine podman --local-node --ipfs --json

# Objective useful-work round + payout plan (prototype)
python3 tools/gpu_jobs/improvement_bounty_round_route_v1.py --help

# Proof-mining-compatible claim bridge
python3 tools/permissionless_solver_proof_mining_claim.py --help

# Public append-only ledger for round winners + reward artifacts
python3 tools/permissionless_round_ledger.py --help
```

Who this is not for:
- ordinary retail swaps where the public path is simpler and faster
- always-on low-latency execution where extra coordination hurts UX
- use cases that need encrypted on-chain state rather than private off-chain execution

Useful commands:
```bash
python3 tools/sealed_bid_disaster_catalog.py
```

Additional non-public evaluation methods for sealed-bid flows are intentionally not documented in the public README.
## Experimental Curves (Research)
ZenoDex is designed to support multiple **integer-auditable AMM curves** (CFMM invariants). The production path is CPMM;
other curves live behind “research / not-default” status until they have strong evidence (tests + specs + proofs).

- **CPMM (baseline)**: `K = x*y` with deterministic fee+rounding semantics (`src/core/cpmm.py`, `src/kernels/dex/cpmm_swap_v8.yaml`).
- **Quadratic CPMM (experimental)**: `K = x^2*y` (`src/core/quadratic_cpmm.py`).
- **Cubic-sum AMM (experimental)**: `K(x,y)=x*y*(p*x+q*y)` (baseline `p=q=1` ⇒ `K=x*y*(x+y)`)
  (`src/core/cubic_sum_amm.py`, `src/kernels/python/cubic_sum_swap_v1.py`, `src/kernels/dex/cubic_sum_swap_v1.yaml`).
  - Exact-out is designed to be **quadratic-solvable** (integer `ceil_isqrt` + `ceil_div`) and **minimal** (by construction + certificates).
  - Like CPMM, integer exact-out may **overdeliver** due to rounding granularity; specs must treat “≥ requested out” as success.
  - Research result (continuous, fee-free): cubic-sum improves near-balance slippage but has higher IL than CPMM for all tested price moves; see `docs/CUBIC_SUM_CURVE_ANALYSIS.md`.
  - Formal result (local, continuous): for the power-family `K=x*y*(x+y)^α` (includes cubic-sum as `α=1`), a Lean-verified local tradeoff holds:
    improving near-balance “slippage coefficient” worsens local IL curvature vs CPMM; see `docs/CUBIC_SUM_CURVE_ANALYSIS.md` and `lean-mathlib/Proofs/ImpossibilityTheorem.lean`.
  - Research result (discrete, integer rounding): deterministic sweeps suggest smaller exact-out overdelivery gaps vs CPMM in small-reserve regimes; see `tools/curve_comparison_sweep.py`.

## Quick Start (Local)
```bash
# Full local checkout (runtime + agent helpers + tests)
pip install -r requirements.txt

# Minimal runtime-only install
# pip install -r requirements-core.txt

# Clone Tau dependencies (git-ignored)
mkdir -p external
cd external
git clone https://github.com/IDNI/tau-lang.git
git clone https://github.com/IDNI/tau-testnet.git
```

## UI (Local)
```bash
# 1) Start the stdlib demo/dev API (perps + zUSD).
# DEMO_API_TOKEN is optional on loopback (`API_HOST=127.0.0.1`), and required on non-loopback binds.
PERPS_API_ENABLED=true ZUSD_API_ENABLED=true DEMO_API_TOKEN=sekret python3 -m src.integration.api_server

# 2) Start the UI (Vite dev server). Recommended: use the proxy (no CORS needed).
cd tools/dex-ui
npm install
VITE_DEMO_MODE=false API_PROXY_TARGET=http://127.0.0.1:8000 VITE_API_TOKEN=sekret npm run dev -- --host 127.0.0.1 --port 5173
```

## Build Tau (example)
```bash
cmake -S external/tau-lang -B external/tau-lang/build-Release -DCMAKE_BUILD_TYPE=Release
cmake --build external/tau-lang/build-Release -j
```

## Tests / Spec Checks
```bash
pytest tests/
bash tests/tau/test_specs_syntax.sh
```

## Docs (current)
- `docs/SPECIFICATION.md` — Protocol specification overview
- `docs/SECURITY_POSTURE.md` — Runtime hardening choices and operator-facing security posture
- `docs/ZDEX_TOKEN.md` — ZDEX tokenomics and spec references
- `docs/ZENO_ORACLE_MVP_STATUS.md` — current Zeno Oracle MVP branch status
- `docs/ZENO_ORACLE_MVP_DESIGN.md` — Zeno Oracle MVP design snapshot
- `docs/ZENO_ORACLE_PRODUCTION_GATES.md` — Zeno Oracle rollout and verifier gates
- `docs/ZENO_ORACLE_RECEIPT_FORMAT_V1.md` — current local Oracle receipt-bundle format
- `docs/ZENO_ORACLE_SIGNED_REPORT_V1.md` — current local Oracle signed-report format
- `docs/ZENO_ORACLE_REPORT_ADMISSION_V1.md` — current local Oracle report-admission bridge format
- `docs/ZENO_ORACLE_MEDIAN3_AGGREGATE_V1.md` — current local Oracle median3 aggregate format
- `docs/ZENO_ORACLE_ADMITTED_MEDIAN3_V1.md` — current local Oracle admitted-report median3 aggregate format
- `docs/ZENO_ORACLE_AGGREGATE_READ_V1.md` — current local Oracle aggregate-to-read bridge format
- `docs/ZENO_ORACLE_SOURCE_DIVERSITY_V1.md` — current local Oracle source-diversity format
- `docs/ZENO_ORACLE_QUERY_POLICY_V1.md` — current local Oracle query-policy versioning format
- `docs/ZENO_ORACLE_ADAPTER_V1.md` — current local Oracle critical-action adapter format
- `docs/ZENO_ORACLE_CONSUMER_PROFILES_V1.md` — current local Oracle critical consumer profile catalog
- `docs/ZENO_ORACLE_ECONOMIC_SECURITY_V1.md` — current local Oracle economic security envelope
- `docs/ZENO_ORACLE_TOKEN_BUDGET_V1.md` — current local Oracle token budget format
- `docs/ZENO_ORACLE_REPORTER_LIFECYCLE_V1.md` — current local Oracle reporter lifecycle format
- `docs/ZENO_ORACLE_CHAOS_ENGINEERING.md` — Zeno Oracle disaster-shape replay lane
- `docs/ECOSYSTEM_STRATEGY.md` — Deflationary DAC ecosystem design
- `docs/ECOSYSTEM_GRAPH.md` — Ecosystem module graph
- `docs/TOKEN_VERSIONS.md` — Token spec hierarchy (V1–V8)
- `docs/TOKEN_GOVERNANCE.md` — Governance parameter design
- `docs/ALGORITHMS.md` — Algorithm catalog
- `docs/CONFIDENTIAL_FEATURES_USE_CASES.md` — Confidential extensions plain-language guide
- `docs/TAU_LANGUAGE_CONSTRAINTS.md` — Tau Language bitvector and stream constraints
- `docs/TAU_ARCHITECTURE.md` — Tau integration architecture
- `docs/REVISION_PIPELINE.md` — Spec revision workflow
- `docs/KERNEL_ABI_AND_COMPOSITION.md` — Kernel interface and composition
- `docs/VERIFIED_COMPUTATION_MPRD_TAU_TESTNET.md` — MPRD verification on testnet
- `docs/PROOF_MINING.md` — Proof-of-useful-work mining
- `docs/PERMISSIONLESS_HOSTING.md` — Operator hosting guide
- `docs/CUBIC_SUM_CURVE_ANALYSIS.md` — Curve tradeoff analysis
- `docs/papers/zenodex-full-system/README.md` — Full-system paper package
- `docs/PRODUCTION_GATE.md` — Production readiness gate
- `docs/DEX_READINESS_PEER_REVIEW.md` — Peer review of readiness
- `docs/derivatives/` — Perpetuals and zUSD specifications

## Status
Active research and implementation. Specs evolve frequently; check `docs/dex_readiness.md` for coverage status.

## License
TBD
