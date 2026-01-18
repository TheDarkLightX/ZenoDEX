# ZenoDex

ZenoDex is a decentralized exchange (DEX) and token-economics stack for Tau Network. It uses a **hybrid model**: Python computes operational state, while **Tau Language specs validate invariants** and settlement rules.

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
  - `src/core/` DEX math
  - `src/state/` state transitions
  - `src/agents/` agent workflows
  - `src/tau_specs/` Tau specifications
- `docs/`: protocol/spec notes and ecosystem design
- `tests/`: test scripts and spec checks
- `external/`: Tau dependencies (git-ignored)

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
    improving near-balance “slippage coefficient” worsens local IL curvature vs CPMM; see `docs/AMM_POWER_FAMILY_LOCAL_TRADEOFF_WHITEPAPER.md`.
  - Research result (discrete, integer rounding): deterministic sweeps suggest smaller exact-out overdelivery gaps vs CPMM in small-reserve regimes; see `tools/curve_comparison_sweep.py`.

## Quick Start (Local)
```bash
pip install -r requirements.txt

# Clone Tau dependencies (git-ignored)
mkdir -p external
cd external
git clone https://github.com/IDNI/tau-lang.git
git clone https://github.com/IDNI/tau-testnet.git
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
- `docs/SPECIFICATION.md`
- `docs/ECOSYSTEM_STRATEGY.md`
- `docs/ECOSYSTEM_GRAPH.md`
- `docs/TAU_LANGUAGE_CONSTRAINTS.md`
- `docs/TAU_ARCHITECTURE.md`
- `docs/REVISION_PIPELINE.md`
- `docs/KERNEL_ABI_AND_COMPOSITION.md`
- `docs/VERIFIED_COMPUTATION_MPRD_TAU_TESTNET.md`
- `docs/PROOF_MINING.md`
- `docs/AMM_POWER_FAMILY_LOCAL_TRADEOFF_WHITEPAPER.md`

## Status
Active research and implementation. Specs evolve frequently; check `docs/dex_readiness.md` for coverage status.

## License
TBD
