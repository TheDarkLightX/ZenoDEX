# DAC / DEX Module Catalog (TauSwap)

This repository is evolving toward a **spec-driven DAC architecture** where each module is:

- a **small, Tau-executable specification** (`src/tau_specs/*.tau`)
- paired with a clear **interface** (inputs/outputs)
- governed via **pointwise revision** (versioned rule updates)

## Design rules (global)

- **Determinism:** outcomes depend only on explicit inputs; no hidden ordering authority.
- **Bounded compute:** every module must be evaluable without unbounded loops.
- **External computation pattern:** any 256-bit math or cryptography is computed outside Tau and validated by constraints inside Tau.

## Modules

## 1) Canonicalization (reject-only)

- **Spec:** `batch_canonical_v1_4.tau`
- **Purpose:** enforce unique canonical batch encoding (strictly increasing intent IDs)
- **Invariants:**
  - if `valid=1` then `id0 < id1 < id2 < id3`
- **Upgrade knobs:** batch size (N), ID type width

## 2) Deterministic batching (ordering safety)

- **Specs:** `batching_v1.tau`, `batching_v1_4.tau`
- **Purpose:** ensure “executed order” is a strictly increasing permutation of the included IDs
- **Invariants:** distinctness, membership, strict order
- **Upgrade knobs:** batch size (N), membership policy

## 3) CPMM validation (external computation constraint layer)

- **Spec:** `cpmm_v1.tau`
- **Purpose:** validate externally computed swap outputs satisfy basic safety constraints
- **Invariants:**
  - fee bounds
  - reserves positive
  - `amount_out <= reserve_out`
- **Upgrade knobs:** fee cap, rounding conventions, additional invariant checks

## 4) Swap exact-in validation (bounds + reserve transitions)

- **Spec:** `swap_exact_in_v1.tau`
- **Purpose:** validate exact-in swaps with slippage bounds and reserve transitions
- **Invariants:**
  - `amount_out >= min_amount_out`
  - `amount_out <= reserve_out`
  - `new_reserve_in = reserve_in + amount_in`
  - `new_reserve_out = reserve_out - amount_out`
- **Upgrade knobs:** slippage rules, fee caps, reserve transition checks

## 5) Swap exact-out validation (bounds + reserve transitions)

- **Spec:** `swap_exact_out_v1.tau`
- **Purpose:** validate exact-out swaps with max input bounds and reserve transitions
- **Invariants:**
  - `amount_in <= max_amount_in`
  - `amount_out < reserve_out` (no full drain)
  - `new_reserve_in = reserve_in + amount_in`
  - `new_reserve_out = reserve_out - amount_out`
- **Upgrade knobs:** slippage rules, fee caps, reserve transition checks

## 6) Balance transition validation

- **Spec:** `balance_transition_v1.tau`
- **Purpose:** validate `balance_after = balance_before + delta_add - delta_sub`
- **Invariants:**
  - all limbs non-negative
  - no underflow on `delta_sub`
  - balance update matches provided witness
- **Upgrade knobs:** limb width, witness structure

## 7) Protocol token (ledger transition validity)

- **Spec:** `protocol_token_v1.tau`
- **Purpose:** validate a single token transition (transfer/mint/burn) using 32-bit (hi/lo) limbs
- **Invariants:**
  - transfer keeps supply constant and conserves value between two accounts
  - mint increases supply by minted amount
  - burn decreases supply by burned amount
- **Upgrade knobs:** supply rules, permission model (external signature checks), rate limits

## 8) Tokenomics: fee flow + buyback-and-burn

- **Spec:** `tokenomics_buyback_burn_v1.tau`
- **Purpose:** validate fee splits and bound buyback/burn actions
- **Invariants:**
  - fee splits sum to total fee (validated via external computation pattern)
  - burn only occurs when triggered, and is bounded by a limit
- **Upgrade knobs:** split ratios, burn limits, triggers (per batch / per epoch)

## Upgrade strategy (pointwise revision)

Each module is intended to be upgradable via governance-controlled rule updates. A safe baseline upgrade policy is:

- upgrades are **versioned** (old rules remain provable artifacts)
- upgrades must preserve a small set of **non-negotiable safety invariants** (no negative balances, bounded actions)
- upgrades should enforce **bounded parameter drift** (e.g., fee cap cannot jump arbitrarily in one revision)
