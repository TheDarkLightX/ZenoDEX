# Kernel ABI + Composition

This repo uses YAML kernel specs (`src/kernels/**.yaml`) as **deterministic state machines**. The highest-ROI way
to scale correctness is to treat *interfaces* as first-class and verified: define module ABIs, decompose by risk
surfaces, and then prove that the composition preserves global invariants.

This document explains:
- what we mean by a kernel “ABI template”
- how to name and classify effects (observable vs internal)
- how to compose kernels safely using a system spec

## Terminology (concrete meanings in this repo)

### Kernel (module)
A YAML kernel spec file with:
- `state_vars`: the full internal state of the module
- `actions`: commands the module accepts (each with `params`, a `guard`, `updates`, and `effects`)
- `invariants`: properties that must hold in every reachable state
- `observables`: the *external contract* we treat as the module’s ABI

### Command
In this repo, a “command” means invoking an `action` by `id` with concrete `params`.

### Effect
An “effect” is an action output (a value computed from pre-state/params and/or post-state). In a blockchain analogy,
effects are “events” or “return values” from a step.

Effects matter because they are:
- the right place to expose *public* outputs (fees paid, amount out, minted shares, etc.)
- the safest “wiring pins” to connect modules in a system spec (without giving other modules raw write-access)

### Observable vs internal (non-observable)
`observables` defines what we consider “ABI”:

- `observables.state_vars`: state we promise is visible/stable to external users of the kernel.
- `observables.effects`: effects we promise are visible/stable.

Anything **not** listed under `observables.*` is treated as internal and can be added for composition/testing without
changing the module’s observational contract.

This repo relies on that property to build *compose-friendly wrappers*:
- add extra effects like `new_reserve_x` for wiring
- keep `observables.*` unchanged
- verify observational equivalence to the original kernel

## What is an “ABI template” for a kernel?

An ABI template is a **repeatable structure + naming discipline** that makes a kernel:
- easy to compose (explicit ports)
- easy to upgrade (stable names + versioning)
- easy to verify (clean separation of “public contract” vs “internal wiring”)

Concretely, an ABI template is:
1) A stable list of **commands** (action ids + parameter names/types).
2) A stable list of **observable state** (`observables.state_vars`).
3) A stable list of **observable effects** (`observables.effects`).
4) A convention for **internal wiring effects** (non-observable) that expose “next values” safely.

Minimal skeleton:

```yaml
ir_version: "<ir_version>"
meta:
  model_id: "<name>_vN"
observables:
  state_vars: ["<public_state_var>", "..."]
  effects: ["<public_effect>", "..."]
types: [...]
state_vars:
  - id: "<state_var>"
    role: "data" | "control"
    type: { kind: "int", min: 0, max: 123 }
invariants: [...]
init: [...]
actions:
  - id: "<command>"
    params: [...]
    guard: <expr>
    updates: [...]
    effects:
      # Public/observable effects (stable ABI)
      <public_effect>: <expr>
      # Internal wiring effects (NOT listed in observables.effects)
      <internal_effect>: <expr>
```

## Effect naming (why it matters, and how to do it)

Effect names are the “ports” other modules and tooling bind to. If naming drifts, composition breaks and upgrades become
dangerous (silent miswiring looks like a logic bug).

### Recommended naming convention

**1) Public effects (observable)**
- Name them as *user-meaningful outputs*.
- Keep them stable across refactors.
- Prefer explicit direction/units:
  - `amount_in`, `amount_out`
  - `fee_paid`, `net_in`
  - `lp_shares_minted`, `lp_shares_burned`
  - `k_before`, `k_after` (if exposing constant-product diagnostics)

**2) Internal wiring effects (non-observable)**
Use these when another module needs a value *deterministically*.

Pattern: `new_<state_var_name>`
- Meaning: “the post-state value of `<state_var_name>` after this action”
- Example: `new_reserve_x`, `new_total_lp_shares`, `new_staked_lp_shares`

Why this pattern is high-ROI:
- It is unambiguous (“new” == post-state)
- It composes cleanly with “set” wiring ops
- It stays out of the ABI by default (not listed under `observables.effects`)

**3) Internal intent effects (optional)**
If you want strict “no cross-module writes”, another pattern is *intent-only wiring*:
- `intent_ledger_delta_x`, `intent_transfer`, `intent_burn`, etc.
- A downstream module validates and applies the intent.

This is often better for security, but it requires more plumbing than “new_* mirrors”.

## Composition: how to wire kernels without breaking trust boundaries

### The core pattern: “Mirror + Sync + Global Invariant”

If module A needs a fact owned by module B to enforce a safety property **inductively**, do not let A read or mutate B.
Instead:
1) Add a **mirror state var** in A (usually non-observable).
2) Add a **wiring rule** that deterministically updates the mirror after the actions in B that can change the source.
3) Add a **system-level invariant** asserting the mirrors match (`A.mirror == B.source`).

Why the invariant matters: it forces the *pre-state* seen by every step to be consistent, so the property becomes
guard-inductive rather than “eventually consistent”.

### Example: stake-aware LP burn

We want: “LP shares cannot be burned below the amount staked in the vault.”

To make that inductive:
- LP has `vault_staked_lp_shares_mirror`
- Vault has `staked_lp_shares`
- System invariant: `lp.vault_staked_lp_shares_mirror == vault.staked_lp_shares`
- Wiring: `vault.stake.new_staked_lp_shares -> lp.vault_staked_lp_shares_mirror` and same for `unstake`
- LP `remove_liquidity` guard fails closed if a burn would make `total_lp_shares - burn < mirror`

### Reserve synchronization

For a single-pool “core”, we also want reserves consistent between the AMM swap engine and the LP accounting.

We do this with internal effects:
- swap emits `new_reserve_x/new_reserve_y`
- LP emits `new_reserve_a/new_reserve_b`
- wiring sets the other module’s mirrored reserve state vars
- global invariants enforce equality

## Current ZenoDex compose artifacts

These are additive; they do not modify the original A+ kernels.

- System spec: `src/kernels/dex/zenodex_system_compose_v1.yaml`
- Compose-friendly wrappers (ABI-compatible, equivalence-verified):
  - `src/kernels/dex/cpmm_swap_compose_v1.yaml`
  - `src/kernels/dex/liquidity_pool_compose_v1.yaml`
  - `src/kernels/dex/vault_manager_compose_v1.yaml`
- Stake-aware composition variants (new behavior in new files):
  - `src/kernels/dex/liquidity_pool_compose_v2.yaml`
  - `src/kernels/dex/vault_manager_compose_v2.yaml`

## Refactor vs “new implementation” (how to avoid regressions)

Use these rules:
- **Refactor**: allowed when you can prove observational equivalence to the existing kernel (same `observables.*` and
  behavior). Example: adding internal wiring effects to enable composition.
- **New behavior**: must go in a new file/version suffix (e.g. `_compose_v2`, `_v1_4`), never overwrite the A+ file.

The “don’t step backwards” guarantee comes from:
- keeping the original kernel intact
- proving equivalence for wrappers
- adding system invariants that become inductive (fail-closed guards + mirror consistency)
