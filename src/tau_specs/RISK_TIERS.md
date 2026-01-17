# ZenoDex Spec Tiers (Risk-Based Profiles)

This repo organizes Tau specs by **risk tier** so the community can decide which profile to deploy. The tiers are **not legal advice**; they are pragmatic groupings based on complexity, discretion, and external perception risk.

## Tier 1: Recommended (Canonical)
**Goal:** lowest-risk, transparent, deterministic, and bounded rules.
- Deterministic fee splits, rebates tied to usage, and service-tied treasury spends.
- Bounded governance parameters and timelocked changes.
- No discretionary market support or privileged flows.

Folder: `src/tau_specs/recommended/`

## Tier 2: Medium Risk
**Goal:** more aggressive tokenomics and features, still bounded but more complex.
- Adds stronger deflation mechanics, transfer taxes, or more elaborate buyback logic.
- Increases dependence on policy assumptions and parameter tuning.

Folder: `src/tau_specs/risk_medium/`

## Tier 3: Higher Risk
**Goal:** maximum experimentation and aggressive tokenomics.
- Complex or highly dynamic token policies.
- More external perception risk and higher coordination overhead.

Folder: `src/tau_specs/risk_high/`

## How to Use
1. Start with **Tier 1** if you want the safest, most predictable deployment.
2. Add **Tier 2** modules only if you understand the trade-offs.
3. Use **Tier 3** for research, testing, and experimental deployments.

## Important
- These tiers do **not** change protocol behavior by themselves; they are curated **profiles**.
- The production system should document which tier(s) are in use.
