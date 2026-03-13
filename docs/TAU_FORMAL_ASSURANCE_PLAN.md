# Tau Formal Assurance Plan

This document defines the strongest guarantee this repo should aim for for Tau
specs. The target is not "many tests passed." The target is a proved statement:

For a Tau spec `S`, explicit domain `D`, and formal contract `C`, prove that
for every input `x ∈ D`, the Tau semantics `⟦S⟧(x)` is defined and exactly
matches `C(x)`.

That decomposes into:

- Totality: `⟦S⟧(x)` is defined for all `x ∈ D`.
- Exactness: `⟦S⟧(x) = C(x)` for all `x ∈ D`.
- Partition completeness: every `x ∈ D` lands in exactly one proved behavior
  region.
- Reachability accounting: every output pattern is either proved reachable with
  a witness or proved unreachable.
- Interpreter trust: the formal semantics and the Tau binary agree on the
  supported spec subset.

This is the standard required to say a Tau spec has "full behavioral coverage"
under explicit assumptions.

## Artifact Set

The formal lane lives under [`formal/tau/`](../formal/tau/README.md).

Required artifacts per promoted spec:

- Contract artifact:
  [`formal/tau/spec_contract.schema.json`](../formal/tau/spec_contract.schema.json)
- Behavior-atlas artifact:
  [`formal/tau/behavior_atlas.schema.json`](../formal/tau/behavior_atlas.schema.json)
- Coverage / wave assignment registry:
  [`formal/tau/recommended_proof_plan.json`](../formal/tau/recommended_proof_plan.json)

The current bounded assurance lane in
[`docs/TAU_SPEC_ASSURANCE.md`](TAU_SPEC_ASSURANCE.md)
remains valuable, but it is regression evidence, not the final proof object.

## Contract Format

Each spec needs a contract artifact that states:

- exact input domain and any assumed preconditions
- public meaning of every output stream
- machine-checkable output expressions for the current proof scope
- required proof obligations for each output and for the aggregate behavior
- intended partition basis for the behavior atlas

The contract is the source of truth for "what the spec is supposed to mean."
No English-only promotion. Every contract must also declare its proof scope,
for example `bounded_assurance_domain` vs `full_input_domain`.

## Behavior Atlas

Each atlas is a partition of the explicit domain by output vector.

For every output vector `y`, the atlas records:

- the characteristic region formula `B_y`
- whether `B_y` is reachable, unreachable, or still open
- a witness input if reachable
- proof references for reachability or impossibility

Promotion requires:

- disjointness proof: no input belongs to two regions
- exhaustiveness proof: every input belongs to some region
- witness coverage for every reachable region
- impossibility proof for every forbidden / absent region

## Proof Profiles

The proof-plan registry assigns every `src/tau_specs/recommended/*.tau` file to
an ordered profile. The current profiles are:

- `exact_combinational_guard`
- `multi_limb_word_arithmetic`
- `proof_gate_or_certificate`
- `bundle_or_composition`
- `stateful_policy_guard`
- `default_combinational_guard`

Each profile fixes:

- required artifacts
- required theorem families
- preferred mechanization stack
- promotion gate expectations

This keeps new specs from bypassing the formal lane by accident.

## Mechanization Stack

The preferred stack for combinational specs is:

1. Contract-level exact bitvector equivalence in SMT.
2. Lean theorems for arithmetic facts, carry/borrow lemmas, and any normalization
   that should not depend on solver heuristics.
3. Differential execution against the Tau binary for the supported subset.
4. Bounded assurance / regression enumeration as a guardrail, not as the final proof.

Use stronger profiles for:

- multi-limb arithmetic
- certificate or proof-gated specs
- bundle / composition specs
- specs whose meaning depends on step-to-step policy interpretation

## Interpreter Trust Boundary

There are two separate claims:

- "the Tau formula means what we intend"
- "the Tau interpreter executes that formula correctly"

The formal lane must make both explicit.

For the supported Tau subset used in promoted specs:

- define a trusted formal semantics / mirror
- prove or exhaustively check equivalence of that semantics against the Tau binary
- record the Tau build / commit used for differential evidence

If a spec uses unsupported Tau features, it cannot be promoted under this lane
until the semantics is extended.

## CI Gates

The proof plan should be mechanically checked in CI.

Minimum CI gate:

```bash
python3 tools/check_tau_formal_plan.py
```

That gate is intentionally narrow: every recommended Tau spec must be assigned
to exactly one proof profile / wave in the registry. Coverage drift should fail
fast even before proofs are written.

Bounded exactness gate for seeded specs:

```bash
python3 tools/check_tau_formal_seed_artifacts.py --use-discovered-tau
```

Generalized active/promotion gate for formal contracts:

```bash
python3 tools/check_tau_formal_contract_artifacts.py --use-discovered-tau
```

That gate checks, on the explicit assurance domain, that:

- the contract expressions reproduce the documented behavior
- the extracted Tau semantics matches the contract
- the atlas exactly matches reachable vs unreachable output vectors
- the Tau binary matches the same contract when available

## Initial Adoption Plan

Wave ordering:

1. Seed disputed / reviewed specs with exact contracts and initial atlases.
2. Clear multi-limb arithmetic specs with Lean carry/borrow lemmas plus SMT.
3. Clear proof gates and certificate guards by linking them to their kernel or
   witness contracts.
4. Expand to the remaining recommended combinational guards by profile.
5. Promote only after contract, atlas, and interpreter-equivalence evidence exist.

To accelerate authoring without auto-promoting claims, use scaffold generation:

```bash
python3 tools/scaffold_tau_contract_drafts.py
```

The scaffold output is draft-only by design. It provides contract/atlas skeletons and
does not mark artifacts active or promoted.

The seed example currently included is:

- [`formal/tau/contracts/oracle_freshness_v2.contract.json`](../formal/tau/contracts/oracle_freshness_v2.contract.json)
- [`formal/tau/atlases/oracle_freshness_v2.atlas.json`](../formal/tau/atlases/oracle_freshness_v2.atlas.json)

The current seed set also includes:

- `rate_limiter_v1`
- `nonce_replay_guard_v1`
- `sandwich_detection_v1`

These are the initial active bounded-domain artifacts. They demonstrate the
structure the repo should standardize on for the full recommended set, but they
still do not imply full-input-domain correctness.
