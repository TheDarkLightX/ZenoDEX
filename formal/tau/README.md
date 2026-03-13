# Tau Formal Artifacts

This directory is the formal-promotion lane for Tau specs.

Contents:

- `spec_contract.schema.json`
  The required structure for a per-spec formal contract.
- `behavior_atlas.schema.json`
  The required structure for a per-spec behavior atlas.
- `recommended_proof_plan.json`
  Ordered proof-profile coverage for `src/tau_specs/recommended/*.tau`.
- `contracts/`
  Seed and future contract artifacts.
- `atlases/`
  Seed and future behavior-atlas artifacts.

The checker for the proof-plan registry is:

```bash
python3 tools/check_tau_formal_plan.py
```

The executable bounded seed-artifact gate is:

```bash
python3 tools/check_tau_formal_seed_artifacts.py --use-discovered-tau
```

The generalized formal-contract gate for active/promoted artifacts is:

```bash
python3 tools/check_tau_formal_contract_artifacts.py --use-discovered-tau
```

The bounded behavior-atlas generator is:

```bash
python3 tools/generate_tau_behavior_atlas.py --only oracle_freshness_v2
```

The repo-wide Tau execution census is:

```bash
python3 tools/generate_tau_execution_census.py --step-count 1
```

To merge retry passes into a single best-known census:

```bash
python3 tools/merge_tau_execution_census.py formal/tau/recommended_execution_census.json formal/tau/recommended_execution_census_retry120.json
```

To generate control/data semantic packets for selected specs:

```bash
python3 tools/generate_tau_semantic_view.py --spec-list-json formal/tau/remaining_execution_hard_specs.json
```

To generate the repo-wide semantic surface for every recommended Tau spec:

```bash
python3 tools/generate_tau_semantic_view.py --all-recommended --out-json formal/tau/recommended_semantic_view.json --out-md formal/tau/recommended_semantic_view.md
```

To check that the committed repo-wide semantic-view artifacts are complete and fresh:

```bash
python3 tools/check_tau_recommended_semantic_view.py
```

To build the repo-wide semantic-understanding status map:

```bash
python3 tools/build_tau_semantic_understanding_status.py
```

To scaffold draft contracts/atlases from the semantic-view surface:

```bash
python3 tools/scaffold_tau_contract_drafts.py
```

The current high-confidence semantic findings subset is:

- [`formal/tau/confirmed_semantic_findings.md`](confirmed_semantic_findings.md)

The current per-spec semantic-understanding status map is:

- [`formal/tau/semantic_understanding_status.json`](semantic_understanding_status.json)

The design document is:

- [`docs/TAU_FORMAL_ASSURANCE_PLAN.md`](../../docs/TAU_FORMAL_ASSURANCE_PLAN.md)

Bounded assurance remains useful, but promotion should eventually require:

- contract artifact
- machine-checkable contract expressions
- behavior atlas
- exactness / partition proofs
- Tau interpreter differential evidence

The repo-wide `recommended_semantic_view.*` artifact is intentionally weaker than the
exact semantic-contract lane. It is the all-recommended structural-semantic surface:

- every recommended spec is included
- every spec is mapped to a proof-plan profile/rule
- every spec exposes its `always` control surface
- the normalized output-equation surface is machine-extracted, with indexed equations
  preserved where the spec uses history-shaped output slots

It does **not** mean every recommended spec already has a human-authored contract and
proof of `forall x in D: ⟦S⟧(x) = C(x)`. That exactness claim remains scoped to the
smaller semantic-contract / bounded-seed subsets until more contracts and proofs are added.
