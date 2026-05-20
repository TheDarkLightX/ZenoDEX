# Gemini Langevin Discovery Boundary

```text
ok: true
decision: research_only_verifier_checked_proposal
seed_energy: 289.823312
refined_energy: 281.350644
energy_delta: -8.472668
seed_verifier_ok: true
refined_verifier_ok: false
accepted_refinement: false
fallback_to_seed: true
selected_verifier_ok: true
```

Langevin refinement is a proposal mechanism. The selected candidate is verifier-backed; a lower-energy refined proposal is rejected when deterministic verification fails.

## Checks

| check | status |
| --- | --- |
| `langevin_discovery.seed_verifier_ok` | pass |
| `langevin_discovery.selected_verifier_ok` | pass |
| `langevin_discovery.model_does_not_authorize_settlement` | pass |
| `langevin_discovery.invalid_refinement_falls_back` | pass |

## Negative Knowledge

- Lower learned energy does not imply verifier acceptance.
- ZenoGuard is an advisory soft prior and cannot prove candidate validity.
- Langevin proposals must be canonicalized and checked by the deterministic verifier before selection.
