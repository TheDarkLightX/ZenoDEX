# ZenoDEX M6 Normative Requirements V1

Status: research-only structural requirements registry. It grants no production or value-moving authority.

## Immutable source subject

- Source commit: `99667c04980e60b6298e433e33bf3a4efc77e983`
- Source tree: `1284e05d9f5606f28cbd6a1159b54a8fba2477a5`
- Artifact Git commit binding: none. This avoids a self-referential generated-artifact HEAD.

## Structural inventory

- Requirement atoms: 152 (18 WF, 81 BDD, 14 INV, 11 RSE, 8 CE, 20 UP)
- Lane-qualified capability targets: 103
- Enabled capability targets with direct semantic scope: 54
- Ambiguous capability targets: 2
- Cross-cutting capability targets: 0
- Disabled capability targets: 9
- Disabled capability targets with direct semantic scope: 2
- Enabled targets directly scoped by a workflow or BDD row: 51
- Enabled targets scoped by a BDD row: 46
- Enabled direct RSE-only gaps: 1
- Enabled direct CE-plus-RSE-only gaps: 2
- Enabled direct workflow-only targets: 5
- Global obligations: 5; missing concepts: 12
- Required routes: 4; exclusions: 4; invariant targets: 14
- These partitions describe requirements-scope classification. They do not establish feature implementation or semantic closure.

## Source-gate posture

- `docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json`: `CURRENT_CHECKER_PASS_RESEARCH_ONLY`
- `docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json`: `CURRENT_CHECKER_PASS_RESEARCH_ONLY`
- `docs/research/m6_global_economic_core_atdd_bdd_v1.json`: `STALE_INTERNAL_PROVENANCE_RESEARCH_ONLY_DRAFT`
- `docs/research/m6_global_economic_core_luna_completeness_review_v1.json`: `STALE_INTERNAL_PROVENANCE_ADVISORY_ONLY`

## Claim ceiling

- `manifest_complete=false`
- `requirements_closed=false`
- `release_eligible=false`
- `production_promotion=false`
- `production_authority=NONE`
- `settlement_authority=NONE`
- `source_row_census_complete=true`
- `semantic_target_inventory_complete=false`
- `structural_mapping_complete=false`
- `semantic_closure_complete=false`
- `value_movement_claim_allowed=false`

The registry records exact donor rows, typed inverse targets, and unresolved gaps. It is neither proof nor implementation evidence.
