# ZenoDEX Disaster Schema Instantiations Proof Receipt

Date: 2026-04-28

Integrated module:

- `Proofs.ZenoDEXDisasterSchemaInstantiations`

Purpose:

- instantiate the generic forbidden-minor and no-free-resource theorem schemas
  against small ZenoDEX-shaped surfaces
- provide proof adapters for future replay receipts without claiming a new
  closed disaster-axis count

Accepted theorem layer:

- `nonpositive_event_deltas_cannot_create_positive_resource`
- `api_scan_prefix_claim_above_budget_rejected`
- `proof_mining_reward_claim_above_budget_rejected`
- `bounty_claim_above_budget_rejected`
- `proof_work_claim_above_budget_rejected`
- `known_motif_bad_traces_rejected`
- `accepted_known_motif_bad_impossible`

Instantiated surfaces:

- API scan resource budget
- proof-mining reward budget
- bounty payout budget
- proof-work budget
- stale quote plus settlement-use motif
- missing oracle plus perps-settlement motif
- unpaired COW-fill motif
- API overscan request motif

Local acceptance checks:

```text
cd lean-mathlib && lake env lean Proofs/ZenoDEXDisasterSchemaInstantiations.lean
cd lean-mathlib && lake build Proofs.ZenoDEXDisasterSchemaInstantiations Proofs.NoFreeResourceTraceLedger Proofs.ForbiddenTraceMinor Proofs.DisasterAntichainBasis Proofs.CertificateGluing
python3 tools/check_formal_proof_hygiene.py
pytest -q tests/integration/test_disaster_assurance_ratchets.py tests/test_public_text_hygiene.py tests/test_security_posture_files.py
```

Scope:

- This is a concrete adapter layer over abstract proof schemas.
- It does not prove concrete Python/Tau runtime refinement.
- It does not increase the current closed disaster-state receipt from `29`.
- The next promotion step is to bind concrete replay receipts to these adapter
  predicates.
