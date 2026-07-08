# ZenoDEX AB One-Witness No-Extra Refuter - 2026-06-29

## Executive Result

A bounded countermodel refutes standalone no-extra claims for one-witness child-frontier packets: the same packet covers all advertised child states while a hidden extra generated state remains invisible to coverage-only verification.

Research-only certificate-boundary evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority.

## Countermodel

- Packet hash: `a742ca893b6f1df484d3bc24fdb5302bba6d661dffd328fa62fc5ffcf26446c0`
- Witness rows: `2`
- Advertised child states: `2`
- Baseline generated states: `2`
- Extra-world generated states: `3`
- Same packet hash for both worlds: `True`
- Coverage-only accepts baseline: `True`
- Coverage-only accepts extra world: `True`
- Full verifier accepts baseline: `True`
- Full verifier accepts extra world: `False`
- Countermodel valid: `True`
- Deterministic replay ok: `True`

The two worlds expose the same one-witness packet to a coverage-only verifier.
Only a verifier that also receives or recomputes generated states can reject the extra-world case.

## Hidden Extra State

```json
{
  "processed_reserve_in": 170,
  "reserve_out": 9830
}
```

## Full Extra-World Rejection

```json
{
  "extra_generated_state_count": 1,
  "extra_generated_states": [
    {
      "processed_reserve_in": 170,
      "reserve_out": 9830
    }
  ],
  "generated_state_count": 3,
  "missing_generated_state_count": 0,
  "ok": false,
  "reasons": [
    "generated_frontier_extra_child_state"
  ]
}
```

## Negative Controls

- Negative controls: `6`
- Negative control accepts: `0`

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `missing_child_state_witness` | `False` | `missing_child_state_witness` |
| `duplicate_witness_row` | `False` | `duplicate_witness_row` |
| `witness_child_not_in_frontier` | `False` | `witness_child_not_in_frontier` |
| `forbidden_standalone_no_extra_claim` | `False` | `forbidden_standalone_no_extra_claim` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Hypothesis Card

```json
{
  "expected_metric_delta": {
    "cap_efficiency": "0",
    "determinism_simplicity": "+clear certificate boundary",
    "execution_quality": "0",
    "perf_cost": "+constant refuter only",
    "safety": "+prevents overclaim"
  },
  "falsification_recipe": "Construct two worlds with identical one-witness packet hashes where coverage-only verification accepts both, but full generated-state verification rejects one for an extra generated state.",
  "formal_obligations": "Lean or Tau claims must distinguish coverage from no-extra generation.",
  "hypothesis_id": "H-AB-ONE-WITNESS-NO-EXTRA-REFUTER-20260629",
  "mechanism_change": "Treat one-witness child-frontier packets as coverage certificates, not standalone no-extra certificates.",
  "null_hypothesis": "One predecessor witness per child state is sufficient to prove no extra generated child states.",
  "representation_shift_used": "counterexample_boundary",
  "risk_modes": [
    "coverage certificate overclaimed as equality certificate",
    "hidden generated state",
    "authority leakage",
    "stale packet hash"
  ],
  "status": "falsified",
  "support_recipe": "Require future no-extra certificates to bind all generated-state images, a generated-state digest, or a theorem strong enough to derive no-extra."
}
```

## Design Recommendation

- Keep one-witness packets as coverage certificates only.
- For no-extra, add a generated-image digest, all-transition image check, or a stronger Lean theorem.
- Preserve the no-authority boundary until a production verifier independently checks the complete equality obligation.

## Non-Claims

- This refuter is a bounded certificate-boundary countermodel, not a proof about all possible ZenoDEX frontier certificates.
- This refuter does not invalidate n=7 or n=8 witness-coverage evidence.
- This refuter does not prove child-frontier generation in Lean.
- This refuter does not prove Python-to-Lean refinement.
- This refuter does not cover nonzero min_amount_out behavior.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_child_frontier_one_witness_no_extra_refuter_20260629.py
```
