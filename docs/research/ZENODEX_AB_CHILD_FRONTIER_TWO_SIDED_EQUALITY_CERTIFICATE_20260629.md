# ZenoDEX AB Two-Sided Child-Frontier Equality Certificate - 2026-06-29

## Executive Result

A bounded two-sided child-frontier certificate pairs one-witness coverage with generated-state binding and rejects the hidden-extra countermodel that coverage-only verification accepted.

Research-only certificate-boundary evidence; no settlement, state-root, production, routing, matching, pool-mutation, or governance authority.

## Certificate Shape

```text
coverage_witnesses + generated_state_digest + child_state_digest -> bounded frontier equality check
```

The verifier accepts only when every advertised child state has a witness and the generated-state set equals the advertised child-state set.

## Replay Result

- Packet hash: `5180484e1cb6893879873caaf811296598f2c377255acbccbba55b3b38cba650`
- Child-state digest: `20debc2b386b88b55708cbd5c6d18febab91b3ea22beea0f030064f40d3d7dfd`
- Generated-state digest: `20debc2b386b88b55708cbd5c6d18febab91b3ea22beea0f030064f40d3d7dfd`
- Witness rows digest: `8216f62477012095592dcc45ed7551b3cadf83d84aa1a3f61f5b612f7ce60290`
- Child states: `2`
- Generated states: `2`
- Witness rows: `2`
- Baseline accepted: `True`
- Extra-world rejected: `True`
- Stale digest rejected: `True`
- Coverage-only rejected: `True`
- Equality certificate valid: `True`
- Negative controls: `8`
- Negative control accepts: `0`
- Deterministic replay ok: `True`

## Hidden Extra Rejection

```json
{
  "child_state_count": 2,
  "covered_child_state_count": 2,
  "extra_generated_state_count": 1,
  "extra_generated_states": [
    {
      "processed_reserve_in": 170,
      "reserve_out": 9830
    }
  ],
  "generated_state_count": 3,
  "missing_generated_state_count": 0,
  "missing_generated_states": [],
  "missing_witness_count": 0,
  "ok": false,
  "reasons": [
    "generated_frontier_extra_child_state"
  ],
  "witness_count": 2
}
```

## Coverage-Only Rejection

```json
{
  "child_state_count": 2,
  "covered_child_state_count": 2,
  "extra_generated_state_count": 0,
  "extra_generated_states": [],
  "generated_state_count": 0,
  "missing_generated_state_count": 2,
  "missing_generated_states": [
    {
      "processed_reserve_in": 100,
      "reserve_out": 9900
    },
    {
      "processed_reserve_in": 140,
      "reserve_out": 9861
    }
  ],
  "missing_witness_count": 0,
  "ok": false,
  "reasons": [
    "frontier_equality_bound_missing",
    "generated_state_binding_missing",
    "generated_state_digest_mismatch",
    "generated_frontier_missing_child_state"
  ],
  "witness_count": 2
}
```

## Negative Controls

| mutation | accepted | expected reason |
| --- | ---: | --- |
| `packet_hash_mismatch` | `False` | `packet_hash_mismatch` |
| `child_state_digest_mismatch` | `False` | `child_state_digest_mismatch` |
| `generated_state_digest_mismatch` | `False` | `generated_state_digest_mismatch` |
| `generated_frontier_missing_child_state` | `False` | `generated_frontier_missing_child_state` |
| `generated_frontier_extra_child_state` | `False` | `generated_frontier_extra_child_state` |
| `missing_child_state_witness` | `False` | `missing_child_state_witness` |
| `frontier_equality_bound_missing` | `False` | `frontier_equality_bound_missing` |
| `authority_effect_present` | `False` | `authority_effect_present` |

## Hypothesis Card

```json
{
  "expected_metric_delta": {
    "cap_efficiency": "0",
    "determinism_simplicity": "+explicit equality obligation",
    "execution_quality": "0",
    "perf_cost": "+one extra digest and generated-state set check",
    "safety": "+rejects hidden extra generated states in bounded model"
  },
  "falsification_recipe": "Mutate generated states, state digests, witness rows, equality rails, packet hashes, and authority rails; any accepted negative control falsifies the certificate boundary.",
  "formal_obligations": "A production-grade theorem would need to prove that the generated state set is the complete transition image for the scoped domain.",
  "hypothesis_id": "H-AB-TWO-SIDED-EQUALITY-CERTIFICATE-20260629",
  "mechanism_change": "Add generated-image binding to one-witness child-frontier packets so the verifier checks child_states == generated_states.",
  "null_hypothesis": "A generated-state digest plus witness coverage can distinguish the bounded hidden-extra world from the baseline world.",
  "representation_shift_used": "certificate_boundary",
  "risk_modes": [
    "generated-state digest not recomputed",
    "coverage witness overclaimed as equality",
    "hidden generated state",
    "authority leakage",
    "stale packet hash"
  ],
  "status": "supported_bounded",
  "support_recipe": "Verify the baseline packet, reject the hidden-extra packet, reject coverage-only packets, and assert zero accepted negative controls."
}
```

## Design Recommendation

- Use coverage_witnesses + generated_state_digest as a compact bounded certificate shape for no-extra child-frontier claims.
- Reject coverage-only packets whenever the claim needs frontier equality rather than coverage.
- Keep the certificate research-only until a production verifier or Lean theorem checks complete generated-image construction.

## Non-Claims

- Scope is limited to a bounded certificate-boundary design; universal claims about all ZenoDEX frontier certificates are excluded.
- This artifact does not prove child-frontier generation in Lean.
- This artifact does not prove Python-to-Lean refinement.
- This artifact does not cover nonzero min_amount_out behavior.
- This artifact does not define canonical tie order or production verifier framing.
- No settlement, state-root, production, routing, matching, pool-mutation, or governance authority is derived from this artifact.

## Replay

```bash
python3 tools/check_ab_child_frontier_two_sided_equality_certificate_20260629.py
```
