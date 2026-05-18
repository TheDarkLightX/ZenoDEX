# WES Checker Tools

This directory contains command-line checkers used by Witness Energy Search.
They build real ZenoDEX cases, apply WES candidate mutations, run the normal
ZenoDEX checker path, and emit WES `CheckResult` JSON.

## recompute_batch_v4_wes_checker.py

Checks candidates against the real `recompute_batch_v4` proof path:

```bash
python tools/wes/recompute_batch_v4_wes_checker.py candidate.json
```

The checker returns:

```json
{
  "result": "near_miss",
  "checker": "zenodex_recompute_batch_v4_wes_checker",
  "checker_ms": 123.4,
  "violated_predicate": "zenodex_recompute_batch_v4_binding_rejects_invalid",
  "replay_receipt": "sha256:...",
  "telemetry": {
    "engine_ok": false,
    "error_code": "proof pre_state_commitment mismatch"
  }
}
```

This is not a consensus path. It is regression-search tooling.

The checker currently runs each mutation against `create_pool`,
`swap_exact_in`, and `add_liquidity` base transitions. Covered mutation
families include proof commitment drift, embedded witness drift, malformed
witness encodings, missing witness fields, invalid witness JSON, malformed
embedded operation shapes, proof envelope policy, duplicate proof fields,
legacy `zk_proof`, v4 quotient controls, and outer settlement payload drift.

The canonical case contract is in `recompute_batch_v4_cases.json`. Tests load
that file directly so expected outcomes are data, not only test code.

## run_recompute_batch_v4_bridge.py

Runs the full WES bridge from this ZenoDEX checkout:

```bash
python tools/wes/run_recompute_batch_v4_bridge.py \
  --wes-root /path/to/WitnessEnergySearch \
  --out-dir artifacts/wes/zenodex_recompute_batch_v4
```

The wrapper delegates to:

```bash
python -m wes.cli run-zenodex-recompute-batch-v4
```

and returns WES's exit code. A healthy report returns success. An unhealthy
report fails unless `--allow-unhealthy` is passed for local diagnosis.
