# ZenoOracle Workflow Evidence Status

Status: first public workflow status check, bounded smoke evidence only.

Replay:

```bash
python3 tools/zeno_oracle_workflow_evidence_status.py --format text --skip-morph
```

Expected receipt:

```text
lane_count = 4
accepted_lane_count = 4
failed_lane_count = 0
status = accepted
```

The checker covers these public lanes:

- TLA Oracle recovery lifecycle artifacts and replay command.
- LTLf Oracle recovery artifacts and replay command.
- ESSO zUSD Oracle recovery lifecycle artifacts and replay command.
- Temporary PopperPad append-only smoke using `tools/popper_pad.py`.

The default command without `--skip-morph` includes the strict Morph
oracle-clamp envelope smoke check and fails closed when the Morph verifier is
unavailable.

This lane is a status and smoke boundary. It does not publish private PopperPad
content, claim Morph replay verification when `--skip-morph` is used, claim
exhaustive Morph search, or certify production oracle truth.
