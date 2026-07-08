# ZenoOracle Workflow Evidence Status

Status: first public workflow status check, bounded smoke evidence only.

Replay:

```bash
python3 tools/zeno_oracle_workflow_evidence_status.py --format text
```

Expected receipt:

```text
lane_count = 4
accepted_lane_count = 4
failed_lane_count = 0
status = accepted
```

The checker covers these public artifact lanes:

- TLA Oracle recovery lifecycle artifacts and replay command.
- LTLf Oracle recovery artifacts and replay command.
- ESSO zUSD Oracle recovery lifecycle artifacts and replay command.
- Temporary PopperPad append-only smoke using `tools/popper_pad.py`.

Morph oracle-clamp envelope checks are external research evidence and are not a
ZenoDEX runtime or release dependency.
TLA, LTLf, and ESSO replay commands remain documented external formal-tool
checks; they are not generated as hermetic ZenoProof self-test profiles unless
their toolchains are installed by the runner.

This lane is a status and smoke boundary. It does not publish private
PopperPad content, execute external Morph/TLA/LTLf/ESSO runners, or certify
production oracle truth.
