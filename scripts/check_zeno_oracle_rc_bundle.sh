#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${root}"

export PYTHONDONTWRITEBYTECODE="${PYTHONDONTWRITEBYTECODE:-1}"

python3 tools/zenodex_oracle_cli.py doctor
python3 tools/zeno_oracle_o3_receipt_flow_replay.py --format text
python3 tools/zenodex_oracle_reporter_economics_replay.py self-test
python3 tools/zenodex_oracle_reporter_token_settlement_replay.py self-test
python3 tools/check_zeno_oracle_live_economics_policy.py --format text
python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text
python3 tools/zeno_oracle_disaster_class_corpus.py --format text
python3 tools/check_disaster_obligation_certificate.py --manifest tools/zeno_oracle_disaster_obligation_certificate_manifest.json
python3 tools/check_zeno_oracle_disaster_frontier.py --format text
python3 tools/check_zeno_oracle_frontier_obligation_projection.py --format text
python3 tools/check_zenoproof_production_governance_policy.py --format text
python3 tools/check_claims_registry.py
python3 tools/check_zeno_oracle_goal_completion_audit.py --format text --expect-blocked
python3 tools/check_zeno_oracle_rc_package.py --package-dir "${root}" --local-only-manifest-check

if command -v julia >/dev/null 2>&1; then
  julia tools/zeno_oracle_math_witness_sweep.jl --json >/tmp/zeno_oracle_rc_bundle_julia_math_witness.json
  python3 - <<'PY'
from __future__ import annotations

import json
from pathlib import Path

receipt = json.loads(Path("/tmp/zeno_oracle_rc_bundle_julia_math_witness.json").read_text(encoding="utf-8"))
if receipt.get("status") != "accepted":
    raise SystemExit("julia_math_witness_rejected")
print(
    "julia_math_witness_status = "
    f"{receipt['status']} case_count={receipt['case_count']} failed_count={receipt['failed_count']}"
)
PY
else
  printf '%s\n' 'julia_math_witness_status = skipped_missing_julia'
fi
