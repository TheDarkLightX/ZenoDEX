#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${root}"

bash scripts/check_zeno_oracle_mvp.sh
python3 tools/check_zeno_oracle_critical_action_map.py
python3 tools/zeno_oracle_o3_receipt_flow_replay.py --format text
pytest -q tests/test_zeno_oracle_o3_receipt_flow_replay.py
pytest -q tests/test_zenodex_oracle_devnet_service.py tests/test_zenodex_oracle_devnet_disaster_harness.py
python3 tools/zenodex_oracle_reporter_economics_replay.py self-test
python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text
python3 tools/zeno_oracle_disaster_class_corpus.py --format text
python3 tools/check_disaster_obligation_certificate.py --manifest tools/zeno_oracle_disaster_obligation_certificate_manifest.json
python3 tools/zeno_oracle_workflow_evidence_status.py --format text
python3 tools/zenodex_oracle_devnet_alpha_audit.py
