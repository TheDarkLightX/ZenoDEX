#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${root}"

bash scripts/check_zeno_oracle_mvp.sh
pytest -q tests/test_zenodex_oracle_devnet_service.py tests/test_zenodex_oracle_devnet_disaster_harness.py
python3 tools/zenodex_oracle_devnet_disaster_harness.py --format text
python3 tools/zenodex_oracle_devnet_alpha_audit.py
