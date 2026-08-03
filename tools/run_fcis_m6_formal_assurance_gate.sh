#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

python3 tools/build_fcis_m6_formal_source_manifest.py --check
sha256sum -c docs/research/FCIS_M6_FORMAL_SUITE_SOURCE_MANIFEST.sha256
python3 tools/check_fcis_m6_formal_specs.py --check
python3 tools/check_fcis_m6_formal_runtime_matrix.py

ESSO_ROOT="${ESSO_ROOT:-$ROOT/external/ESSO}"
if [[ -d "$ESSO_ROOT/ESSO" ]]; then
  while IFS= read -r model; do
    PYTHONPATH="$ESSO_ROOT" python3 -m ESSO validate "$model"
    PYTHONPATH="$ESSO_ROOT" python3 -m ESSO verify-multi "$model" --solvers z3,cvc5
  done < <(python3 - <<'PY'
import json
from pathlib import Path
manifest=json.loads(Path('formal/esso/fcis_m6_formal_suite_v1.json').read_text())
for item in manifest['models']:
    print(item['path'])
PY
)
elif [[ "${FCIS_REQUIRE_ESSO:-0}" == "1" ]]; then
  echo "ESSO toolchain not found at $ESSO_ROOT" >&2
  exit 2
else
  echo "ESSO toolchain unavailable; bounded independent replay passed, but no solver receipt was produced." >&2
fi
