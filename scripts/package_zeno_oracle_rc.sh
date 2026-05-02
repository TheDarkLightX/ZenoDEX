#!/usr/bin/env bash
set -euo pipefail

version="${1:-zeno-oracle-mvp-rc1}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dist_dir="${root}/dist"
stage="${dist_dir}/${version}"

rm -rf "${stage}"
mkdir -p "${stage}/bin" "${stage}/tools" "${stage}/docs" "${stage}/scripts"

cp "${root}/bin/zenodex-oracle" "${stage}/bin/zenodex-oracle"
cp "${root}/README.md" "${stage}/README.md"
cp "${root}/requirements-core.txt" "${stage}/requirements-core.txt"
cp "${root}/requirements-dev.txt" "${stage}/requirements-dev.txt"
cp "${root}/scripts/check_zeno_oracle_mvp.sh" "${stage}/scripts/check_zeno_oracle_mvp.sh"
cp "${root}/scripts/package_zeno_oracle_rc.sh" "${stage}/scripts/package_zeno_oracle_rc.sh"

find "${root}/tools" -maxdepth 1 -type f -name 'zenodex_oracle*.py' -print0 |
  sort -z |
  xargs -0 -I{} cp "{}" "${stage}/tools/"

find "${root}/docs" -maxdepth 1 -type f -name 'ZENO_ORACLE*.md' -print0 |
  sort -z |
  xargs -0 -I{} cp "{}" "${stage}/docs/"

chmod +x "${stage}/tools/zenodex_oracle_cli.py"
chmod +x "${stage}/bin/zenodex-oracle"
chmod +x "${stage}/scripts/check_zeno_oracle_mvp.sh"
chmod +x "${stage}/scripts/package_zeno_oracle_rc.sh"

commit="$(git -C "${root}" rev-parse HEAD 2>/dev/null || printf 'unknown')"
created_utc="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

python3 - "$stage" "$version" "$commit" "$created_utc" <<'PY'
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

stage = Path(sys.argv[1])
version = sys.argv[2]
commit = sys.argv[3]
created_utc = sys.argv[4]

files = []
for path in sorted(p for p in stage.rglob("*") if p.is_file()):
    rel = path.relative_to(stage).as_posix()
    if rel == "ZEN_ORACLE_RC_MANIFEST.json":
        continue
    data = path.read_bytes()
    files.append(
        {
            "path": rel,
            "size_bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest(),
        }
    )

manifest = {
    "schema": "zenodex.oracle.rc_manifest.v1",
    "version": version,
    "source_commit": commit,
    "created_utc": created_utc,
    "entrypoint": "bin/zenodex-oracle",
    "python_entrypoint": "tools/zenodex_oracle_cli.py",
    "local_gate": "scripts/check_zeno_oracle_mvp.sh",
    "file_count": len(files),
    "files": files,
    "not_claimed": [
        "does_not_claim_live_oracle_network",
        "does_not_claim_onchain_feed_governance",
        "does_not_claim_platform_native_binary",
    ],
}
text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
(stage / "ZEN_ORACLE_RC_MANIFEST.json").write_text(text, encoding="utf-8")
PY

tarball="${dist_dir}/${version}.tar.gz"
rm -f "${tarball}"
tar -C "${dist_dir}" -czf "${tarball}" "${version}"
python3 - "$tarball" <<'PY'
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
data = path.read_bytes()
receipt = {
    "schema": "zenodex.oracle.rc_package_receipt.v1",
    "path": str(path),
    "size_bytes": len(data),
    "sha256": hashlib.sha256(data).hexdigest(),
}
print(json.dumps(receipt, indent=2, sort_keys=True))
PY
