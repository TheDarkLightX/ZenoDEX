#!/usr/bin/env bash
set -euo pipefail

version="${1:-zeno-oracle-mvp-rc1}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dist_dir="${root}/dist"
stage="${dist_dir}/${version}"

rm -rf "${stage}"
mkdir -p "${stage}/bin" "${stage}/tools" "${stage}/docs" "${stage}/scripts" "${stage}/assets/branding"
mkdir -p "${stage}/.github/workflows"

cp "${root}/bin/zenodex-oracle" "${stage}/bin/zenodex-oracle"
cp "${root}/.github/workflows/zeno-oracle-mvp.yml" "${stage}/.github/workflows/zeno-oracle-mvp.yml"
cp "${root}/README.md" "${stage}/README.md"
cp "${root}/requirements-core.txt" "${stage}/requirements-core.txt"
cp "${root}/requirements-dev.txt" "${stage}/requirements-dev.txt"
cp "${root}/scripts/check_zeno_oracle_mvp.sh" "${stage}/scripts/check_zeno_oracle_mvp.sh"
cp "${root}/scripts/check_zeno_oracle_devnet_alpha.sh" "${stage}/scripts/check_zeno_oracle_devnet_alpha.sh"
cp "${root}/scripts/check_zeno_oracle_rc_bundle.sh" "${stage}/scripts/check_zeno_oracle_rc_bundle.sh"
cp "${root}/scripts/package_zeno_oracle_rc.sh" "${stage}/scripts/package_zeno_oracle_rc.sh"
cp -R "${root}/assets/branding/zeno-oracle" "${stage}/assets/branding/zeno-oracle"
cp "${root}/tools/check_zeno_oracle_critical_action_map.py" "${stage}/tools/check_zeno_oracle_critical_action_map.py"
cp "${root}/tools/check_zeno_oracle_rc_package.py" "${stage}/tools/check_zeno_oracle_rc_package.py"
cp "${root}/tools/check_disaster_obligation_certificate.py" "${stage}/tools/check_disaster_obligation_certificate.py"
cp "${root}/tools/check_claims_registry.py" "${stage}/tools/check_claims_registry.py"
cp "${root}/tools/check_zeno_oracle_disaster_frontier.py" "${stage}/tools/check_zeno_oracle_disaster_frontier.py"
cp "${root}/tools/check_zeno_oracle_frontier_obligation_projection.py" "${stage}/tools/check_zeno_oracle_frontier_obligation_projection.py"
cp "${root}/tools/check_zeno_oracle_goal_completion_audit.py" "${stage}/tools/check_zeno_oracle_goal_completion_audit.py"
cp "${root}/tools/check_zeno_oracle_live_economics_policy.py" "${stage}/tools/check_zeno_oracle_live_economics_policy.py"
cp "${root}/tools/check_zenoproof_production_governance_policy.py" "${stage}/tools/check_zenoproof_production_governance_policy.py"
cp "${root}/tools/zeno_oracle_disaster_class_corpus.py" "${stage}/tools/zeno_oracle_disaster_class_corpus.py"
cp "${root}/tools/zeno_oracle_o3_receipt_flow_replay.py" "${stage}/tools/zeno_oracle_o3_receipt_flow_replay.py"
cp "${root}/tools/zeno_oracle_disaster_obligation_certificate_manifest.json" "${stage}/tools/zeno_oracle_disaster_obligation_certificate_manifest.json"
cp "${root}/tools/zeno_oracle_math_witness_sweep.jl" "${stage}/tools/zeno_oracle_math_witness_sweep.jl"
cp -R "${root}/tools/macos_scout" "${stage}/tools/macos_scout"
cp -R "${root}/tools/confidential_attestation_verifier_rust" "${stage}/tools/confidential_attestation_verifier_rust"
cp -R "${root}/tools/intent_lattices" "${stage}/tools/intent_lattices"
cp -R "${root}/tools/batch_auction_ifql_sources" "${stage}/tools/batch_auction_ifql_sources"

find "${root}/tools" -maxdepth 1 -type f -name 'zenodex_oracle*.py' -print0 |
  sort -z |
  xargs -0 -I{} cp "{}" "${stage}/tools/"

find "${root}/tools" -maxdepth 1 -type f -print0 |
  sort -z |
  xargs -0 -I{} cp "{}" "${stage}/tools/"

cp -R "${root}/docs/." "${stage}/docs/"
cp -R "${root}/src" "${stage}/src"
cp -R "${root}/tests" "${stage}/tests"
cp -R "${root}/generated" "${stage}/generated"
cp -R "${root}/formal" "${stage}/formal"
mkdir -p "${stage}/zk"
cp -R "${root}/zk/state_proof_risc0" "${stage}/zk/state_proof_risc0"
mkdir -p "${stage}/lean-mathlib"
cp "${root}/lean-mathlib/Proofs.lean" "${stage}/lean-mathlib/Proofs.lean"
cp -R "${root}/lean-mathlib/Proofs" "${stage}/lean-mathlib/Proofs"
cp -R "${root}/lean-mathlib/proof_receipts" "${stage}/lean-mathlib/proof_receipts"

mkdir -p "${stage}/docs/papers"
cp -R "${root}/docs/papers/zeno-oracle-whitepaper" "${stage}/docs/papers/zeno-oracle-whitepaper"

find "${stage}" -type d -name '__pycache__' -prune -exec rm -rf {} +
find "${stage}/zk" -type d -name 'target' -prune -exec rm -rf {} +
find "${stage}" -type f -name '*.pyc' -delete

chmod +x "${stage}/tools/zenodex_oracle_cli.py"
chmod +x "${stage}/tools/zenodex_oracle_devnet_disaster_harness.py"
chmod +x "${stage}/tools/zenodex_oracle_reporter_economics_replay.py"
chmod +x "${stage}/tools/zenodex_oracle_reporter_token_settlement_replay.py"
chmod +x "${stage}/tools/check_zeno_oracle_critical_action_map.py"
chmod +x "${stage}/tools/check_zeno_oracle_rc_package.py"
chmod +x "${stage}/tools/check_disaster_obligation_certificate.py"
chmod +x "${stage}/tools/check_claims_registry.py"
chmod +x "${stage}/tools/check_zeno_oracle_disaster_frontier.py"
chmod +x "${stage}/tools/check_zeno_oracle_frontier_obligation_projection.py"
chmod +x "${stage}/tools/check_zeno_oracle_goal_completion_audit.py"
chmod +x "${stage}/tools/check_zeno_oracle_live_economics_policy.py"
chmod +x "${stage}/tools/check_zenoproof_production_governance_policy.py"
chmod +x "${stage}/tools/zeno_oracle_disaster_class_corpus.py"
chmod +x "${stage}/tools/zeno_oracle_o3_receipt_flow_replay.py"
find "${stage}/tools/macos_scout" -type f \( -name '*.py' -o -name '*.sh' \) -exec chmod +x {} +
find "${stage}/tools/confidential_attestation_verifier_rust" -type d -name 'target' -prune -exec rm -rf {} +
chmod +x "${stage}/bin/zenodex-oracle"
chmod +x "${stage}/scripts/check_zeno_oracle_mvp.sh"
chmod +x "${stage}/scripts/check_zeno_oracle_devnet_alpha.sh"
chmod +x "${stage}/scripts/check_zeno_oracle_rc_bundle.sh"
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
    "product_name": "Zeno Oracle",
    "branding": {
        "icon_256": "assets/branding/zeno-oracle/zeno_oracle_icon_256.png",
        "icon_512": "assets/branding/zeno-oracle/zeno_oracle_icon_512.png",
        "favicon": "assets/branding/zeno-oracle/zeno_oracle_favicon.ico",
        "vector_icon": "assets/branding/zeno-oracle/zeno_oracle_icon_embedded.svg",
        "transparent_logo": "assets/branding/zeno-oracle/zeno_oracle_full_transparent_1024.png"
    },
    "whitepaper": "docs/papers/zeno-oracle-whitepaper/main.pdf",
    "whitepaper_author": "Dana Edwards",
    "local_gate": "scripts/check_zeno_oracle_mvp.sh",
    "devnet_alpha_gate": "scripts/check_zeno_oracle_devnet_alpha.sh",
    "package_replay_gate": "scripts/check_zeno_oracle_rc_bundle.sh",
    "file_count": len(files),
    "files": files,
    "not_claimed": [
        "does_not_claim_production_oracle_network",
        "does_not_claim_onchain_feed_governance",
        "does_not_claim_live_public_reporter_economics",
        "does_not_claim_platform_native_binary",
        "does_not_claim_production_code_signing",
        "does_not_claim_production_zenoproof_governance",
        "does_not_claim_generalized_math_proof_completion",
    ],
}
text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
(stage / "ZEN_ORACLE_RC_MANIFEST.json").write_text(text, encoding="utf-8")
PY

tarball="${dist_dir}/${version}.tar.gz"
rm -f "${tarball}"
tar -C "${dist_dir}" -czf "${tarball}" "${version}"
python3 - "$tarball" "${dist_dir}/${version}.receipt.json" "${dist_dir}/${version}.sig" <<'PY'
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
receipt_path = Path(sys.argv[2])
signature_path = Path(sys.argv[3])
data = path.read_bytes()
sha256 = hashlib.sha256(data).hexdigest()
signature_payload = f"zenodex-oracle-devnet-alpha-rc:{sha256}".encode("utf-8")
signature = hashlib.sha256(signature_payload).hexdigest()
receipt = {
    "schema": "zenodex.oracle.rc_package_receipt.v1",
    "path": str(path),
    "size_bytes": len(data),
    "sha256": sha256,
    "signature_schema": "zenodex.oracle.devnet_package_signature.v1",
    "signature": signature,
    "signature_note": "devnet integrity signature, not production code signing",
}
text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
receipt_path.write_text(text, encoding="utf-8")
signature_path.write_text(signature + "\n", encoding="utf-8")
print(text, end="")
PY
