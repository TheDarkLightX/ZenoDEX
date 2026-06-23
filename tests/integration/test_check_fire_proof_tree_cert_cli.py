from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
CHECK_CLI = REPO_ROOT / "tools" / "check_fire_proof_tree_cert.py"


def _valid_payload() -> dict[str, object]:
    return {
        "version": "FIRE_CERT_RULES_v0.1",
        "object_hash": "sha256:" + ("1" * 64),
        "instance_hash": "sha256:" + ("2" * 64),
        "certificate_sha256": "sha256:" + ("4" * 64),
        "runtime_certificate_summary": {
            "root_rule": "min",
            "root_interval": {"lower": 0, "upper": 3},
            "node_count": 3,
            "exact_params": [{"name": "cap_index", "value": 3}],
            "source_bounds": [{"name": "burn_final", "lower": 0, "upper": 9}],
            "operator_tree": {
                "rule": "min",
                "lower": 0,
                "upper": 3,
                "children": [
                    {
                        "rule": "source_bound",
                        "name": "burn_final",
                        "lower": 0,
                        "upper": 9,
                        "children": [],
                    },
                    {
                        "rule": "exact_param",
                        "name": "cap_index",
                        "lower": 3,
                        "upper": 3,
                        "children": [],
                    },
                ],
            },
        },
        "dependency_hashes": [
            {
                "name": "burn_index_v1",
                "version": "1.0.0",
                "hash": "sha256:" + ("3" * 64),
            }
        ],
        "evidence_floor": "contract",
        "claims": {
            "BoundOK": {
                "evidence": "proved",
                "claim": "0 <= payoff <= cap",
                "root_node": "n_bound",
            },
            "CollateralOK": {
                "evidence": "contract",
                "claim": "writer collateral >= cap",
                "root_node": "n_collateral",
            },
        },
        "proof_tree": [
            {
                "id": "n_bound_expr_0",
                "rule": "source_bound",
                "claim": {
                    "predicate": "BoundLeafSourceBound",
                    "name": "burn_final",
                    "lower": "0",
                    "upper": "9",
                },
                "evidence": "proved",
            },
            {
                "id": "n_bound_expr_1",
                "rule": "exact_param",
                "claim": {
                    "predicate": "BoundLeafExactParam",
                    "name": "cap_index",
                    "value": "3",
                    "lower": "3",
                    "upper": "3",
                },
                "evidence": "proved",
            },
            {
                "id": "n_bound_expr",
                "rule": "interval_min",
                "claim": {"predicate": "BoundExpr", "runtime_rule": "min", "lower": "0", "upper": "3"},
                "inputs": ["n_bound_expr_0", "n_bound_expr_1"],
                "evidence": "proved",
            },
            {
                "id": "n_bound",
                "rule": "witness_bound_intro",
                "claim": {
                    "predicate": "BoundOK",
                    "lower": "0",
                    "upper": "3",
                    "runtime_root_rule": "min",
                    "runtime_node_count": "3",
                },
                "inputs": ["n_bound_expr"],
                "evidence": "proved",
            },
            {
                "id": "n_collateral",
                "rule": "collateral_one_sided_writer",
                "inputs": ["n_bound"],
                "claim": {"predicate": "CollateralOK"},
                "evidence": "contract",
            },
        ],
    }


def test_check_fire_proof_tree_cert_cli_roundtrip(tmp_path: Path) -> None:
    cert_file = tmp_path / "proof_tree_cert.json"
    payload = _valid_payload()
    cert_file.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--cert-file",
            str(cert_file),
            "--expected-object-hash",
            payload["object_hash"],
            "--expected-instance-hash",
            payload["instance_hash"],
            "--expected-certificate-sha256",
            payload["certificate_sha256"],
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["schema"] == "zenodex/fire-proof-tree-cert-check-report/v1"
    assert report["ok"] is True
    assert report["object_hash"] == payload["object_hash"]
    assert report["instance_hash"] == payload["instance_hash"]
    assert report["certificate_sha256"] == payload["certificate_sha256"]
    assert report["evidence_floor"] == "contract"
    assert report["schema_path"].endswith("src/fire/spec/fire-cert-rules.schema.json")


def test_check_fire_proof_tree_cert_cli_rejects_mismatched_object_hash(tmp_path: Path) -> None:
    cert_file = tmp_path / "proof_tree_cert.json"
    cert_file.write_text(json.dumps(_valid_payload(), indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--cert-file",
            str(cert_file),
            "--expected-object-hash",
            "sha256:" + ("9" * 64),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    error = json.loads(proc.stderr)
    assert error["ok"] is False
    assert error["error"] == "proof_tree_cert_object_hash_mismatch"


def test_check_fire_proof_tree_cert_cli_rejects_mismatched_certificate_sha256(tmp_path: Path) -> None:
    cert_file = tmp_path / "proof_tree_cert.json"
    payload = _valid_payload()
    cert_file.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CHECK_CLI),
            "--cert-file",
            str(cert_file),
            "--expected-certificate-sha256",
            "sha256:" + ("9" * 64),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    error = json.loads(proc.stderr)
    assert error["ok"] is False
    assert error["error"] == "proof_tree_cert_certificate_sha256_mismatch"
