from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from tools.check_kernel_assurance_public_receipt import (
    build_public_receipt_from_report,
    check_receipt_file,
    verify_public_receipt,
)


def _write_json(path: Path, obj: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _manifest() -> dict[str, Any]:
    return {
        "manifest_version": 1,
        "solvers": ["cvc5"],
        "timeout_ms": 30000,
        "determinism_trials": 2,
        "seeds": [0, 1],
        "toolchain": {
            "esso_code_hash": "1145cf77668b6d86cda83d79820b13a65fbde12f",
            "esso_tree_sha256": "463ba86b72ffb345a435cf9fff8e6dd51a7385e0faffa7b53490b195a143c336",
            "solvers": {"cvc5": "This is cvc5 version 1.1.2"},
        },
        "kernels": [
            {
                "model_id": "cpmm_swap",
                "kernel_path": "src/kernels/dex/cpmm_swap.yaml",
                "expected_ir_hash": "sha256:95dd8740ce38b990736bdf59d060104a5626f429181a3414b0a6085101f71d73",
                "ce_corpus_path": "src/kernels/dex/ce_corpus_cpmm_swap.jsonl",
                "expected_ce_corpus_sha256": "0a97f7a5ebe6843e2071e9d11227173cee0e4493b37f7a07a453c6b49ab2bd76",
            }
        ],
    }


def _manifest_hash(manifest: dict[str, Any], tmp_path: Path) -> tuple[str, Path]:
    manifest_path = tmp_path / "kernel_assurance_manifest.json"
    _write_json(manifest_path, manifest)
    from tools.check_kernel_assurance_public_receipt import _sha256_file

    return _sha256_file(manifest_path), manifest_path


def _private_report(manifest_sha256: str) -> dict[str, Any]:
    return {
        "ok": True,
        "manifest_sha256": manifest_sha256,
        "toolchain": {
            "esso_code_hash": "1145cf77668b6d86cda83d79820b13a65fbde12f",
            "esso_tree_sha256": "463ba86b72ffb345a435cf9fff8e6dd51a7385e0faffa7b53490b195a143c336",
            "esso_dirty": False,
            "esso_dirty_entries": [],
        },
        "repo_root": "/private/workspace/path/that/must/not/be/copied",
        "kernels": [
            {
                "model_id": "cpmm_swap",
                "kernel_path": "src/kernels/dex/cpmm_swap.yaml",
                "ir_hash": "sha256:95dd8740ce38b990736bdf59d060104a5626f429181a3414b0a6085101f71d73",
                "ce_corpus_path": "src/kernels/dex/ce_corpus_cpmm_swap.jsonl",
                "ce_corpus_sha256": "0a97f7a5ebe6843e2071e9d11227173cee0e4493b37f7a07a453c6b49ab2bd76",
                "corpus_stats": {
                    "total": 200,
                    "per_action": {"swap_x_for_y": 100, "swap_y_for_x": 100},
                    "boundary_per_action": {"swap_x_for_y": 10, "swap_y_for_x": 10},
                    "unique_ids": 200,
                    "unique_signatures": 200,
                    "unique_signature_ratio": 1.0,
                },
                "verification": {
                    "tool_versions": {"solvers": {"cvc5": "This is cvc5 version 1.1.2"}},
                    "timeout_ms": 30000,
                    "determinism_trials": 2,
                    "seeds": [0, 1],
                    "fingerprint": "d8" * 32,
                    "elapsed_s": 12.5,
                    "evidence_bundle": {"bundle_dir": "/private/workspace/internal/bundle"},
                },
            }
        ],
    }


def test_build_and_verify_public_receipt_without_private_source(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    receipt = build_public_receipt_from_report(
        _private_report(manifest_sha256),
        manifest=manifest,
        manifest_sha256=manifest_sha256,
        source_report_sha256="ab" * 32,
    )

    assert receipt["ok"] is True
    assert receipt["private_toolchain_source_included"] is False
    assert "repo_root" not in json.dumps(receipt)
    assert "private/workspace" not in json.dumps(receipt)
    assert verify_public_receipt(receipt, manifest=manifest, manifest_sha256=manifest_sha256) == []


def test_receipt_rejects_manifest_hash_mismatch(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    receipt = build_public_receipt_from_report(
        _private_report(manifest_sha256),
        manifest=manifest,
        manifest_sha256=manifest_sha256,
    )

    errors = verify_public_receipt(receipt, manifest=manifest, manifest_sha256="00" * 32)

    assert any("manifest_sha256 mismatch" in error for error in errors)


def test_build_accepts_dirty_private_esso_checkout_when_tree_hash_matches(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    report = _private_report(manifest_sha256)
    report["toolchain"]["esso_dirty"] = True

    receipt = build_public_receipt_from_report(report, manifest=manifest, manifest_sha256=manifest_sha256)

    assert receipt["toolchain"]["esso_dirty"] is True
    assert "esso_dirty_entries" not in json.dumps(receipt)


def test_receipt_file_checker_accepts_and_rejects_tampering(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, manifest_path = _manifest_hash(manifest, tmp_path)
    receipt = build_public_receipt_from_report(
        _private_report(manifest_sha256),
        manifest=manifest,
        manifest_sha256=manifest_sha256,
    )
    receipt_path = tmp_path / "receipt.json"
    _write_json(receipt_path, receipt)

    assert check_receipt_file(receipt_path=receipt_path, manifest_path=manifest_path)["ok"] is True

    receipt["kernels"][0]["verification"]["fingerprint"] = "00" * 32
    _write_json(receipt_path, receipt)

    rejected = check_receipt_file(receipt_path=receipt_path, manifest_path=manifest_path)
    assert rejected["ok"] is False
    assert any("receipt_sha256 mismatch" in error for error in rejected["errors"])
