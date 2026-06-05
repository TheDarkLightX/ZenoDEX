from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

import tools.check_kernel_assurance_public_receipt as kar
from tools.check_kernel_assurance_public_receipt import (
    build_public_receipt_from_report,
    check_receipt_file,
    verify_public_receipt,
)

_PRIVATE_WORKSPACE_PREFIX = "/private/" + "workspace"
ROOT = Path(__file__).resolve().parents[1]


def _write_json(path: Path, obj: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _manifest() -> dict[str, Any]:
    kani = kar.EXPECTED_KANI_PROOFS["balance_kernel_kani"]
    lean = kar.EXPECTED_LEAN_PROOFS["nonce_batch_wrapper_lean"]
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
        "kani_proofs": [
            {
                "id": "balance_kernel_kani",
                "tool": kani["tool"],
                "package": kani["package"],
                "working_directory": kani["working_directory"],
                "cargo_kani_version": kani["cargo_kani_version"],
                "harness_timeout": kani["harness_timeout"],
                "required_verdict": kani["required_verdict"],
                "source_files": kani["source_files"],
                "harnesses": list(kani["harnesses"]),
            }
        ],
        "lean_proofs": [
            {
                "id": "nonce_batch_wrapper_lean",
                "tool": lean["tool"],
                "module": lean["module"],
                "required_verdict": lean["required_verdict"],
                "source_files": lean["source_files"],
                "required_theorems": lean["required_theorems"],
            }
        ],
    }


def _manifest_hash(manifest: dict[str, Any], tmp_path: Path) -> tuple[str, Path]:
    manifest_path = tmp_path / "kernel_assurance_manifest.json"
    _write_json(manifest_path, manifest)
    from tools.check_kernel_assurance_public_receipt import _sha256_file

    return _sha256_file(manifest_path), manifest_path


def _private_report(manifest_sha256: str) -> dict[str, Any]:
    kani = kar.EXPECTED_KANI_PROOFS["balance_kernel_kani"]
    lean = kar.EXPECTED_LEAN_PROOFS["nonce_batch_wrapper_lean"]
    return {
        "ok": True,
        "manifest_sha256": manifest_sha256,
        "toolchain": {
            "esso_code_hash": "1145cf77668b6d86cda83d79820b13a65fbde12f",
            "esso_tree_sha256": "463ba86b72ffb345a435cf9fff8e6dd51a7385e0faffa7b53490b195a143c336",
            "esso_dirty": False,
            "esso_dirty_entries": [],
        },
        "repo_root": f"{_PRIVATE_WORKSPACE_PREFIX}/path/that/must/not/be/copied",
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
                    "evidence_bundle": {"bundle_dir": f"{_PRIVATE_WORKSPACE_PREFIX}/internal/bundle"},
                },
            }
        ],
        "kani_proofs": [
            {
                "id": "balance_kernel_kani",
                "tool": kani["tool"],
                "package": kani["package"],
                "working_directory": kani["working_directory"],
                "source_files": [
                    {"path": rel, "sha256": kar._sha256_file(ROOT / rel)}
                    for rel in kani["source_files"]
                ],
                "result": {
                    "verdict": "VERIFIED",
                    "cargo_kani_version": kani["cargo_kani_version"],
                    "package": kani["package"],
                    "working_directory": kani["working_directory"],
                    "command": kar._kani_command(kani),
                    "harnesses": [
                        {
                            "name": name,
                            "verdict": "VERIFIED",
                            **expected,
                        }
                        for name, expected in kani["harnesses"].items()
                    ],
                    "summary": {
                        "successfully_verified": len(kani["harnesses"]),
                        "failures": 0,
                        "total": len(kani["harnesses"]),
                    },
                },
            }
        ],
        "lean_proofs": [
            {
                "id": "nonce_batch_wrapper_lean",
                "tool": lean["tool"],
                "module": lean["module"],
                "source_files": [
                    {"path": rel, "sha256": kar._sha256_file(ROOT / rel)}
                    for rel in lean["source_files"]
                ],
                "result": {
                    "verdict": "BUILT_NO_SORRY",
                    "lean_toolchain": lean["expected_lean_toolchain"],
                    "module": lean["module"],
                    "required_theorems": lean["required_theorems"],
                },
            }
        ],
    }


def _reseal(receipt: dict[str, Any]) -> None:
    receipt["receipt_sha256"] = kar._sha256_bytes(kar._canonical_json_bytes(kar._receipt_hash_body(receipt)))


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


def test_committed_receipt_covers_balance_kernel_kani() -> None:
    report = check_receipt_file(
        receipt_path=ROOT / "docs/assurance/kernel_assurance_public_receipt.json",
        manifest_path=ROOT / "tools/kernel_assurance_manifest.json",
    )
    assert report["ok"] is True, report["errors"]

    receipt = json.loads(
        (ROOT / "docs/assurance/kernel_assurance_public_receipt.json").read_text(encoding="utf-8")
    )
    proofs = {entry["id"]: entry for entry in receipt["kani_proofs"]}
    proof = proofs["balance_kernel_kani"]
    assert proof["source_files"] == [
        {
            "path": "rust-runtime/crates/zenodex-runtime-core/src/balance_kernel.rs",
            "sha256": kar._sha256_file(
                ROOT / "rust-runtime/crates/zenodex-runtime-core/src/balance_kernel.rs"
            ),
        }
    ]
    assert proof["result"]["verdict"] == "VERIFIED"
    assert proof["result"]["summary"] == {"failures": 0, "successfully_verified": 7, "total": 7}


def test_committed_receipt_covers_nonce_batch_wrapper_lean() -> None:
    report = check_receipt_file(
        receipt_path=ROOT / "docs/assurance/kernel_assurance_public_receipt.json",
        manifest_path=ROOT / "tools/kernel_assurance_manifest.json",
    )
    assert report["ok"] is True, report["errors"]

    receipt = json.loads(
        (ROOT / "docs/assurance/kernel_assurance_public_receipt.json").read_text(encoding="utf-8")
    )
    proofs = {entry["id"]: entry for entry in receipt["lean_proofs"]}
    proof = proofs["nonce_batch_wrapper_lean"]
    assert proof["source_files"] == [
        {
            "path": "lean-mathlib/Proofs/ZenoDEXNonceBatchWrapper.lean",
            "sha256": kar._sha256_file(
                ROOT / "lean-mathlib/Proofs/ZenoDEXNonceBatchWrapper.lean"
            ),
        }
    ]
    assert proof["result"]["verdict"] == "BUILT_NO_SORRY"
    assert (
        "Proofs.ZenoDEX.NonceBatchWrapper.batch_accept_decision_implies_safety"
        in proof["result"]["required_theorems"]
    )
    assert (
        "Proofs.ZenoDEX.NonceBatchWrapper.canonical_batch_accept_decision_implies_safety"
        in proof["result"]["required_theorems"]
    )


def test_lean_theorem_smoke_source_names_every_pinned_theorem() -> None:
    lean = kar.EXPECTED_LEAN_PROOFS["nonce_batch_wrapper_lean"]
    source = kar._lean_required_theorem_check_source(
        lean["module"],
        list(lean["required_theorems"]),
    )

    assert source.startswith(f"import {lean['module']}\n")
    for theorem_name in lean["required_theorems"]:
        assert f"#check {theorem_name}\n" in source


def test_run_lean_proof_invokes_required_theorem_smoke(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[list[str]] = []

    class _Proc:
        returncode = 0
        stdout = ""
        stderr = ""

    def fake_run(command: list[str], **_kwargs: Any) -> _Proc:
        calls.append(command)
        return _Proc()

    monkeypatch.setattr(kar.subprocess, "run", fake_run)

    proof = kar._run_lean_proof(_manifest()["lean_proofs"][0])

    assert proof["result"]["verdict"] == "BUILT_NO_SORRY"
    assert any(command[:3] == ["lake", "env", "lean"] for command in calls)


def test_build_rejects_kani_manifest_harness_drop_before_toolchain(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    manifest["kani_proofs"][0]["harnesses"] = manifest["kani_proofs"][0]["harnesses"][:-1]

    with pytest.raises(kar.ReceiptError, match="source-pinned"):
        build_public_receipt_from_report(
            _private_report(manifest_sha256),
            manifest=manifest,
            manifest_sha256=manifest_sha256,
        )


def test_build_rejects_lean_manifest_theorem_drop_before_toolchain(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    manifest["lean_proofs"][0]["required_theorems"] = manifest["lean_proofs"][0]["required_theorems"][:-1]

    with pytest.raises(kar.ReceiptError, match="source-pinned"):
        build_public_receipt_from_report(
            _private_report(manifest_sha256),
            manifest=manifest,
            manifest_sha256=manifest_sha256,
        )


def test_resealed_kani_verdict_downgrade_fails(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    receipt = build_public_receipt_from_report(
        _private_report(manifest_sha256),
        manifest=manifest,
        manifest_sha256=manifest_sha256,
    )

    receipt["kani_proofs"][0]["result"]["verdict"] = "UNKNOWN"
    _reseal(receipt)
    errors = verify_public_receipt(receipt, manifest=manifest, manifest_sha256=manifest_sha256)

    assert any("verdict" in error for error in errors), errors


def test_resealed_kani_cover_downgrade_fails(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    receipt = build_public_receipt_from_report(
        _private_report(manifest_sha256),
        manifest=manifest,
        manifest_sha256=manifest_sha256,
    )

    receipt["kani_proofs"][0]["result"]["harnesses"][0]["cover_properties_satisfied"] = 0
    _reseal(receipt)
    errors = verify_public_receipt(receipt, manifest=manifest, manifest_sha256=manifest_sha256)

    assert any("cover_properties_satisfied" in error for error in errors), errors


def test_resealed_kani_missing_harness_fails(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    receipt = build_public_receipt_from_report(
        _private_report(manifest_sha256),
        manifest=manifest,
        manifest_sha256=manifest_sha256,
    )

    receipt["kani_proofs"][0]["result"]["harnesses"] = receipt["kani_proofs"][0]["result"]["harnesses"][:-1]
    receipt["kani_proofs"][0]["result"]["summary"]["successfully_verified"] = 6
    receipt["kani_proofs"][0]["result"]["summary"]["total"] = 6
    _reseal(receipt)
    errors = verify_public_receipt(receipt, manifest=manifest, manifest_sha256=manifest_sha256)

    assert any("result harnesses" in error for error in errors), errors


@pytest.mark.parametrize(
    ("mutator", "expected"),
    [
        (
            lambda receipt: receipt["kani_proofs"][0]["result"].update(
                {"raw_stdout": f"{_PRIVATE_WORKSPACE_PREFIX}/secret.log"}
            ),
            "unexpected public field",
        ),
        (
            lambda receipt: receipt["kani_proofs"][0]["result"]["harnesses"][0].update(
                {"raw_stdout": f"{_PRIVATE_WORKSPACE_PREFIX}/secret.log"}
            ),
            "unexpected public field",
        ),
        (
            lambda receipt: receipt["kani_proofs"][0]["result"]["summary"].update(
                {"xfailed": 1}
            ),
            "unexpected public field",
        ),
    ],
)
def test_resealed_kani_extra_result_fields_fail(
    tmp_path: Path,
    mutator: Any,
    expected: str,
) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    receipt = build_public_receipt_from_report(
        _private_report(manifest_sha256),
        manifest=manifest,
        manifest_sha256=manifest_sha256,
    )

    mutator(receipt)
    _reseal(receipt)
    errors = verify_public_receipt(receipt, manifest=manifest, manifest_sha256=manifest_sha256)

    assert any(expected in error for error in errors), errors


def test_resealed_lean_theorem_drop_fails(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    receipt = build_public_receipt_from_report(
        _private_report(manifest_sha256),
        manifest=manifest,
        manifest_sha256=manifest_sha256,
    )

    receipt["lean_proofs"][0]["result"]["required_theorems"] = (
        receipt["lean_proofs"][0]["result"]["required_theorems"][:-1]
    )
    _reseal(receipt)
    errors = verify_public_receipt(receipt, manifest=manifest, manifest_sha256=manifest_sha256)

    assert any("required_theorems" in error for error in errors), errors


def test_resealed_lean_extra_result_field_fails(tmp_path: Path) -> None:
    manifest = _manifest()
    manifest_sha256, _manifest_path = _manifest_hash(manifest, tmp_path)
    receipt = build_public_receipt_from_report(
        _private_report(manifest_sha256),
        manifest=manifest,
        manifest_sha256=manifest_sha256,
    )

    receipt["lean_proofs"][0]["result"]["raw_stdout"] = f"{_PRIVATE_WORKSPACE_PREFIX}/secret.log"
    _reseal(receipt)
    errors = verify_public_receipt(receipt, manifest=manifest, manifest_sha256=manifest_sha256)

    assert any("unexpected public field" in error for error in errors), errors
