from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest
import yaml

import tools.check_state_root_surface_evidence as sre

ROOT = Path(__file__).resolve().parents[1]
RECEIPT = ROOT / "docs" / "assurance" / "state_root_surface_evidence_receipt.json"
SPEC = ROOT / "src" / "kernels" / "dex" / "state_root_v5_scope_contract.json"


def _load_receipt() -> dict:
    return json.loads(RECEIPT.read_text(encoding="utf-8"))


def _reseal(receipt: dict) -> None:
    receipt["receipt_sha256"] = sre._sha256_bytes(sre._canonical_json_bytes(sre._receipt_hash_body(receipt)))


def _runtime_shadow_workflow() -> dict:
    workflow = yaml.safe_load(
        (ROOT / ".github" / "workflows" / "runtime-shadow.yml").read_text(encoding="utf-8")
    )
    assert isinstance(workflow, dict)
    return workflow


def _release_integrity_workflow() -> dict:
    workflow = yaml.safe_load(
        (ROOT / ".github" / "workflows" / "release-integrity.yml").read_text(encoding="utf-8")
    )
    assert isinstance(workflow, dict)
    return workflow


def test_committed_state_root_surface_receipt_verifies() -> None:
    report = sre.check_receipt_file(receipt_path=RECEIPT, spec_path=SPEC, run_required_tests=False)
    assert report["ok"] is True, report["errors"]
    assert report["schema"] == sre.CHECK_SCHEMA


def test_committed_receipt_covers_all_six_evidence_columns() -> None:
    receipt = _load_receipt()
    assert receipt["schema"] == sre.RECEIPT_SCHEMA
    assert receipt["private_toolchain_source_included"] is False
    assert set(receipt["evidence_columns"]) == {
        "running_impl",
        "formal_spec",
        "proof_artifact",
        "differential_tests",
        "runtime_invariants",
        "authority_mode",
    }
    assert receipt["evidence_columns"]["proof_artifact"]["kani"]["verdict"] == "VERIFIED"
    assert receipt["evidence_columns"]["proof_artifact"]["preimage_injectivity"]["ok"] is True


def test_resealed_source_hash_tamper_fails() -> None:
    receipt = _load_receipt()
    receipt["source_files"][0]["sha256"] = "0" * 64
    _reseal(receipt)
    errors = sre.verify_receipt(receipt, spec_path=SPEC)
    assert any("source hash drift" in err for err in errors), errors


def test_resealed_kani_harness_drop_fails() -> None:
    receipt = _load_receipt()
    receipt["evidence_columns"]["proof_artifact"]["kani"]["harnesses"] = receipt["evidence_columns"][
        "proof_artifact"
    ]["kani"]["harnesses"][:-1]
    _reseal(receipt)
    errors = sre.verify_receipt(receipt, spec_path=SPEC)
    assert any("harness" in err for err in errors), errors


def test_resealed_proof_verdict_downgrade_fails() -> None:
    receipt = _load_receipt()
    receipt["evidence_columns"]["proof_artifact"]["verdict"] = "CLAIMED"
    _reseal(receipt)
    errors = sre.verify_receipt(receipt, spec_path=SPEC)
    assert any("proof_artifact verdict" in err for err in errors), errors


@pytest.mark.parametrize(
    ("mutate", "needle"),
    (
        (
            lambda receipt: receipt.update({"private_path": "/private/workspace/secret"}),
            "unexpected public field",
        ),
        (
            lambda receipt: receipt["evidence_columns"]["running_impl"].update(
                {"private_path": "/private/workspace/secret"}
            ),
            "unexpected public field",
        ),
        (
            lambda receipt: receipt["evidence_columns"]["proof_artifact"].update(
                {"private_path": "/private/workspace/secret"}
            ),
            "unexpected public field",
        ),
        (
            lambda receipt: receipt["evidence_columns"]["proof_artifact"]["kani"].update(
                {"raw_stdout": "/private/workspace/secret.log"}
            ),
            "unexpected public field",
        ),
        (
            lambda receipt: receipt["evidence_columns"]["proof_artifact"]["kani"]["harnesses"][0].update(
                {"raw_stdout": "/private/workspace/secret.log"}
            ),
            "unexpected public field",
        ),
        (
            lambda receipt: receipt["source_files"][0].update(
                {"private_path": "/private/workspace/secret"}
            ),
            "unexpected public field",
        ),
    ),
)
def test_resealed_extra_state_root_receipt_fields_fail(mutate, needle: str) -> None:
    """Review regression: accepted state-root receipts use an exact public schema."""
    receipt = _load_receipt()
    mutate(receipt)
    _reseal(receipt)
    errors = sre.verify_receipt(receipt, spec_path=SPEC)
    assert any(needle in err for err in errors), errors


def test_malformed_evidence_column_fails_with_error() -> None:
    receipt = _load_receipt()
    receipt["evidence_columns"]["running_impl"] = "not-an-object"
    _reseal(receipt)
    errors = sre.verify_receipt(receipt, spec_path=SPEC)
    assert any("running_impl must be an object" in err for err in errors), errors


def test_weakened_formal_spec_fails(tmp_path: Path) -> None:
    weakened = json.loads(SPEC.read_text(encoding="utf-8"))
    weakened["root_formula"]["section_order"] = ["BAL", "POL", "LPB", "LPA", "NNC"]
    spec_path = tmp_path / "state_root_v5_scope_contract.json"
    spec_path.write_text(json.dumps(weakened, indent=2, sort_keys=True), encoding="utf-8")

    report = sre.check_receipt_file(receipt_path=RECEIPT, spec_path=spec_path)
    assert report["ok"] is False
    assert any("section_order" in err or "included_sections" in err for err in report["errors"])


def test_swapped_pool_reserve_spec_body_fails(tmp_path: Path) -> None:
    weakened = json.loads(SPEC.read_text(encoding="utf-8"))
    pol = list(weakened["included_sections"]["POL"])
    i0, i1 = pol.index("reserve0:uvarint"), pol.index("reserve1:uvarint")
    pol[i0], pol[i1] = pol[i1], pol[i0]
    weakened["included_sections"]["POL"] = pol
    spec_path = tmp_path / "state_root_v5_scope_contract.json"
    spec_path.write_text(json.dumps(weakened, indent=2, sort_keys=True), encoding="utf-8")

    report = sre.check_receipt_file(
        receipt_path=RECEIPT,
        spec_path=spec_path,
        run_required_tests=False,
    )
    assert report["ok"] is False
    assert any("section-body encoding" in err for err in report["errors"])


def test_empty_section_bodies_fail(tmp_path: Path) -> None:
    weakened = json.loads(SPEC.read_text(encoding="utf-8"))
    weakened["included_sections"] = {section: [] for section in sre.EXPECTED_SECTIONS}
    spec_path = tmp_path / "state_root_v5_scope_contract.json"
    spec_path.write_text(json.dumps(weakened, indent=2, sort_keys=True), encoding="utf-8")

    report = sre.check_receipt_file(
        receipt_path=RECEIPT,
        spec_path=spec_path,
        run_required_tests=False,
    )
    assert report["ok"] is False
    assert any("section-body encoding" in err for err in report["errors"])


def test_live_python_encoder_token_order_drift_fails(monkeypatch) -> None:
    original_read = sre._read_source_file
    source = original_read("src/state/state_root.py")
    old = "out += encode_uvarint(pool.reserve0)\n        out += encode_uvarint(pool.reserve1)"
    new = "out += encode_uvarint(pool.reserve1)\n        out += encode_uvarint(pool.reserve0)"
    assert old in source

    def fake_read(rel: str) -> str:
        if rel == "src/state/state_root.py":
            return source.replace(old, new)
        return original_read(rel)

    monkeypatch.setattr(sre, "_read_source_file", fake_read)
    errors = sre.verify_receipt(_load_receipt(), spec_path=SPEC)
    assert any("src/state/state_root.py::_encode_pools_section encoder token order drifted" in err for err in errors)


def test_live_contract_encoder_pool_reserve_order_drift_fails(monkeypatch) -> None:
    from src.state import state_root as state_root_mod
    from src.state.canonical import encode_bytes, encode_uvarint, hex_to_bytes_fixed

    def swapped_pools_section(pools) -> bytes:
        out = bytearray()
        entries = state_root_mod._sorted_pool_entries(pools)
        out += encode_uvarint(len(entries))
        for pool_b, pool in entries:
            asset0_b = hex_to_bytes_fixed(pool.asset0, nbytes=32, name="asset0")
            asset1_b = hex_to_bytes_fixed(pool.asset1, nbytes=32, name="asset1")
            status_code = state_root_mod._POOL_STATUS_CODE[pool.status]
            out += pool_b
            out += asset0_b
            out += asset1_b
            out += encode_uvarint(pool.reserve1)
            out += encode_uvarint(pool.reserve0)
            out += encode_uvarint(pool.fee_bps)
            out += encode_uvarint(pool.lp_supply)
            out += encode_uvarint(status_code)
            out += encode_uvarint(pool.created_at)
            out += encode_bytes(pool.curve_tag.encode("utf-8"))
            out += encode_bytes(pool.curve_params.encode("utf-8"))
        return bytes(out)

    monkeypatch.setattr(state_root_mod, "_encode_pools_section", swapped_pools_section)
    errors = sre.verify_receipt(_load_receipt(), spec_path=SPEC)
    assert any("formal spec/live encoder byte mismatch" in err and "section POL" in err for err in errors), errors


def test_live_rust_encoder_token_order_drift_fails(monkeypatch) -> None:
    original_read = sre._read_source_file
    source = original_read("rust-runtime/crates/zenodex-runtime-core/src/state_root.rs")
    old = (
        "out.extend_from_slice(&encode_uvarint(e.reserve0));\n"
        "        out.extend_from_slice(&encode_uvarint(e.reserve1));"
    )
    new = (
        "out.extend_from_slice(&encode_uvarint(e.reserve1));\n"
        "        out.extend_from_slice(&encode_uvarint(e.reserve0));"
    )
    assert old in source

    def fake_read(rel: str) -> str:
        if rel == "rust-runtime/crates/zenodex-runtime-core/src/state_root.rs":
            return source.replace(old, new)
        return original_read(rel)

    monkeypatch.setattr(sre, "_read_source_file", fake_read)
    errors = sre.verify_receipt(_load_receipt(), spec_path=SPEC)
    assert any("rust state_root.rs::encode_pools encoder token order drifted" in err for err in errors)


def test_check_runs_required_test_commands(monkeypatch) -> None:
    calls: list[str] = []

    def fake_run_required_test_commands(*, profile: sre.TestProfile = "all") -> list[str]:
        calls.append(profile)
        return []

    monkeypatch.setattr(sre, "_run_required_test_commands", fake_run_required_test_commands)
    report = sre.check_receipt_file(receipt_path=RECEIPT, spec_path=SPEC, run_required_tests=True)
    assert report["ok"] is True, report["errors"]
    assert calls == ["all"]


def test_required_test_command_failure_fails_check(monkeypatch) -> None:
    monkeypatch.setattr(sre, "_run_required_test_commands", lambda **_kwargs: ["required test command failed"])
    report = sre.check_receipt_file(receipt_path=RECEIPT, spec_path=SPEC, run_required_tests=True)
    assert report["ok"] is False
    assert "required test command failed" in report["errors"]


@pytest.mark.parametrize(
    "summary",
    [
        "1 passed, 1 skipped in 0.01s",
        "1 passed, 1 xfailed in 0.01s",
        "1 passed, 1 xpassed in 0.01s",
        "1 passed, 1 deselected in 0.01s",
        "no tests ran in 0.01s",
    ],
)
def test_required_test_command_non_clean_output_fails(monkeypatch, summary: str) -> None:
    class FakeProc:
        returncode = 0
        stdout = summary
        stderr = ""

    monkeypatch.setattr(sre.subprocess, "run", lambda *args, **kwargs: FakeProc())
    errors = sre._run_required_test_commands(profile="python")
    assert errors


def test_required_test_profiles_split_rust_required_command() -> None:
    assert [row["id"] for row in sre._required_test_commands_for_profile("python")] == [
        "state_root_python_semantics",
        "state_root_runtime_binding",
    ]
    assert [row["id"] for row in sre._required_test_commands_for_profile("rust")] == [
        "state_root_python_rust_differential"
    ]
    assert sre._required_test_commands_for_profile("all") == sre.REQUIRED_TEST_COMMANDS


def test_runtime_shadow_structural_placement_rejects_comment_only_rust_profile(monkeypatch) -> None:
    """Review regression: the Rust authority receipt check must run in python-rust-shadow."""
    workflow = _runtime_shadow_workflow()
    mutated = copy.deepcopy(workflow)
    for step in mutated["jobs"]["python-rust-shadow"]["steps"]:
        if isinstance(step, dict) and isinstance(step.get("run"), str):
            rust_check = "python3 tools/check_state_root_surface_evidence.py check --pretty --test-profile rust"
            step["run"] = step["run"].replace(
                rust_check,
                f"# {rust_check}",
            )

    monkeypatch.setattr(
        sre,
        "_load_workflow",
        lambda rel: mutated if rel == ".github/workflows/runtime-shadow.yml" else workflow,
    )
    errors = sre._runtime_shadow_state_root_placement_errors()
    assert any("python-rust-shadow job missing state-root run snippet" in err for err in errors), errors


def test_runtime_shadow_structural_placement_rejects_rust_check_before_build(monkeypatch) -> None:
    workflow = _runtime_shadow_workflow()
    mutated = copy.deepcopy(workflow)
    steps = mutated["jobs"]["python-rust-shadow"]["steps"]
    build_index = next(
        index
        for index, step in enumerate(steps)
        if "cargo build --bin zenodex-runtime" in step.get("run", "")
    )
    receipt_index = next(
        index
        for index, step in enumerate(steps)
        if "tools/check_state_root_surface_evidence.py check --pretty --test-profile rust" in step.get("run", "")
    )
    steps[build_index], steps[receipt_index] = steps[receipt_index], steps[build_index]

    monkeypatch.setattr(
        sre,
        "_load_workflow",
        lambda rel: mutated if rel == ".github/workflows/runtime-shadow.yml" else workflow,
    )
    errors = sre._runtime_shadow_state_root_placement_errors()
    assert any("must run after cargo builds zenodex-runtime" in err for err in errors), errors


def test_release_integrity_structural_placement_rejects_comment_only_checker(monkeypatch) -> None:
    """Review regression: release gating must execute the checker in the release job."""
    workflow = _release_integrity_workflow()
    mutated = copy.deepcopy(workflow)
    for step in mutated["jobs"]["release-integrity"]["steps"]:
        if isinstance(step, dict) and isinstance(step.get("run"), str):
            step["run"] = step["run"].replace(
                "python3 tools/check_state_root_surface_evidence.py check --pretty",
                "# python3 tools/check_state_root_surface_evidence.py check --pretty",
            )

    monkeypatch.setattr(
        sre,
        "_load_workflow",
        lambda rel: mutated if rel == ".github/workflows/release-integrity.yml" else workflow,
    )
    errors = sre._release_integrity_state_root_placement_errors()
    assert any("release-integrity job missing state-root run snippet" in err for err in errors), errors
