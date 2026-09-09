"""Hostile structural controls for the bounded V3 acceptance index."""

from __future__ import annotations

import copy
import hashlib
import json
import shutil
import sys
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from tools import v3_acceptance as acceptance

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture
def index() -> dict[str, Any]:
    return acceptance.load_index(ROOT / acceptance.INDEX_PATH)


def _binding(
    index: dict[str, Any],
    case_id: str,
    limitation: str = "This bounded case does not establish a lifecycle.",
) -> dict[str, Any]:
    case = index["case_catalog"][case_id]
    return {
        "case_id": case_id,
        "implementation_paths": list(case["implementation_paths"]),
        "limitation": limitation,
    }


def _copy_subject(index: dict[str, Any], tmp_path: Path) -> Path:
    paths: set[str] = set()
    for pin in index["source_pins"].values():
        entries = [pin] if "path" in pin else pin["sources"]
        paths.update(entry["path"] for entry in entries)
    for component in index["components"]:
        paths.update(entry["path"] for entry in component["sources"])
    for case in index["case_catalog"].values():
        paths.update(entry["path"] for entry in case["test_sources"])
    for relative in paths:
        target = tmp_path / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / relative, target)
    return tmp_path


def _layout_hash(index: dict[str, Any]) -> str:
    layout = {key: index[key] for key in ("source_pins", "components", "case_catalog")}
    return hashlib.sha256(
        json.dumps(layout, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
    ).hexdigest()


def test_structural_inventory_is_distinct_from_bindings_replay_and_conformance(
    index: dict[str, Any], capsys: pytest.CaptureFixture[str]
) -> None:
    status = acceptance.validate_index(index)

    assert status["mapping"] == "PARTIAL"
    assert status["case_sources"] == "PINNED"
    assert status["provisional_cases"] == ""
    assert status["next_unmet"] == "CAPABILITY:ASSET_TRANSFER:tau_originated_asset_registration"
    assert acceptance.main(["--validate"]) == 0
    assert "STRUCTURAL_INVENTORY=PASS" in capsys.readouterr().out
    assert acceptance.main([]) == 0
    output = capsys.readouterr().out
    assert "MAPPED_TESTS=PARTIAL" in output
    assert "CASE_SOURCES=PINNED" in output
    assert "REPLAY=UNRECORDED" in output
    assert "FULL_CONFORMANCE=UNESTABLISHED" in output
    assert (
        "NEXT_UNMET=COVERAGE_GAP:CAPABILITY:ASSET_TRANSFER:tau_originated_asset_registration"
        in output
    )
    assert acceptance.main(["--check"]) == 2
    assert (
        "INCOMPLETE COVERAGE_GAP:CAPABILITY:ASSET_TRANSFER:tau_originated_asset_registration"
        in capsys.readouterr().out
    )


def test_pinned_custody_successor_is_limited_python_evidence(
    index: dict[str, Any],
) -> None:
    case_id = "custody-successor-v2-python"
    case = index["case_catalog"][case_id]
    component = next(item for item in index["components"] if item["id"] == case["component_id"])

    assert case["source_status"] == component["source_status"] == "PINNED"
    assert [entry["path"] for entry in component["sources"]] == [
        "src/core/asset_lane_custody_state_v2.py",
        "src/core/asset_lane_custody_coordinator_v2.py",
        "src/core/asset_lane_custody_global_v2.py",
    ]
    assert [entry["path"] for entry in case["test_sources"]] == [
        "tests/core/test_asset_lane_custody_v2.py",
        "tests/core/test_asset_lane_custody_global_v2.py",
    ]
    assert all(len(entry["sha256"]) == 64 for entry in component["sources"] + case["test_sources"])
    assert tuple(case["pytest_nodes"]) == acceptance.REPLAY_CASES[case_id]
    assert set(case["allowed_ids"]) == {
        "CAPABILITY:ASSET_TRANSFER:generic_transfer",
        "CAPABILITY:ASSET_TRANSFER:managed_issue",
        "CAPABILITY:ASSET_TRANSFER:managed_burn",
    }
    assert all(
        "does not execute Rust" in binding["limitation"]
        for mapping in index["mappings"]
        if mapping["id"]
        in {
            "CAPABILITY:ASSET_TRANSFER:managed_issue",
            "CAPABILITY:ASSET_TRANSFER:managed_burn",
        }
        for binding in mapping["bindings"]
    )


def test_check_rejects_provisional_case_sources(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(
        acceptance,
        "validate_index",
        lambda *_: {
            "mapping": "FULL_PREREQUISITE_BINDINGS",
            "next_unmet": "",
            "case_sources": "PROVISIONAL",
            "provisional_cases": "custody-successor-v2-python",
        },
    )

    assert acceptance.main(["--check"]) == 2
    assert (
        "INCOMPLETE PROVISIONAL_CASE_SOURCES:custody-successor-v2-python" in capsys.readouterr().out
    )


@pytest.mark.parametrize(
    ("mutate", "code"),
    (
        (
            lambda data: data["inventory"]["workflow_ids"].pop(),
            "INVENTORY_DRIFT",
        ),
        (
            lambda data: data["gaps"][0]["ids"].append(data["gaps"][0]["ids"][0]),
            "DUPLICATE_REQUIREMENT",
        ),
    ),
)
def test_requirement_deletion_or_duplication_rejects(
    index: dict[str, Any], mutate: object, code: str
) -> None:
    data = copy.deepcopy(index)
    mutate(data)  # type: ignore[operator]

    with pytest.raises(ValueError, match=code):
        acceptance.validate_index(data)


def test_stale_component_or_test_binding_rejects(index: dict[str, Any], tmp_path: Path) -> None:
    subject = _copy_subject(index, tmp_path)
    source = subject / "src/core/asset_lane_custody_global_v2.py"
    source.write_text(source.read_text(encoding="utf-8") + "\n# drift\n", encoding="utf-8")

    with pytest.raises(ValueError, match="COMPONENT_SOURCE_STALE"):
        acceptance.validate_index(index, subject)

    subject = _copy_subject(index, tmp_path / "test-drift")
    test_source = subject / "tests/core/test_asset_lane_custody_global_v2.py"
    test_source.write_text(
        test_source.read_text(encoding="utf-8") + "\n# drift\n", encoding="utf-8"
    )
    with pytest.raises(ValueError, match="CASE_TEST_STALE"):
        acceptance.validate_index(index, subject)


def test_nonexistent_node_or_unlinked_implementation_rejects(
    index: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    missing = copy.deepcopy(index)
    original_layout = acceptance.LAYOUT_SHA256
    monkeypatch.setattr(
        acceptance,
        "LAYOUT_SHA256",
        _layout_hash(
            {
                **missing,
                "case_catalog": {
                    **missing["case_catalog"],
                    "transfer-v2-core": {
                        **missing["case_catalog"]["transfer-v2-core"],
                        "pytest_nodes": [
                            "tests/core/test_asset_transfer_module_v2.py::missing_case"
                        ],
                    },
                },
            }
        ),
    )
    missing["case_catalog"]["transfer-v2-core"]["pytest_nodes"] = [
        "tests/core/test_asset_transfer_module_v2.py::missing_case"
    ]
    with pytest.raises(ValueError, match="NODE_MISSING"):
        acceptance.validate_index(missing)
    monkeypatch.setattr(acceptance, "LAYOUT_SHA256", original_layout)

    unlinked = copy.deepcopy(index)
    binding = unlinked["mappings"][0]["bindings"][0]
    binding["implementation_paths"] = ["src/core/global_settlement_abi_v2_codec.py"]
    with pytest.raises(ValueError, match="IMPLEMENTATION_COVERAGE"):
        acceptance.validate_index(unlinked)


def test_successor_cannot_inherit_historical_runtime_evidence_by_name(
    index: dict[str, Any],
) -> None:
    data = copy.deepcopy(index)
    data["successors"][0]["binding"] = _binding(data, "custody-transfer-v1")

    with pytest.raises(ValueError, match="SUCCESSOR_ABI"):
        acceptance.validate_index(data)


@pytest.mark.parametrize(
    ("result", "code"),
    (
        (SimpleNamespace(returncode=1, stdout="1 failed", stderr=""), "REPLAY_FAILED"),
        (SimpleNamespace(returncode=0, stdout="1 skipped", stderr=""), "REPLAY_NONPASS"),
        (
            SimpleNamespace(returncode=0, stdout="2 passed, 1 skipped", stderr=""),
            "REPLAY_NONPASS",
        ),
    ),
)
def test_failing_or_skipped_replay_cannot_promote_bindings(
    index: dict[str, Any], monkeypatch: pytest.MonkeyPatch, result: object, code: str
) -> None:
    calls: list[tuple[list[str], dict[str, Any]]] = []

    def fake_run(argv: list[str], **kwargs: object) -> object:
        calls.append((argv, kwargs))
        return result

    monkeypatch.setattr(acceptance.subprocess, "run", fake_run)
    with pytest.raises(ValueError, match=code):
        acceptance.run_replay("transfer-v2-core")

    assert calls == [
        (
            [
                sys.executable,
                "-m",
                "pytest",
                "-q",
                *acceptance.REPLAY_CASES["transfer-v2-core"],
            ],
            {"cwd": ROOT, "capture_output": True, "text": True, "check": False},
        )
    ]
    assert acceptance.validate_index(index)["mapping"] == "PARTIAL"


def test_duplicate_json_key_and_fabricated_full_conformance_reject(
    index: dict[str, Any], tmp_path: Path
) -> None:
    malformed = tmp_path / "duplicate.json"
    malformed.write_text('{"schema":"one","schema":"two"}', encoding="utf-8")
    with pytest.raises(ValueError, match="DUPLICATE_JSON_KEY"):
        acceptance.load_index(malformed)

    data = copy.deepcopy(index)
    data["claim_states"]["full_conformance"] = "ESTABLISHED"
    with pytest.raises(ValueError, match="CLAIM_STATE"):
        acceptance.validate_index(data)
