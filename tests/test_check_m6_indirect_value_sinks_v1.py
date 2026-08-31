"""Adversarial evidence for the O-007C indirect sink registry."""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from tools.m6_indirect_value_sinks.dynamic import (
    scan_dynamic_declarations,
    scan_indirect_aliases,
)
from tools.m6_indirect_value_sinks.inventory import (
    DYNAMIC_TARGET_SETS,
    EVIDENCE_TOOL_PATHS,
    GAP_DISPOSITIONS,
    REGISTRY_PATH,
    RESEARCH_DYNAMIC_EXCLUSIONS,
    _dynamic_dispositions,
    _gap_dispositions,
    decode_registry,
    require_dynamic_disposition_completeness,
    scoped_python_candidate,
    validate_target_pins,
)
from tools.m6_indirect_value_sinks.model import (
    DynamicDeclarationV1,
    IndirectSinkRejectV1,
    pretty_json_bytes,
)
from tools.m6_indirect_value_sinks.report import build_indirect_value_sink_report

ROOT = Path(__file__).resolve().parents[1]


@pytest.fixture(scope="module")
def public_report() -> dict[str, object]:
    return build_indirect_value_sink_report(ROOT)


def test_exact_evidence_tool_exclusion_cannot_absorb_unrelated_tool() -> None:
    assert len(EVIDENCE_TOOL_PATHS) == 9
    assert all(not scoped_python_candidate(path) for path in EVIDENCE_TOOL_PATHS)
    assert scoped_python_candidate("tools/unrelated_o007c_probe.py")
    assert not scoped_python_candidate("tests/unrelated_o007c_probe.py")


def test_path_write_bytes_alias_is_discovered_while_direct_call_is_not() -> None:
    direct = ast.parse("from pathlib import Path\nPath('x').write_bytes(b'x')\n")
    alias = ast.parse("from pathlib import Path\nindirect_writer = Path.write_bytes\n")

    assert scan_indirect_aliases("src/direct.py", direct, primary_reachable=False) == ()
    rows = scan_indirect_aliases("src/alias.py", alias, primary_reachable=False)
    assert len(rows) == 1
    assert rows[0].sink_kind == "PATH_WRITE"
    assert rows[0].symbol == "<module>"


def _scan_dynamic(source: str) -> tuple[DynamicDeclarationV1, ...]:
    return scan_dynamic_declarations(
        "src/example.py",
        ast.parse(source),
        primary_reachable=False,
        source_sha256="1" * 64,
    )


def test_dynamic_call_extraction_binds_the_mechanism_specific_target_argument() -> None:
    positional = _scan_dynamic('spec_from_file_location("misleading_name", ref_path)')
    assert len(positional) == 1
    assert positional[0].target_kind == "FILE_LOCATION"
    assert positional[0].target_status == "UNRESOLVED_SYNTACTIC"
    assert positional[0].targets == ()
    assert positional[0].target_expression == "Name(id='ref_path', ctx=Load())"

    keyword = _scan_dynamic(
        'spec_from_file_location(name="misleading_name", location="src/actual.py")'
    )
    assert keyword[0].target_status == "LITERAL_TARGET"
    assert keyword[0].targets == ("src/actual.py",)

    with pytest.raises(IndirectSinkRejectV1) as error:
        _scan_dynamic(
            'spec_from_file_location("misleading_name", ref_path, location=other_path)'
        )
    assert error.value.code == "DYNAMIC_SIGNATURE"


@pytest.mark.parametrize(
    ("source", "mechanism", "target_kind", "status", "targets"),
    [
        ('import_module("tau")', "import_module", "MODULE_NAME", "LITERAL_TARGET", ("tau",)),
        ('__import__(name="sys")', "__import__", "MODULE_NAME", "LITERAL_TARGET", ("sys",)),
        (
            'loader.load_module(fullname="package.module")',
            "load_module",
            "MODULE_NAME",
            "LITERAL_TARGET",
            ("package.module",),
        ),
        (
            "loader.exec_module(module)",
            "exec_module",
            "MODULE_OBJECT",
            "UNRESOLVED_SYNTACTIC",
            (),
        ),
    ],
)
def test_supported_dynamic_signatures_are_explicit(
    source: str,
    mechanism: str,
    target_kind: str,
    status: str,
    targets: tuple[str, ...],
) -> None:
    row = _scan_dynamic(source)[0]
    assert (row.mechanism, row.target_kind, row.target_status, row.targets) == (
        mechanism,
        target_kind,
        status,
        targets,
    )


def test_closed_disposition_maps_reject_unknown_rows(tmp_path: Path) -> None:
    unknown = DynamicDeclarationV1(
        path="src/new_loader.py",
        line=1,
        mechanism="import_module",
        fingerprint="0" * 64,
        primary_reachable=False,
        source_sha256="1" * 64,
        target_expression="Name(id='target', ctx=Load())",
        target_kind="MODULE_NAME",
        target_status="UNRESOLVED_SYNTACTIC",
        targets=(),
    )
    with pytest.raises(IndirectSinkRejectV1) as dynamic_error:
        _dynamic_dispositions(tmp_path, (unknown,))
    assert dynamic_error.value.code == "DYNAMIC_IDENTITY_SET"

    with pytest.raises(IndirectSinkRejectV1) as gap_error:
        _gap_dispositions(
            tmp_path,
            ({"path": "src/new_loader.py", "mechanism": "import_module"},),
        )
    assert gap_error.value.code == "CLOSURE_GAP_IDENTITY_SET"


def test_exact_disposition_completeness_rejects_missing_derived_row() -> None:
    first = DynamicDeclarationV1(
        path="src/first.py",
        line=1,
        mechanism="import_module",
        fingerprint="1" * 64,
        primary_reachable=False,
        source_sha256="2" * 64,
        target_expression="Constant(value='tau')",
        target_kind="MODULE_NAME",
        target_status="LITERAL_TARGET",
        targets=("tau",),
    )
    second = DynamicDeclarationV1(
        path="src/second.py",
        line=2,
        mechanism="import_module",
        fingerprint="3" * 64,
        primary_reachable=False,
        source_sha256="4" * 64,
        target_expression="Constant(value='sys')",
        target_kind="MODULE_NAME",
        target_status="LITERAL_TARGET",
        targets=("sys",),
    )
    disposition = {
        "path": first.path,
        "line": first.line,
        "mechanism": first.mechanism,
        "fingerprint": first.fingerprint,
    }
    with pytest.raises(IndirectSinkRejectV1) as error:
        require_dynamic_disposition_completeness((first, second), (disposition,))
    assert error.value.code == "MISSING_DYNAMIC_DISPOSITION"


def _pin_registry(path: str, digest: str) -> dict[str, object]:
    row = {"target_pins": [{"path": path, "sha256": digest}]}
    return {
        "closure_gap_dispositions": [],
        "dynamic_dispositions": [row],
    }


def test_target_boundaries_and_digest_fail_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    target = tmp_path / "target.py"
    target.write_bytes(b"bound target\n")
    digest = hashlib.sha256(target.read_bytes()).hexdigest()
    validate_target_pins(tmp_path, _pin_registry("target.py", digest))
    monkeypatch.chdir(tmp_path)
    validate_target_pins(Path("."), _pin_registry("target.py", digest))

    with pytest.raises(IndirectSinkRejectV1) as digest_error:
        validate_target_pins(tmp_path, _pin_registry("target.py", "0" * 64))
    assert digest_error.value.code == "TARGET_DIGEST"

    with pytest.raises(IndirectSinkRejectV1) as missing_error:
        validate_target_pins(tmp_path, _pin_registry("missing.py", digest))
    assert missing_error.value.code == "TARGET_MISSING"

    outside = tmp_path.parent / "outside-o007c.py"
    outside.write_bytes(b"outside\n")
    link = tmp_path / "link.py"
    link.symlink_to(outside)
    with pytest.raises(IndirectSinkRejectV1) as symlink_error:
        validate_target_pins(tmp_path, _pin_registry("link.py", digest))
    assert symlink_error.value.code == "TARGET_SYMLINK"

    with pytest.raises(IndirectSinkRejectV1) as escape_error:
        validate_target_pins(tmp_path, _pin_registry("../outside-o007c.py", digest))
    assert escape_error.value.code == "TARGET_ESCAPE"


def test_registry_decoder_rejects_unknown_duplicate_and_noncanonical_fields() -> None:
    raw = (ROOT / REGISTRY_PATH).read_bytes()
    registry: dict[str, Any] = json.loads(raw)

    unknown = dict(registry)
    unknown["future_field"] = True
    with pytest.raises(IndirectSinkRejectV1) as unknown_error:
        decode_registry(pretty_json_bytes(unknown))
    assert unknown_error.value.code == "UNKNOWN_FIELD"

    duplicate = raw.replace(b'{\n  "closure_gap_dispositions":', b'{\n  "schema": "duplicate",\n  "closure_gap_dispositions":', 1)
    with pytest.raises(IndirectSinkRejectV1) as duplicate_error:
        decode_registry(duplicate)
    assert duplicate_error.value.code == "DUPLICATE_JSON_KEY"

    noncanonical = (json.dumps(registry) + "\n").encode()
    with pytest.raises(IndirectSinkRejectV1) as canonical_error:
        decode_registry(noncanonical)
    assert canonical_error.value.code == "REGISTRY_CANONICAL"


def test_registry_decoder_rejects_noncanonical_resolved_target_order() -> None:
    registry: dict[str, Any] = json.loads((ROOT / REGISTRY_PATH).read_bytes())
    dynamic = registry["dynamic_dispositions"]
    row = next(item for item in dynamic if len(item["resolved_targets"]) > 1)
    row["resolved_targets"] = list(reversed(row["resolved_targets"]))
    with pytest.raises(IndirectSinkRejectV1) as error:
        decode_registry(pretty_json_bytes(registry))
    assert error.value.code == "DYNAMIC_ROW"


def test_reviewed_registry_has_exact_closed_disposition_sets() -> None:
    registry = decode_registry((ROOT / REGISTRY_PATH).read_bytes())
    dynamic = registry["dynamic_dispositions"]
    gaps = registry["closure_gap_dispositions"]
    assert isinstance(dynamic, list)
    assert isinstance(gaps, list)
    assert len(DYNAMIC_TARGET_SETS) == 13
    assert len(RESEARCH_DYNAMIC_EXCLUSIONS) == 31
    assert len(dynamic) == 61
    assert len(GAP_DISPOSITIONS) == len(gaps) == 26
    assert sum(row["declaration_status"] == "UNRESOLVED_SYNTACTIC" for row in dynamic) == 44
    assert sum(row["declaration_status"] == "LITERAL_TARGET" for row in dynamic) == 16
    assert sum(row["declaration_status"] == "CLOSED_STATIC_REGISTRY" for row in dynamic) == 1
    assert sum(row["disposition"] == "CLOSED_LOCAL_TARGET_SET" for row in dynamic) == 13
    assert sum(row["disposition"] == "SOURCE_BOUND_RESEARCH_EXCLUSION" for row in dynamic) == 31
    assert sum(row["disposition"] == "DERIVED_LOCAL_LITERAL_TARGET" for row in dynamic) == 7
    assert sum(row["disposition"] == "DERIVED_EXTERNAL_LITERAL_TARGET" for row in dynamic) == 9
    assert sum(row["disposition"] == "DERIVED_CLOSED_STATIC_REGISTRY" for row in dynamic) == 1
    assert sum(row["disposition"] == "UNRESOLVED_OPERATOR_PROCESS_BOUNDARY" for row in gaps) == 9

    tau = next(
        row
        for row in dynamic
        if row["path"] == "src/integration/tau_runner.py" and row["declared_targets"] == ["tau"]
    )
    assert tau["disposition"] == "DERIVED_EXTERNAL_LITERAL_TARGET"
    assert tau["resolved_targets"] == ["tau"]
    assert tau["resolved_target_class"] == "EXTERNAL_MODULE"
    assert tau["containment"] == "EXTERNAL_MODULE_NOT_REPOSITORY_CONTAINED"
    assert tau["target_kind"] == "MODULE_NAME"
    assert tau["target_pins"] == []

    perp_ref = next(
        row
        for row in dynamic
        if row["path"] == "src/integration/perp_engine.py" and row["line"] == 810
    )
    assert perp_ref["target_expression"] == "Name(id='ref_path', ctx=Load())"
    assert perp_ref["target_kind"] == "FILE_LOCATION"
    assert perp_ref["disposition"] == "CLOSED_LOCAL_TARGET_SET"
    assert perp_ref["resolved_targets"] == [
        "generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py"
    ]


def test_public_report_closes_rows_with_evidence_derived_blockers(
    public_report: dict[str, object],
) -> None:
    assert public_report["ok"] is True
    assert public_report["bounded_inventory_status"] == "COMPLETE_RESEARCH_ONLY"
    assert public_report["all_discovered_rows_dispositioned"] is True
    assert public_report["value_movement_authority"] == "NONE"
    assert public_report["vm01_status"] == "OPEN"
    summary = public_report["inventory_summary"]
    assert isinstance(summary, dict)
    assert summary["mounted_worker_launcher_count"] == 0
    assert summary["mounted_migration_launcher_count"] == 0
    assert summary["o007a_decoded_launcher_count"] == 12
    assert summary["proof_callback_record_count"] > 0
    assert len(str(summary["proof_callback_records_root"])) == 64
    assert summary["dynamic_declaration_count"] == 61
    assert summary["dynamic_disposition_count"] == 61
    assert summary["literal_dynamic_count"] == 16
    assert summary["closed_static_registry_dynamic_count"] == 1
    assert summary["unresolved_dynamic_count"] == 44
    assert public_report["production_authority"] == "NONE"
    assert public_report["settlement_authority"] == "NONE"
    assert public_report["verifier_authority"] == "NONE"
    assert public_report["special_statuses"] == [
        "MISSING_MOUNTED_WORKER_ENTRYPOINT",
        "UNMOUNTED_MIGRATION_ENTRYPOINT",
    ]
