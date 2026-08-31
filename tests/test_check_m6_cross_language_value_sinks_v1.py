from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools import check_m6_cross_language_value_sinks_v1 as checker_module
from tools.m6_cross_language_sinks.inventory import (
    build_cross_language_projection,
    compare_projection_to_manifest,
    discover_dynamic_imports,
    discover_risc0_generated_includes,
    parse_rust_lane_ids,
    validate_command_lane_consistency,
)
from tools.m6_cross_language_sinks.model import canonical_root
from tools.m6_cross_language_sinks.operations import (
    generated_python_owner,
    language_operation_definitions,
    scan_generated_python_source,
    scan_rust_source,
    scan_shell_source,
    scan_tau_source,
)
from tools.m6_cross_language_sinks.report import build_cross_language_report
from tools.m6_value_sinks.operations import SINK_KINDS


def test_rust_durable_writer_and_journal_commit_are_observed() -> None:
    source = """
fn persist(path: &Path, bytes: &[u8]) {
    std::fs::write(path, bytes).unwrap();
    risc0_zkvm::guest::env::commit(bytes);
}
"""

    observations = scan_rust_source("zk/example/src/lib.rs", source)

    assert {item.operation_kind for item in observations} == {
        "RISC0_JOURNAL_COMMIT",
        "RUST_FS_WRITE",
    }


def test_rust_unsafe_or_ffi_surface_cannot_disappear_from_inventory() -> None:
    observations = scan_rust_source(
        "zk/example/src/lib.rs",
        'extern "C" { fn foreign_write(); }\nunsafe { foreign_write(); }\n',
    )

    assert [item.operation_kind for item in observations] == ["RUST_UNSAFE_OR_FFI_SURFACE"]


def test_rust_comments_and_strings_do_not_invent_writer_surfaces() -> None:
    observations = scan_rust_source(
        "zk/example/src/lib.rs",
        '// unsafe { std::fs::write("state", b"x"); }\n'
        'const MESSAGE: &str = "unsafe std::fs::write";\n',
    )

    assert observations == ()


def test_rust_extern_crates_are_not_ffi_surfaces() -> None:
    observations = scan_rust_source(
        "zk/example/src/lib.rs",
        "extern crate alloc;\nextern crate std;\n",
    )

    assert observations == ()


def test_rust_same_line_occurrences_are_counted_exactly() -> None:
    observations = scan_rust_source(
        "zk/example/src/lib.rs",
        'fn persist() { std::fs::write("a", b"x"); std::fs::write("b", b"y"); }\n',
    )

    assert len(observations) == 1
    assert observations[0].operation_kind == "RUST_FS_WRITE"
    assert observations[0].occurrence_count == 2


def test_rust_import_alias_writer_is_operation_derived() -> None:
    observations = scan_rust_source(
        "zk/example/src/lib.rs",
        "use std::fs::rename as archive_snapshot;\n"
        'fn persist() { archive_snapshot("old", "new").unwrap(); }\n',
    )

    assert [item.operation_kind for item in observations] == ["RUST_PATH_MUTATION"]
    assert observations[0].occurrence_count == 1


def test_language_definitions_bind_the_o007a_python_vocabulary() -> None:
    definitions = language_operation_definitions()

    assert set(definitions) == {"PYTHON", "RUST", "SHELL", "TAU"}
    assert [row["operation_kind"] for row in definitions["PYTHON"]] == sorted(SINK_KINDS)
    assert {row["effect_class"] for row in definitions["PYTHON"]} >= {
        "DURABLE_MUTATION",
        "IN_MEMORY_STATE_MUTATION",
    }


def test_shell_redirection_and_mutating_command_are_observed() -> None:
    observations = scan_shell_source(
        "scripts/install.sh",
        "install -m 0755 source /usr/local/bin/tool\nprintf x > state.txt\n",
    )

    assert {item.operation_kind for item in observations} == {
        "SHELL_FILE_MUTATION",
        "SHELL_REDIRECTION_WRITE",
    }


def test_shell_same_line_redirections_are_counted_exactly() -> None:
    observations = scan_shell_source(
        "scripts/install.sh",
        "printf x > first.txt; printf y > second.txt\n",
    )

    redirections = [
        item for item in observations if item.operation_kind == "SHELL_REDIRECTION_WRITE"
    ]
    assert len(redirections) == 1
    assert redirections[0].occurrence_count == 2


def test_shell_dynamic_source_dispatch_is_observed() -> None:
    observations = scan_shell_source("tools/run.sh", 'source "${PROFILE}"\n')

    assert [item.operation_kind for item in observations] == ["SHELL_DYNAMIC_DISPATCH"]


def test_dockerfile_run_writer_is_observed_as_shell() -> None:
    observations = scan_shell_source(
        "Dockerfile",
        "RUN install -m 0755 source /usr/local/bin/tool\n",
        source_role="CONTAINER_BUILD_SHELL",
    )

    assert [item.operation_kind for item in observations] == ["SHELL_FILE_MUTATION"]


def test_dockerfile_copy_and_entrypoint_have_typed_effect_classes() -> None:
    observations = scan_shell_source(
        "Dockerfile",
        'COPY source /app/source\nENTRYPOINT ["python3", "-m", "app"]\n',
        source_role="CONTAINER_BUILD_SHELL",
    )

    assert [(item.operation_kind, item.effect_class) for item in observations] == [
        ("SHELL_CONTAINER_COMMAND_DISPATCH", "DISPATCH"),
        ("SHELL_CONTAINER_COPY_ADD", "DURABLE_MUTATION"),
    ]


def test_tau_outputs_are_proposals_without_durable_authority() -> None:
    source = """
always
  (o1[t]:sbf = 1:sbf <-> i1[t]:sbf = 1:sbf) &&
  (o2[t]:sbf = 1:sbf <-> i2[t]:sbf = 1:sbf).
"""

    observations = scan_tau_source("src/tau_specs/recommended/example.tau", source)

    assert len(observations) == 1
    assert observations[0].operation_kind == "TAU_OUTPUT_PROPOSAL"
    assert observations[0].occurrence_count == 2
    assert observations[0].mediation_status == "SPEC_PROPOSAL_NO_DURABLE_AUTHORITY"


def test_generated_python_requires_declared_owner_and_ir_hash() -> None:
    with pytest.raises(ValueError, match="generated owner"):
        generated_python_owner("generated/example.py", "print(1)\n")

    owner = generated_python_owner(
        "generated/example.py",
        '"""\nAuto-generated Python reference model for: example\n'
        "IR hash: sha256:"
        + "1"
        * 64
        + "\nGenerated by ESSO (Evolutionary Spec Search Optimizer)\n\n"
        'This file is standalone.\n"""\n',
    )

    assert owner.owner_class == "ESSO_DECLARED"
    assert owner.ir_sha256 == "1" * 64
    assert owner.replay_binding == "DECLARED_OWNER_WITHOUT_PINNED_GENERATOR_REPLAY"


def test_generated_python_durable_write_is_not_hidden_by_reference_status() -> None:
    source = (
        '"""\nAuto-generated Python reference model for: example\n'
        "IR hash: sha256:" + "2" * 64 + "\nGenerated by an offline verifier toolchain.\n"
        '"""\nfrom pathlib import Path\nPath("x").write_text("value")\n'
    )

    observations = scan_generated_python_source("generated/example.py", source)

    assert [item.operation_kind for item in observations] == ["PATH_WRITE"]
    assert observations[0].mediation_status == "UNMEDIATED_GENERATED_CODE_WRITER"
    assert observations[0].language == "PYTHON"
    assert observations[0].provenance == "GENERATED_REFERENCE"


def test_dynamic_import_sites_retain_literal_and_unresolved_targets() -> None:
    source = """
import importlib
module = importlib.import_module("src.integration.exact_out_route_certificate")
other = importlib.import_module(runtime_name)
__import__("sys")
"""

    declarations = discover_dynamic_imports("src/integration/example.py", source)

    assert [(item.mechanism, item.target_status, item.targets) for item in declarations] == [
        ("import_module", "LITERAL", ("src.integration.exact_out_route_certificate",)),
        ("import_module", "UNRESOLVED", ()),
        ("__import__", "LITERAL", ("sys",)),
    ]


def test_risc0_generated_include_requires_sibling_build_owner(tmp_path: Path) -> None:
    crate = tmp_path / "zk" / "demo" / "methods"
    (crate / "src").mkdir(parents=True)
    (crate / "src" / "lib.rs").write_text(
        'include!(concat!(env!("OUT_DIR"), "/methods.rs"));\n', encoding="utf-8"
    )

    owners, findings = discover_risc0_generated_includes(tmp_path, ("zk/demo/methods/src/lib.rs",))

    assert owners == ()
    assert findings == (
        "zk/demo/methods/src/lib.rs: generated include has no sibling zk/demo/methods/build.rs",
    )


def test_rust_lane_ids_must_cover_every_o006_lane_target() -> None:
    rust = """
pub enum LaneIdV1 {
    SPOT_LIQUIDITY,
    ZUSD_MONETARY,
}
"""
    registry = {
        "decisions": [
            {"command": "spot_swap", "target_kind": "LANE", "target_id": "SPOT_LIQUIDITY"},
            {"command": "zusd_borrow", "target_kind": "LANE", "target_id": "ZUSD_MONETARY"},
        ]
    }

    lane_ids = parse_rust_lane_ids(rust)

    assert validate_command_lane_consistency(registry, lane_ids) == ()
    assert validate_command_lane_consistency(registry, ("SPOT_LIQUIDITY",)) == (
        "O-006 lane target ZUSD_MONETARY is absent from Rust lane enum",
    )


def test_o006_governed_route_must_be_declared_by_capability_manifest() -> None:
    registry = {
        "decisions": [
            {
                "command": "perp_funding",
                "target_kind": "GOVERNED_ROUTE",
                "target_id": "perps_epoch_settlement",
            }
        ]
    }

    assert (
        validate_command_lane_consistency(registry, ("PERPS_MARKET",), ("perps_epoch_settlement",))
        == ()
    )
    assert validate_command_lane_consistency(registry, ("PERPS_MARKET",), ()) == (
        "O-006 governed-route target perps_epoch_settlement is absent from capability manifest",
    )


def test_projection_includes_extensionless_shell_and_generated_fire_reference(
    tmp_path: Path,
) -> None:
    launcher = tmp_path / "bin" / "launch"
    launcher.parent.mkdir(parents=True)
    launcher.write_text("#!/usr/bin/env bash\nprintf x > state\n", encoding="utf-8")
    generated = tmp_path / "src" / "fire" / "kernel" / "demo_ref.py"
    generated.parent.mkdir(parents=True)
    generated.write_text(
        '"""\nIR hash: sha256:'
        + "3" * 64
        + "\nGenerated by ESSO (Evolutionary Spec Search Optimizer)\n\n"
        + '"""\nfrom pathlib import Path\nPath("x").write_text("value")\n',
        encoding="utf-8",
    )

    projection = build_cross_language_projection(
        tmp_path,
        tracked_paths=("bin/launch", "src/fire/kernel/demo_ref.py"),
    )

    assert projection["source_counts"] == {"PYTHON": 1, "SHELL": 1}
    assert projection["source_provenance_counts"] == {
        "GENERATED_REFERENCE": 1,
        "HANDWRITTEN": 1,
    }
    assert len(projection["generated_python_owners"]) == 1
    assert set(projection["source_roots"]) == {"PYTHON", "RUST", "SHELL", "TAU"}


def test_cross_language_writer_alias_mutation_breaks_reviewed_projection(tmp_path: Path) -> None:
    rust_path = tmp_path / "zk" / "demo" / "src" / "lib.rs"
    rust_path.parent.mkdir(parents=True)
    rust_path.write_text("pub fn pure() {}\n", encoding="utf-8")
    tracked = ("zk/demo/src/lib.rs",)
    first = build_cross_language_projection(tmp_path, tracked_paths=tracked)
    reviewed: dict[str, object] = {
        "nonclaims": [],
        "projection": first,
        "review_status": "REVIEWED_CURRENT_SUBJECT",
        "schema": "zenodex/m6-cross-language-value-sinks/v1",
        "scope": "test",
    }
    rust_path.write_text(
        "use std::fs::rename as archive_snapshot;\n"
        'pub fn persist() { archive_snapshot("old", "new").unwrap(); }\n',
        encoding="utf-8",
    )
    second = build_cross_language_projection(tmp_path, tracked_paths=tracked)

    assert canonical_root(first) != canonical_root(second)
    assert second["unmediated_operation_count"] == 1
    assert compare_projection_to_manifest(second, reviewed) == (
        "cross-language projection does not match the reviewed manifest",
    )


def test_projection_manifest_comparison_rejects_rewritten_observation_root() -> None:
    projection: dict[str, object] = {"schema": "projection", "roots": {"rust": "a"}}
    manifest: dict[str, object] = {
        "nonclaims": [],
        "scope": "test",
        "schema": "zenodex/m6-cross-language-value-sinks/v1",
        "review_status": "REVIEWED_CURRENT_SUBJECT",
        "projection": {"schema": "projection", "roots": {"rust": "b"}},
    }

    assert compare_projection_to_manifest(projection, manifest) == (
        "cross-language projection does not match the reviewed manifest",
    )


def test_manifest_regeneration_preserves_malformed_reviewed_bytes(tmp_path: Path) -> None:
    tools = tmp_path / "tools"
    tools.mkdir()
    manifest = tools / "m6_cross_language_value_sink_manifest_v1.json"
    malformed = b'{"schema":'
    manifest.write_bytes(malformed)

    with pytest.raises(ValueError, match="existing cross-language manifest is invalid"):
        checker_module._atomic_write_manifest(tmp_path)

    assert manifest.read_bytes() == malformed


def test_manifest_regeneration_requires_fresh_review(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    tools = tmp_path / "tools"
    tools.mkdir()
    manifest = tools / "m6_cross_language_value_sink_manifest_v1.json"
    manifest.write_text(
        json.dumps(
            {
                "nonclaims": [],
                "projection": {"projection_root": "old"},
                "review_status": "REVIEWED_CURRENT_SUBJECT",
                "schema": "zenodex/m6-cross-language-value-sinks/v1",
                "scope": "old subject",
            }
        ),
        encoding="utf-8",
    )
    regenerated: dict[str, object] = {
        "nonclaims": [],
        "projection": {"projection_root": "new"},
        "review_status": "UNREVIEWED",
        "schema": "zenodex/m6-cross-language-value-sinks/v1",
        "scope": "new subject",
    }
    monkeypatch.setattr(checker_module, "render_manifest", lambda _root: regenerated)

    checker_module._atomic_write_manifest(tmp_path)

    assert json.loads(manifest.read_text(encoding="utf-8")) == regenerated


def test_current_repository_manifest_matches_exact_projection() -> None:
    root = Path(__file__).resolve().parents[1]
    report = build_cross_language_report(root)

    assert report["findings"] == []
    assert report["ok"] is True
    assert report["release_ready"] is False
    assert report["production_authority"] is False
    assert report["vm01_status"] == "OPEN"
    assert report["o007b_bounded_inventory_status"] == "COMPLETE"
    assert report["reviewed_projection_matches_current_subject"] is True
    unmediated_operation_count = report["unmediated_operation_count"]
    assert type(unmediated_operation_count) is int
    assert unmediated_operation_count > 0
    assert report["generated_replay_ownership_complete"] is False
    assert (
        json.loads(
            (root / "tools" / "m6_cross_language_value_sink_manifest_v1.json").read_text(
                encoding="utf-8"
            )
        )["review_status"]
        == "REVIEWED_CURRENT_SUBJECT"
    )
