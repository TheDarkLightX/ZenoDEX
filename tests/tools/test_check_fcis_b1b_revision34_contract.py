from __future__ import annotations

import ast
import shutil
from pathlib import Path

from tools.check_fcis_b1b_revision34_contract import (
    CHECKER_PATH,
    MAX_MUTATION_FIXTURE_BYTES,
    REQUIRED_PATHS,
    REVISION_PATH,
    RUST_LIB_PATH,
    RUST_PATH,
    check_repository,
)

REPO = Path(__file__).resolve().parents[2]


def _copy_required(tmp_path: Path) -> tuple[Path, int, set[Path]]:
    target = tmp_path / "bounded-repo"
    copied: set[Path] = set()
    total_bytes = 0
    for relative in REQUIRED_PATHS:
        source = REPO / relative
        destination = target / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
        copied.add(relative)
        total_bytes += source.stat().st_size
    return target, total_bytes, copied


def _codes(root: Path) -> set[str]:
    return {finding.code for finding in check_repository(root).findings}


def _replace(root: Path, path: Path, old: str, new: str) -> None:
    target = root / path
    text = target.read_text(encoding="utf-8")
    assert old in text
    target.write_text(text.replace(old, new, 1), encoding="utf-8")


def test_revision34_contract_is_green() -> None:
    report = check_repository(REPO)
    assert report.ok, report.findings
    assert report.runtime_files_scanned > 0


def test_mutation_fixture_is_declared_and_disk_bounded(tmp_path: Path) -> None:
    root, total_bytes, copied = _copy_required(tmp_path)
    assert copied == set(REQUIRED_PATHS)
    assert total_bytes <= MAX_MUTATION_FIXTURE_BYTES
    assert sum(path.stat().st_size for path in root.rglob("*") if path.is_file()) == total_bytes

    tree = ast.parse((REPO / Path(__file__).relative_to(REPO)).read_text(encoding="utf-8"))
    copied_whole_tree = any(
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "copytree"
        for node in ast.walk(tree)
    )
    assert not copied_whole_tree


def test_approved_revision_blob_drift_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / REVISION_PATH
    path.write_text(path.read_text(encoding="utf-8") + "\n", encoding="utf-8")
    assert "REV34_BLOB_DRIFT" in _codes(root)


def test_premature_pinned_verifier_type_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/fcis_b1b_authority_values.py"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "\nclass PinnedDeploymentBootstrapVerifierV2:\n    pass\n",
        encoding="utf-8",
    )
    assert "B1B1_PREMATURE_AUTHORITY" in _codes(root)


def test_bare_header_advance_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/fcis_b1b_authority_values.py"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "\ndef advance_header_v2(pre_header):\n    return pre_header\n",
        encoding="utf-8",
    )
    assert "B1B1_BARE_HEADER_TRANSITION" in _codes(root)


def test_runtime_carrier_import_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/runtime_consumer_mutant.py"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "from .fcis_b1b_authority_values import FCISAuthorityHeaderV2\n",
        encoding="utf-8",
    )
    assert "B1B1_RUNTIME_REACHABILITY" in _codes(root)


def test_forbidden_content_authority_path_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/fcis_fee_distribution_configuration_content_validation.py"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("# premature B1B-2 authority\n", encoding="utf-8")
    assert "B1B1_FORBIDDEN_PATH" in _codes(root)


def test_public_rust_carrier_field_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        RUST_PATH,
        "pub struct FCISAuthorityHeaderV2 {\n    chain_deployment_id: String,",
        "pub struct FCISAuthorityHeaderV2 {\n    pub chain_deployment_id: String,",
    )
    assert "B1B1_RUST_PUBLIC_FIELD" in _codes(root)


def test_missing_public_rust_carrier_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        RUST_PATH,
        "pub struct V1ToV2MigrationManifestV2",
        "struct V1ToV2MigrationManifestV2",
    )
    assert "B1B1_RUST_STRUCT" in _codes(root)


def test_python_schema_id_drift_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_values.py"),
        "zenodex/fcis/state/authority-header/v2",
        "zenodex/fcis/state/authority-header/v3",
    )
    assert "B1B1_SCHEMA_ID" in _codes(root)


def test_python_root_domain_drift_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_codec.py"),
        '"fcis_deployment_bootstrap_anchor_claim"',
        '"fcis_deployment_bootstrap_anchor_claim_mutant"',
    )
    assert "B1B1_ROOT_DOMAIN" in _codes(root)


def test_value_immutability_removal_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_values.py"),
        "@final\n@dataclass(frozen=True, slots=True)\nclass FCISAuthorityHeaderSourceV2:",
        "@dataclass(frozen=True, slots=True)\nclass FCISAuthorityHeaderSourceV2:",
    )
    assert "B1B1_VALUE_NOT_IMMUTABLE" in _codes(root)


def test_rust_module_export_removal_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        RUST_LIB_PATH,
        "pub mod fcis_b1b_authority;",
        "// carrier module export removed",
    )
    assert "B1B1_RUST_MODULE_EXPORT" in _codes(root)


def test_missing_required_checker_path_fails_closed(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    (root / CHECKER_PATH).unlink()
    assert "MISSING_PATH" in _codes(root)
