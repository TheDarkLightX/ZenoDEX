from __future__ import annotations

import ast
import shutil
from pathlib import Path

import pytest

from tools.check_fcis_b1b_revision34_contract import (
    CHECKER_PATH,
    MAX_MUTATION_FIXTURE_BYTES,
    REQUIRED_PATHS,
    REVISION_PATH,
    RUST_LIB_PATH,
    RUST_PATH,
    Finding,
    _check_runtime_dataclass_fields,
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


def test_runtime_state_binding_consumer_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/integration/runtime_consumer_mutant.py"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "from ..core.fcis_fee_configuration_state_binding_v2 "
        "import StateBoundActiveFeeConfigurationV2\n",
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


def test_extra_python_carrier_field_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_values.py"),
        "    sequence: int\n    fee_distribution_configuration_root: str",
        "    sequence: int\n    hidden_policy_selector: str = \"\"\n"
        "    fee_distribution_configuration_root: str = \"0x\" + (\"0\" * 64)",
    )
    assert "B1B1_PYTHON_FIELD_SET" in _codes(root)


def test_custom_python_carrier_equality_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_values.py"),
        "    def __post_init__(self) -> None:\n"
        "        _validate_authority_header_fields_v2(\n",
        "    def __eq__(self, other: object) -> bool:\n"
        "        return type(other) is FCISAuthorityHeaderV2\n\n"
        "    def __post_init__(self) -> None:\n"
        "        _validate_authority_header_fields_v2(\n",
    )
    assert "B1B1_PYTHON_IDENTITY" in _codes(root)


@pytest.mark.parametrize(
    "base_definition",
    (
        (
            "@dataclass(frozen=True, slots=True)\n"
            "class _HiddenAuthorityState:\n"
            '    hidden_policy_selector: str = field(init=False, default="GOOD")\n'
        ),
        (
            "@dataclass(frozen=True, slots=True)\n"
            "class _HiddenAuthorityState:\n"
            '    hidden_policy_selector: str = field(init=False, default="GOOD", compare=True)\n'
        ),
        (
            "class _HiddenAuthorityState:\n"
            "    @property\n"
            "    def hidden_policy_selector(self) -> str:\n"
            '        return "GOOD"\n'
        ),
    ),
    ids=("inherited-init-false-field", "inherited-compare-field", "inherited-property"),
)
def test_python_carrier_base_class_is_detected(
    tmp_path: Path,
    base_definition: str,
) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_values.py"),
        "from dataclasses import dataclass",
        "from dataclasses import dataclass, field",
    )
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_values.py"),
        "@final\n@dataclass(frozen=True, slots=True)\nclass FCISAuthorityHeaderV2:",
        base_definition
        + "\n@final\n@dataclass(frozen=True, slots=True)\n"
        + "class FCISAuthorityHeaderV2(_HiddenAuthorityState):",
    )
    assert "B1B1_PYTHON_CLASS_SHAPE" in _codes(root)


def test_runtime_field_probe_detects_inherited_stored_state(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_values.py"),
        "from dataclasses import dataclass",
        "from dataclasses import dataclass, field",
    )
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_values.py"),
        "@final\n@dataclass(frozen=True, slots=True)\nclass FCISAuthorityHeaderV2:",
        "@dataclass(frozen=True, slots=True)\n"
        "class _HiddenAuthorityState:\n"
        '    hidden_policy_selector: str = field(init=False, default="GOOD")\n'
        "\n@final\n@dataclass(frozen=True, slots=True)\n"
        "class FCISAuthorityHeaderV2(_HiddenAuthorityState):",
    )
    findings: list[Finding] = []
    _check_runtime_dataclass_fields(root, findings)
    assert {finding.code for finding in findings} == {
        "B1B1_PYTHON_RUNTIME_FIELDS"
    }


def test_extra_python_carrier_decorator_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_values.py"),
        "@final\n@dataclass(frozen=True, slots=True)\nclass FCISAuthorityHeaderV2:",
        "def identity_replacing_decorator(carrier_type):\n"
        "    carrier_type.__eq__ = lambda self, other: True\n"
        "    return carrier_type\n\n"
        "@identity_replacing_decorator\n"
        "@final\n@dataclass(frozen=True, slots=True)\n"
        "class FCISAuthorityHeaderV2:",
    )
    assert "B1B1_PYTHON_DECORATORS" in _codes(root)


def test_python_carrier_metaclass_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        Path("src/core/fcis_b1b_authority_values.py"),
        "@final\n@dataclass(frozen=True, slots=True)\nclass FCISAuthorityHeaderV2:",
        "class _InjectingMeta(type):\n"
        "    def __new__(metaclass, name, bases, namespace):\n"
        '        namespace["hidden_policy_selector"] = "GOOD"\n'
        "        return super().__new__(metaclass, name, bases, namespace)\n\n"
        "@final\n@dataclass(frozen=True, slots=True)\n"
        "class FCISAuthorityHeaderV2(metaclass=_InjectingMeta):",
    )
    assert "B1B1_PYTHON_CLASS_SHAPE" in _codes(root)


@pytest.mark.parametrize(
    "mutation",
    (
        "FCISAuthorityHeaderV2.__eq__ = lambda self, other: True\n",
        'setattr(FCISAuthorityHeaderV2, "__hash__", lambda self: 0)\n',
        'type.__setattr__(FCISAuthorityHeaderV2, "__eq__", lambda self, other: True)\n',
        'delattr(FCISAuthorityHeaderV2, "__post_init__")\n',
    ),
    ids=(
        "module-equality-replacement",
        "setattr-hash",
        "type-setattr-equality",
        "delattr-post-init",
    ),
)
def test_python_carrier_post_definition_identity_mutation_is_detected(
    tmp_path: Path,
    mutation: str,
) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/fcis_b1b_authority_values.py"
    path.write_text(path.read_text(encoding="utf-8") + "\n" + mutation, encoding="utf-8")
    assert "B1B1_PYTHON_IDENTITY_MUTATION" in _codes(root)


@pytest.mark.parametrize(
    "mutation",
    (
        (
            "_original_header_post_init = FCISAuthorityHeaderV2.__post_init__\n\n"
            "def _patched_header_post_init(self):\n"
            "    if getattr(self, \"chain_deployment_id\", None) == \"bypass\":\n"
            "        return\n"
            "    _original_header_post_init(self)\n\n"
            "setattr(\n"
            "    FCISAuthorityHeaderV2,\n"
            "    \"__post_init__\",\n"
            "    _patched_header_post_init,\n"
            ")\n"
        ),
        (
            "HeaderAlias = FCISAuthorityHeaderV2\n"
            "SecondAlias = HeaderAlias\n"
            "setattr(SecondAlias, \"__eq__\", lambda self, other: True)\n"
        ),
        ('globals()["FCISAuthorityHeaderV2"] = object\n'),
        (
            "import sys\n"
            'vars(sys.modules[__name__])["FCISAuthorityHeaderV2"] = object\n'
        ),
        (
            "CapturedPostInit = FCISAuthorityHeaderV2.__post_init__\n"
            "type.__setattr__(\n"
            "    FCISAuthorityHeaderV2,\n"
            "    \"__post_init__\",\n"
            "    lambda self: None,\n"
            ")\n"
        ),
    ),
    ids=(
        "sibling-validation-bypass",
        "sibling-transitive-alias-equality",
        "sibling-globals-replacement",
        "sibling-vars-replacement",
        "sibling-captured-post-init-replacement",
    ),
)
def test_sibling_module_carrier_identity_mutation_is_detected(
    tmp_path: Path,
    mutation: str,
) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/fcis_b1b_authority_admission.py"
    path.write_text(path.read_text(encoding="utf-8") + "\n" + mutation, encoding="utf-8")
    assert "B1B1_PYTHON_IDENTITY_MUTATION" in _codes(root)


def test_full_import_probe_detects_sibling_validation_bypass(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/fcis_b1b_authority_admission.py"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "\nsetattr(FCISAuthorityHeaderV2, \"__post_init__\", lambda self: None)\n",
        encoding="utf-8",
    )
    findings: list[Finding] = []
    _check_runtime_dataclass_fields(root, findings)
    assert {finding.code for finding in findings} == {
        "B1B1_PYTHON_RUNTIME_FIELDS"
    }


@pytest.mark.parametrize(
    "extra_derive",
    ("Default", "Hash", "serde::Deserialize", "arbitrary::Arbitrary"),
    ids=("default", "hash", "deserialize", "arbitrary"),
)
def test_extra_rust_carrier_derive_is_detected(
    tmp_path: Path,
    extra_derive: str,
) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        RUST_PATH,
        "#[derive(Debug, Clone, PartialEq, Eq)]\npub struct FCISAuthorityHeaderV2 {",
        f"#[derive(Debug, Clone, PartialEq, Eq, {extra_derive})]\n"
        "pub struct FCISAuthorityHeaderV2 {",
    )
    assert "B1B1_RUST_DERIVE_SURFACE" in _codes(root)


@pytest.mark.parametrize(
    "mutation",
    (
        (
            "impl Default for FCISAuthorityHeaderV2 {\n"
            "    fn default() -> Self {\n"
            "        Self {\n"
            "            chain_deployment_id: String::new(),\n"
            "            sequence: BigUint::ZERO,\n"
            "            fee_distribution_configuration_root: String::new(),\n"
            "        }\n"
            "    }\n"
            "}\n"
        ),
        (
            "impl From<(String, BigUint, String)> for FCISAuthorityHeaderV2 {\n"
            "    fn from(value: (String, BigUint, String)) -> Self {\n"
            "        Self {\n"
            "            chain_deployment_id: value.0,\n"
            "            sequence: value.1,\n"
            "            fee_distribution_configuration_root: value.2,\n"
            "        }\n"
            "    }\n"
            "}\n"
        ),
    ),
    ids=("manual-default", "manual-from"),
)
def test_rust_trait_constructor_is_detected(tmp_path: Path, mutation: str) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(root, RUST_PATH, "#[cfg(test)]", mutation + "\n#[cfg(test)]")
    assert "B1B1_RUST_IMPL_SURFACE" in _codes(root)


@pytest.mark.parametrize(
    "mutation",
    (
        (
            "impl FCISAuthorityHeaderV2 {\n"
            "    pub fn from_raw_parts(\n"
            "        chain_deployment_id: String,\n"
            "        sequence: BigUint,\n"
            "        fee_distribution_configuration_root: String,\n"
            "    ) -> Self {\n"
            "        Self {\n"
            "            chain_deployment_id,\n"
            "            sequence,\n"
            "            fee_distribution_configuration_root,\n"
            "        }\n"
            "    }\n"
            "}\n"
        ),
        (
            "impl FCISAuthorityHeaderV2 where FCISAuthorityHeaderV2: Clone {\n"
            "    pub(crate) fn new(\n"
            "        chain_deployment_id: String,\n"
            "        sequence: BigUint,\n"
            "        fee_distribution_configuration_root: String,\n"
            "    ) -> Self {\n"
            "        Self {\n"
            "            chain_deployment_id,\n"
            "            sequence,\n"
            "            fee_distribution_configuration_root,\n"
            "        }\n"
            "    }\n"
            "}\n"
        ),
        (
            "pub(crate) trait RawCarrierFactory { fn try_new() -> Self; }\n"
            "impl RawCarrierFactory for "
            "crate::fcis_b1b_authority::FCISAuthorityHeaderV2 {\n"
            "    fn try_new() -> Self {\n"
            "        Self {\n"
            "            chain_deployment_id: String::new(),\n"
            "            sequence: BigUint::ZERO,\n"
            "            fee_distribution_configuration_root: String::new(),\n"
            "        }\n"
            "    }\n"
            "}\n"
        ),
        (
            "use self::FCISAuthorityHeaderV2 as HeaderAlias;\n"
            "pub(crate) trait RawCarrierFactory { fn try_new() -> Self; }\n"
            "impl RawCarrierFactory for HeaderAlias {\n"
            "    fn try_new() -> Self {\n"
            "        Self {\n"
            "            chain_deployment_id: String::new(),\n"
            "            sequence: BigUint::ZERO,\n"
            "            fee_distribution_configuration_root: String::new(),\n"
            "        }\n"
            "    }\n"
            "}\n"
        ),
        (
            "pub(crate) fn try_new(\n"
            "    chain_deployment_id: String,\n"
            "    sequence: BigUint,\n"
            "    fee_distribution_configuration_root: String,\n"
            "  ) -> FCISAuthorityHeaderV2 {\n"
            "    FCISAuthorityHeaderV2 { chain_deployment_id, sequence, "
            "fee_distribution_configuration_root }\n"
            "}\n"
        ),
        (
            "mod hidden_carrier_constructor {\n"
            "    use super::FCISAuthorityHeaderV2;\n"
            "    use num_bigint::BigUint;\n"
            "    pub(crate) fn try_new() -> FCISAuthorityHeaderV2 {\n"
            "        FCISAuthorityHeaderV2 {\n"
            "            chain_deployment_id: String::new(),\n"
            "            sequence: BigUint::ZERO,\n"
            "            fee_distribution_configuration_root: String::new(),\n"
            "        }\n"
            "    }\n"
            "}\n"
        ),
        (
            "impl Default for FCISAuthorityHeaderV2 {\n"
            "    fn default() -> Self {\n"
            "        Self {\n"
            "            chain_deployment_id: String::new(),\n"
            "            sequence: BigUint::ZERO,\n"
            "            fee_distribution_configuration_root: String::new(),\n"
            "        }\n"
            "    }\n"
            "}\n"
        ),
        (
            "impl From<(String, BigUint, String)> for FCISAuthorityHeaderV2 {\n"
            "    fn from(value: (String, BigUint, String)) -> Self {\n"
            "        Self {\n"
            "            chain_deployment_id: value.0,\n"
            "            sequence: value.1,\n"
            "            fee_distribution_configuration_root: value.2,\n"
            "        }\n"
            "    }\n"
            "}\n"
        ),
        (
            "pub fn inspect_raw_header_after_tests(\n"
            "    value: FCISAuthorityHeaderV2,\n"
            ") -> FCISAuthorityHeaderV2 {\n"
            "    value\n"
            "}\n"
        ),
        "carrier_builder!(FCISAuthorityHeaderV2);\n",
        "carrier_builder!();\n",
        (
            "pub const INVALID_HEADER_AFTER_TESTS: FCISAuthorityHeaderV2 = "
            "FCISAuthorityHeaderV2 {\n"
            "    chain_deployment_id: String::new(),\n"
            "    sequence: BigUint::ZERO,\n"
            "    fee_distribution_configuration_root: String::new(),\n"
            "};\n"
        ),
        "pub type HeaderAliasAfterTests = FCISAuthorityHeaderV2;\n",
    ),
    ids=(
        "unchecked-inherent-constructor",
        "where-clause-inherent-constructor",
        "qualified-trait-constructor",
        "use-alias-trait-constructor",
        "top-level-allowlisted-constructor",
        "nested-module-allowlisted-constructor",
        "manual-default",
        "manual-from",
        "public-carrier-helper",
        "constructor-macro-with-carrier",
        "constructor-macro-without-carrier",
        "carrier-const",
        "carrier-type-alias",
    ),
)
def test_rust_production_item_after_test_modules_is_detected(
    tmp_path: Path,
    mutation: str,
) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / RUST_PATH
    path.write_text(
        path.read_text(encoding="utf-8") + "\n" + mutation,
        encoding="utf-8",
    )
    codes = _codes(root)
    assert {
        "B1B1_RUST_IMPL_SURFACE",
        "B1B1_RUST_CARRIER_CONSUMER",
        "B1B1_RUST_PUBLIC_SURFACE",
    } & codes


def test_rust_macro_inside_carrier_impl_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    helper = root / RUST_PATH.parent / "fcis_b1b_hidden_methods.rs"
    helper.write_text(
        "pub(crate) fn new(\n"
        "    chain_deployment_id: String,\n"
        "    sequence: BigUint,\n"
        "    fee_distribution_configuration_root: String,\n"
        "  ) -> Self {\n"
        "    Self { chain_deployment_id, sequence, "
        "fee_distribution_configuration_root }\n"
        "}\n",
        encoding="utf-8",
    )
    _replace(
        root,
        RUST_PATH,
        "impl FCISAuthorityHeaderV2 {\n",
        "impl FCISAuthorityHeaderV2 {\n"
        "    include!(\"fcis_b1b_hidden_methods.rs\");\n",
    )
    assert "B1B1_RUST_IMPL_SURFACE" in _codes(root)


@pytest.mark.parametrize(
    ("old", "new"),
    (
        (
            "impl FCISAuthorityHeaderV2 {\n",
            "#[cfg_attr(\n"
            "    all(),\n"
            "    carrier_methods\n"
            ")]\n"
            "impl FCISAuthorityHeaderV2 {\n",
        ),
        (
            "    pub fn try_new(\n",
            "    #[cfg_attr(all(), carrier_method)]\n"
            "    pub fn try_new(\n",
        ),
    ),
    ids=("impl-attribute", "method-attribute"),
)
def test_rust_carrier_impl_attribute_surface_is_detected(
    tmp_path: Path,
    old: str,
    new: str,
) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(root, RUST_PATH, old, new)
    assert "B1B1_RUST_IMPL_SURFACE" in _codes(root)


def test_rust_second_inherent_impl_between_test_modules_is_detected(
    tmp_path: Path,
) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / RUST_PATH
    text = path.read_text(encoding="utf-8")
    final_test_module = text.rfind("#[cfg(test)]")
    assert final_test_module > 0
    mutation = (
        "impl FCISAuthorityHeaderV2 {\n"
        "    pub fn from_raw_parts_between_tests(\n"
        "        chain_deployment_id: String,\n"
        "        sequence: BigUint,\n"
        "        fee_distribution_configuration_root: String,\n"
        "    ) -> Self {\n"
        "        Self { chain_deployment_id, sequence, "
        "fee_distribution_configuration_root }\n"
        "    }\n"
        "}\n\n"
    )
    path.write_text(
        text[:final_test_module] + mutation + text[final_test_module:],
        encoding="utf-8",
    )
    assert "B1B1_RUST_IMPL_SURFACE" in _codes(root)


def test_multiline_rust_cfg_attr_default_derive_is_detected(
    tmp_path: Path,
) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        RUST_PATH,
        "#[derive(Debug, Clone, PartialEq, Eq)]\n"
        "pub struct FCISAuthorityHeaderV2 {",
        "#[cfg_attr(\n"
        "    all(),\n"
        "    derive(Default)\n"
        ")]\n"
        "#[derive(Debug, Clone, PartialEq, Eq)]\n"
        "pub struct FCISAuthorityHeaderV2 {",
    )
    assert "B1B1_RUST_DERIVE_SURFACE" in _codes(root)


def test_multiline_rust_attribute_macro_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        RUST_PATH,
        "#[derive(Debug, Clone, PartialEq, Eq)]\n"
        "pub struct FCISAuthorityHeaderV2 {",
        "#[cfg_attr(\n"
        "    all(),\n"
        "    carrier_builder\n"
        ")]\n"
        "#[derive(Debug, Clone, PartialEq, Eq)]\n"
        "pub struct FCISAuthorityHeaderV2 {",
    )
    assert "B1B1_RUST_DERIVE_SURFACE" in _codes(root)


@pytest.mark.parametrize(
    ("old", "new"),
    (
        (
            "impl FCISAuthorityHeaderV2 {\n",
            "impl FCISAuthorityHeaderV2 {\n"
            "    pub(crate) fn new(\n"
            "        chain_deployment_id: String,\n"
            "        sequence: BigUint,\n"
            "        fee_distribution_configuration_root: String,\n"
            "    ) -> Self {\n"
            "        Self { chain_deployment_id, sequence, "
            "fee_distribution_configuration_root }\n"
            "    }\n\n",
        ),
        (
            "impl FCISAuthorityHeaderV2 {\n",
            "impl FCISAuthorityHeaderV2 {\n"
            "    pub const UNCHECKED_SEQUENCE: u8 = 0;\n\n",
        ),
        (
            "#[derive(Debug, Clone, PartialEq, Eq)]\n"
            "pub struct FCISAuthorityHeaderV2 {",
            "#[derive(Debug, Clone, PartialEq, Eq)]\n"
            "#[carrier_builder]\n"
            "pub struct FCISAuthorityHeaderV2 {",
        ),
        (
            "#[cfg(test)]",
            "carrier_builder!(FCISAuthorityHeaderV2);\n\n#[cfg(test)]",
        ),
    ),
    ids=("unchecked-new", "associated-const", "attribute-macro", "constructor-macro"),
)
def test_rust_generated_or_unchecked_constructor_surface_is_detected(
    tmp_path: Path,
    old: str,
    new: str,
) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(root, RUST_PATH, old, new)
    codes = _codes(root)
    assert {"B1B1_RUST_IMPL_SURFACE", "B1B1_RUST_DERIVE_SURFACE"} & codes


def test_extra_rust_carrier_field_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        RUST_PATH,
        "    sequence: BigUint,\n    fee_distribution_configuration_root: String,",
        "    sequence: BigUint,\n    hidden_policy_selector: String,\n"
        "    fee_distribution_configuration_root: String,",
    )
    assert "B1B1_RUST_FIELD_SET" in _codes(root)


def test_rust_lib_publication_helper_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / RUST_LIB_PATH
    path.write_text(
        path.read_text(encoding="utf-8")
        + "\npub fn publish_b1b_header(\n"
        + "    header: fcis_b1b_authority::FCISAuthorityHeaderV2,\n"
        + ") -> fcis_b1b_authority::FCISAuthorityHeaderV2 {\n"
        + "    header\n"
        + "}\n",
        encoding="utf-8",
    )
    assert "B1B1_RUST_MODULE_EXPORT" in _codes(root)


def test_novel_runtime_authority_symbol_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/novel_runtime_mutant.py"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "class PinnedDeploymentBootstrapVerifierV2:\n    pass\n",
        encoding="utf-8",
    )
    assert "B1B1_PREMATURE_AUTHORITY" in _codes(root)


def test_aliased_carrier_import_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/fcis_b1b_authority_schema.py"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "\nfrom .fcis_b1b_authority_values import FCISAuthorityHeaderV2 as Header\n",
        encoding="utf-8",
    )
    assert "B1B1_CARRIER_IMPORT" in _codes(root)


def test_fully_qualified_carrier_annotation_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/fcis_b1b_authority_schema.py"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "\nimport src.core.fcis_b1b_authority_values\n"
        + "def consume(value: src.core.fcis_b1b_authority_values.FCISAuthorityHeaderV2)"
        + " -> object:\n"
        + "    return value\n",
        encoding="utf-8",
    )
    codes = _codes(root)
    assert "B1B1_CARRIER_IMPORT" in codes
    assert "B1B1_CARRIER_CONSUMER" in codes


def test_neutral_name_carrier_consumer_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    path = root / "src/core/fcis_b1b_authority_values.py"
    path.write_text(
        path.read_text(encoding="utf-8")
        + "\ndef inspect_carrier(value: FCISAuthorityHeaderV2)"
        + " -> FCISAuthorityHeaderV2:\n"
        + "    return value\n",
        encoding="utf-8",
    )
    assert "B1B1_CARRIER_CONSUMER" in _codes(root)


def test_private_rust_alias_consumer_is_detected(tmp_path: Path) -> None:
    root, _, _ = _copy_required(tmp_path)
    _replace(
        root,
        RUST_PATH,
        "#[cfg(test)]",
        "type HeaderAliasV2 = FCISAuthorityHeaderV2;\n"
        "fn inspect_alias(value: HeaderAliasV2) -> HeaderAliasV2 {\n"
        "    value\n"
        "}\n\n"
        "#[cfg(test)]",
    )
    assert "B1B1_RUST_CARRIER_CONSUMER" in _codes(root)
