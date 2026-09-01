from __future__ import annotations

import ast
from pathlib import Path

from tools.check_global_settlement_canonical_manifest_v1 import (
    DISPATCHER_PATH_V1,
    ENUM_TUPLE_V1,
    MANIFEST_PATH_V1,
    SERIALIZER_TUPLE_V1,
    _check_data_only_manifest,
    _check_dispatcher,
    _check_manifest_shape,
    _literal_string_tuple,
    _source_closure_sha256,
    check_repository,
)

REPO_ROOT = Path(__file__).resolve().parents[1]


def _tree(relative_path: Path) -> ast.Module:
    path = REPO_ROOT / relative_path
    return ast.parse(path.read_text(encoding="utf-8"), filename=path.as_posix())


def test_repository_canonical_manifest_source_closure_passes() -> None:
    report = check_repository(REPO_ROOT)

    assert report["ok"] is True, report["errors"]
    assert report["serializer_type_count"] == 102
    assert report["enum_type_count"] == 34
    assert report["canonical_helper_call_file_count"] == 93
    assert report["source_closure_file_count"] == 94


def test_manifest_shape_rejects_missing_duplicate_and_unsorted_types() -> None:
    tree = _tree(MANIFEST_PATH_V1)
    serializers = _literal_string_tuple(tree, SERIALIZER_TUPLE_V1)
    enums = _literal_string_tuple(tree, ENUM_TUPLE_V1)

    assert any("count" in error for error in _check_manifest_shape(serializers[:-1], enums))
    assert any(
        "duplicates" in error
        for error in _check_manifest_shape(serializers[:-1] + (serializers[-2],), enums)
    )
    assert any(
        "sorted" in error
        for error in _check_manifest_shape((serializers[1], serializers[0], *serializers[2:]), enums)
    )


def test_manifest_rejects_domain_import_or_executable_registration() -> None:
    source = (REPO_ROOT / MANIFEST_PATH_V1).read_text(encoding="utf-8")

    imported_tree = ast.parse(source + "\nfrom src.core import global_settlement_types_v1\n")
    assert any("forbidden module" in error for error in _check_data_only_manifest(imported_tree))

    registering_tree = ast.parse(source + "\nregister_type('foreign.Type')\n")
    registering_errors = _check_data_only_manifest(registering_tree)
    assert any("forbidden top-level" in error for error in registering_errors)
    assert any("frozenset" in error for error in registering_errors)


def test_dispatcher_checker_rejects_instance_bound_serializer_dispatch() -> None:
    source = (REPO_ROOT / DISPATCHER_PATH_V1).read_text(encoding="utf-8")
    mutated = source.replace(
        "return True, serializer(value)",
        "return True, value.to_canonical()",
        1,
    )

    errors = _check_dispatcher(ast.parse(mutated))

    assert any("unbound" in error for error in errors)
    assert any("instance-bound" in error for error in errors)


def test_dispatcher_checker_rejects_generic_enum_admission() -> None:
    source = (REPO_ROOT / DISPATCHER_PATH_V1).read_text(encoding="utf-8")
    mutated = source.replace(
        "    candidate_type = type(value)\n",
        "    if isinstance(value, Enum):\n"
        "        return True, value.value\n"
        "    candidate_type = type(value)\n",
        1,
    )

    errors = _check_dispatcher(ast.parse(mutated))

    assert any("generic Enum" in error for error in errors)


def test_dispatcher_checker_rejects_weakened_loaded_type_identity() -> None:
    source = (REPO_ROOT / DISPATCHER_PATH_V1).read_text(encoding="utf-8")
    mutated = source.replace(
        "namespace.get(type_name) is not candidate_type",
        "namespace.get(type_name) is None",
        1,
    )

    errors = _check_dispatcher(ast.parse(mutated))

    assert any("exact candidate type identity" in error for error in errors)


def test_dispatcher_checker_rejects_dynamic_import_and_registry_mutation() -> None:
    source = (REPO_ROOT / DISPATCHER_PATH_V1).read_text(encoding="utf-8")
    mutated = source.replace(
        "    candidate_type = type(value)\n",
        "    __import__('foreign')\n"
        "    GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPE_SET_V1.add('foreign.Type')\n"
        "    candidate_type = type(value)\n",
        1,
    )

    errors = _check_dispatcher(ast.parse(mutated))

    assert any("dynamic admission" in error for error in errors)
    assert any("mutate its admission registry" in error for error in errors)


def test_source_closure_digest_is_order_independent_and_content_sensitive(
    tmp_path: Path,
) -> None:
    first = tmp_path / "first.py"
    second = tmp_path / "second.py"
    first.write_text("FIRST = 1\n", encoding="utf-8")
    second.write_text("SECOND = 2\n", encoding="utf-8")

    original = _source_closure_sha256(tmp_path, (first, second))
    assert _source_closure_sha256(tmp_path, (second, first, first)) == original

    second.write_text("SECOND = 3\n", encoding="utf-8")
    assert _source_closure_sha256(tmp_path, (first, second)) != original
