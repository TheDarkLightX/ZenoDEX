from __future__ import annotations

import copy

import yaml

from tools.check_claims_registry import (
    REGISTRY_PATH,
    CheckError,
    validate_registry,
    validate_registry_root,
)


def _loaded() -> dict:
    return yaml.safe_load(REGISTRY_PATH.read_text(encoding="utf-8"))


def test_claims_registry_is_valid() -> None:
    validate_registry(REGISTRY_PATH)


def test_status_outside_the_closed_vocabulary_is_rejected() -> None:
    root = copy.deepcopy(_loaded())
    root["claims"][0]["status"] = "vibes"
    try:
        validate_registry_root(root)
    except CheckError as error:
        assert "closed vocabulary" in str(error)
    else:
        raise AssertionError("invented status accepted")


def test_theorem_not_declared_in_referenced_lean_file_is_rejected() -> None:
    root = copy.deepcopy(_loaded())
    claim = next(c for c in root["claims"] if c.get("evidence", {}).get("theorems"))
    claim["evidence"]["theorems"] = [claim["evidence"]["theorems"][0] + "_renamed_away"]
    try:
        validate_registry_root(root)
    except CheckError as error:
        assert "not declared" in str(error)
    else:
        raise AssertionError("phantom theorem accepted")


def test_theorem_with_foreign_namespace_prefix_is_rejected() -> None:
    root = copy.deepcopy(_loaded())
    claim = next(c for c in root["claims"] if c.get("evidence", {}).get("theorems"))
    bare = claim["evidence"]["theorems"][0].rpartition(".")[2]
    claim["evidence"]["theorems"] = [f"SomeOther.Namespace.{bare}"]
    try:
        validate_registry_root(root)
    except CheckError as error:
        assert "not declared" in str(error)
    else:
        raise AssertionError("foreign namespace accepted")
