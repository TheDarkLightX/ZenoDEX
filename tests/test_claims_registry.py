from __future__ import annotations


def test_claims_registry_is_valid() -> None:
    from tools.check_claims_registry import validate_registry, REGISTRY_PATH

    validate_registry(REGISTRY_PATH)

