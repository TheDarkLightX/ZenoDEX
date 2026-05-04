from __future__ import annotations

import pytest

from src.integration.zeno_oracle_authorization import semantic_hash
from src.state.canonical import canonical_json_bytes
from tools.build_oracle_authorization_canonical_vectors import RESULT_SCHEMA, build_vectors


def test_oracle_authorization_canonical_vectors_are_stable() -> None:
    vectors = build_vectors()
    by_name = {vector["name"]: vector for vector in vectors["vectors"]}

    assert vectors["schema"] == RESULT_SCHEMA
    assert vectors["canonical_encoding_version"] == 1
    assert vectors["value_hash_vector"]["value_hash"] == (
        "sha256:c0ea36e0cad8ef73627ff9b4c25bf9f6de47bf7bc200c59886e43f0649055a81"
    )
    assert by_name["oracle_authorization_ascii_v1"]["semantic_hash"] == (
        "sha256:1475ae5257003ece4ae5ac14a146e6e9fb29341c44dbf5ee9ae429ab3d46a3b5"
    )
    expected_unicode_hex = (
        "7b226465736372697074696f6e223a225554462d382063616e6f6e6963616c697a6174696f6e20766563746f72"
        "20666f72206e6f6e2d41534349492066656564206c6162656c73222c22666565645f6c6162656c223a224147"
        "52532f5a44455820cebc2d6d61726b6574222c2273796d626f6c73223a5b225ace9e4e4f222c22ce94222c"
        "22e4bea1e6a0bc225d7d"
    )
    assert by_name["oracle_authorization_unicode_utf8_v1"]["canonical_json_utf8_hex"] == (
        expected_unicode_hex
    )
    assert by_name["oracle_authorization_unicode_utf8_v1"]["semantic_hash"] == (
        "sha256:58611d89de9e81e6a86131be76ae229848994de92f3572da4436caf0da31f88b"
    )


def test_oracle_authorization_canonicalization_rejects_ambiguous_json_values() -> None:
    with pytest.raises(TypeError, match="floats are not allowed"):
        canonical_json_bytes({"value_e8": 1.25})
    with pytest.raises(TypeError, match="dict keys must be str"):
        semantic_hash("zenodex.oracle.bad-key.v1", {1: "not-a-string-key"})  # type: ignore[arg-type]
