from __future__ import annotations

import json

import pytest

from tools.run_zrpf_spot_source_opening import (
    SOURCE_IMAGE_ID,
    SourceOpeningError,
    _decode_exact_json,
    _require_proof,
    _require_request,
    _write_new,
)


def _request() -> dict[str, object]:
    return {
        "schema": "tau_state_proof_request",
        "schema_version": 1,
        "proof_type": "risc0.zenodex_recursive_spot_leaf.v1",
        "receipt_kind": "succinct",
        "spot_recursive_leaf_input": {
            "risc0_image_id": [1] * 8,
            "spot_input": {
                "txs": [{}],
                "tx_execution_order": [0],
                "tx_ingress": [{}],
            },
        },
    }


def _proof() -> dict[str, object]:
    return {
        "schema": "tau_state_proof",
        "schema_version": 1,
        "proof_type": "risc0.zenodex_recursive_spot_leaf.v1",
        "proof": "receipt",
        "meta": {
            "risc0_image_id": SOURCE_IMAGE_ID,
            "receipt_kind": "succinct",
        },
    }


def test_exact_json_rejects_duplicate_keys_and_trailing_values() -> None:
    for raw in [b'{"a":1,"a":2}', b'{"a":1} {"b":2}']:
        with pytest.raises(SourceOpeningError):
            _decode_exact_json(raw, maximum=128, label="fixture")


def test_request_requires_singleton_ordered_profile() -> None:
    request = _request()
    _require_request(request)
    leaf = request["spot_recursive_leaf_input"]
    assert isinstance(leaf, dict)
    spot_input = leaf["spot_input"]
    assert isinstance(spot_input, dict)
    spot_input["tx_execution_order"] = []
    with pytest.raises(SourceOpeningError, match="singleton ordered"):
        _require_request(request)


def test_proof_requires_exact_source_image_and_succinct_kind() -> None:
    proof = _proof()
    _require_proof(proof)
    meta = proof["meta"]
    assert isinstance(meta, dict)
    meta["risc0_image_id"] = "00" * 32
    with pytest.raises(SourceOpeningError, match="image ID"):
        _require_proof(proof)


def test_create_new_output_refuses_replacement(tmp_path) -> None:
    path = tmp_path / "artifact.json"
    _write_new(path, b"first")
    with pytest.raises(FileExistsError):
        _write_new(path, b"second")
    assert path.read_bytes() == b"first"


def test_request_and_proof_fixtures_are_exact_json() -> None:
    for value, label in [(_request(), "request"), (_proof(), "proof")]:
        raw = json.dumps(value, separators=(",", ":")).encode()
        assert _decode_exact_json(raw, maximum=4_096, label=label) == value
