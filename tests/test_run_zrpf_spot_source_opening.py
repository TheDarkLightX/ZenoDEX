from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools import run_zrpf_spot_source_opening as source_opening
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


@pytest.mark.parametrize(
    "raw",
    [b'{"value":1.5}', b'{"value":NaN}', b'{"value":Infinity}', b'{"value":-Infinity}'],
)
def test_exact_json_rejects_floating_point_and_nonfinite_numbers(raw: bytes) -> None:
    with pytest.raises(SourceOpeningError, match="floating-point"):
        _decode_exact_json(raw, maximum=128, label="fixture")


def test_request_and_proof_reject_boolean_schema_version() -> None:
    request = _request()
    request["schema_version"] = True
    with pytest.raises(SourceOpeningError, match="schema version"):
        _require_request(request)

    proof = _proof()
    proof["schema_version"] = True
    with pytest.raises(SourceOpeningError, match="schema mismatch"):
        _require_proof(proof)


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


def test_run_supplies_persists_and_hashes_the_same_compact_json(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request_raw = json.dumps(_request(), separators=(",", ":")).encode()
    proof_raw = json.dumps(_proof(), separators=(",", ":")).encode()
    calls = 0

    def fake_run(*_args, input_bytes: bytes | None, **_kwargs) -> bytes:
        nonlocal calls
        calls += 1
        if calls == 1:
            assert input_bytes is None
            return request_raw + b"\n"
        assert input_bytes == request_raw
        return proof_raw + b"\n"

    monkeypatch.setattr(source_opening, "_run", fake_run)
    monkeypatch.setattr(
        source_opening,
        "_sha256_file",
        lambda path: source_opening.SOURCE_CLI_SHA256 if path.name == "source-cli" else "11" * 32,
    )
    for name in ("generator", "source-cli", "r0vm"):
        (tmp_path / name).write_bytes(name.encode())

    report = source_opening.run(
        generator=tmp_path / "generator",
        source_cli=tmp_path / "source-cli",
        r0vm=tmp_path / "r0vm",
        output_directory=tmp_path / "out",
        timeout_seconds=1,
    )

    assert (tmp_path / "out/spot-swap-source.request.json").read_bytes() == request_raw
    assert (tmp_path / "out/spot-swap-source.receipt.json").read_bytes() == proof_raw
    assert report["request_bytes"] == len(request_raw)
    assert report["request_sha256"] == source_opening._sha256_bytes(request_raw)
    assert report["proof_bytes"] == len(proof_raw)
    assert report["proof_sha256"] == source_opening._sha256_bytes(proof_raw)


def test_run_rejects_if_persisted_request_differs_from_supplied_bytes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request_raw = json.dumps(_request(), separators=(",", ":")).encode()
    proof_raw = json.dumps(_proof(), separators=(",", ":")).encode()
    outputs = iter((request_raw, proof_raw))
    monkeypatch.setattr(source_opening, "_run", lambda *_args, **_kwargs: next(outputs))
    monkeypatch.setattr(
        source_opening,
        "_sha256_file",
        lambda path: source_opening.SOURCE_CLI_SHA256 if path.name == "source-cli" else "11" * 32,
    )
    original_write = source_opening._write_new

    def mutate_request_after_write(path: Path, raw: bytes) -> None:
        original_write(path, raw)
        if path.name == "spot-swap-source.request.json":
            path.write_bytes(raw + b"\n")

    monkeypatch.setattr(source_opening, "_write_new", mutate_request_after_write)
    for name in ("generator", "source-cli", "r0vm"):
        (tmp_path / name).write_bytes(name.encode())

    with pytest.raises(SourceOpeningError, match="persisted request bytes changed"):
        source_opening.run(
            generator=tmp_path / "generator",
            source_cli=tmp_path / "source-cli",
            r0vm=tmp_path / "r0vm",
            output_directory=tmp_path / "out",
            timeout_seconds=1,
        )
