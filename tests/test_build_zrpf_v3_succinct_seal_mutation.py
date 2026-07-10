from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from tools import build_zrpf_v3_succinct_seal_mutation as builder


def _receipt() -> dict[str, object]:
    return {
        "inner": {
            "Succinct": {
                "seal": [10, 20, 30],
                "control_id": [1],
                "claim": {"Pruned": [2]},
                "hashfn": "sha-256",
                "verifier_parameters": [3],
                "control_inclusion_proof": [4],
            }
        },
        "journal": {"bytes": [5]},
        "metadata": {"verifier_parameters": [6]},
    }


def _write_canonical(path: Path, value: object) -> None:
    path.write_bytes(builder.canonical_json_bytes(value))


def test_builder_changes_only_the_pinned_seal_word(tmp_path: Path) -> None:
    source_path = tmp_path / "source.json"
    output_path = tmp_path / "mutated.json"
    source = _receipt()
    _write_canonical(source_path, source)

    report = builder.build_mutation(source_path, output_path)

    mutated = json.loads(output_path.read_bytes())
    expected = copy.deepcopy(source)
    expected["inner"]["Succinct"]["seal"][1] = 21  # type: ignore[index]
    assert mutated == expected
    assert report["control_built"] is True
    assert report["python_verifies_risc0_seal"] is False
    assert report["mutation"] == {
        "kind": "succinct_seal_word_xor_lsb_v1",
        "seal_word_count": 3,
        "seal_word_index": 1,
        "seal_word_mutated": 21,
        "seal_word_original": 20,
        "xor_mask": 1,
    }


def test_builder_rejects_noncanonical_duplicate_and_non_succinct_inputs(
    tmp_path: Path,
) -> None:
    output = tmp_path / "mutated.json"
    noncanonical = tmp_path / "noncanonical.json"
    noncanonical.write_text(json.dumps(_receipt(), indent=2), encoding="utf-8")
    with pytest.raises(builder.MutationBuildError, match="not canonical"):
        builder.build_mutation(noncanonical, output)

    duplicate = tmp_path / "duplicate.json"
    duplicate.write_text(
        '{"inner":{"Succinct":{"seal":[1,2],"seal":[1,2]}},"journal":{},"metadata":{}}',
        encoding="utf-8",
    )
    with pytest.raises(builder.MutationBuildError, match="duplicate JSON key"):
        builder.build_mutation(duplicate, output)

    non_succinct = tmp_path / "non-succinct.json"
    value = _receipt()
    value["inner"] = {"Composite": {}}
    _write_canonical(non_succinct, value)
    with pytest.raises(builder.MutationBuildError, match="not structurally Succinct"):
        builder.build_mutation(non_succinct, output)


def test_builder_uses_create_new_output(tmp_path: Path) -> None:
    source_path = tmp_path / "source.json"
    output_path = tmp_path / "mutated.json"
    _write_canonical(source_path, _receipt())
    output_path.write_bytes(b"preserve")

    with pytest.raises(builder.MutationBuildError, match="create-new"):
        builder.build_mutation(source_path, output_path)
    assert output_path.read_bytes() == b"preserve"
