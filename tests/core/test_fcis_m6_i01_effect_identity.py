"""I01 stable semantic effect-identity vectors and mutation checks."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Final, cast

from src.core.fcis_durable_retraction import derive_effect_id, tagged_digest

_VECTOR_PATH: Final[Path] = (
    Path(__file__).resolve().parents[2]
    / "docs/research/m6_tasks/TASK_I01_EFFECT_ID_VECTORS_V1.json"
)
_VECTOR_FIELDS: Final[frozenset[str]] = frozenset(
    {
        "vector_id",
        "commit_id",
        "ordinal",
        "destination",
        "payload_root",
        "writer_profile_root",
        "adapter_profile_root",
        "effect_id",
    }
)


def _vectors() -> list[dict[str, object]]:
    payload = cast(dict[str, object], json.loads(_VECTOR_PATH.read_text(encoding="utf-8")))
    assert payload["schema_version"] == "zenodex.fcis.m6.i01.effect-id-vectors.v1"
    assert payload["task_id"] == "I01"
    assert payload["preimage_fields"] == [
        "commit_id",
        "ordinal",
        "destination",
        "payload_root",
        "writer_profile_root",
    ]
    vectors = payload["vectors"]
    assert type(vectors) is list and vectors
    rows = cast(list[dict[str, object]], vectors)
    for row in rows:
        assert set(row) == _VECTOR_FIELDS
    return rows


def _derive(row: dict[str, object], *, adapter_profile_root: str | None = None) -> str:
    return cast(
        str,
        derive_effect_id(
            commit_id=cast(str, row["commit_id"]),
            ordinal=cast(int, row["ordinal"]),
            destination=cast(str, row["destination"]),
            payload_root=cast(str, row["payload_root"]),
            writer_profile_root=cast(str, row["writer_profile_root"]),
            adapter_profile_root=adapter_profile_root
            if adapter_profile_root is not None
            else cast(str, row["adapter_profile_root"]),
        ),
    )


def test_i01_vectors_recompute_exactly() -> None:
    for row in _vectors():
        assert _derive(row) == row["effect_id"]
        assert _derive(row) == _derive(row)


def test_i01_adapter_profile_rotation_does_not_mint_a_new_semantic_effect() -> None:
    for row in _vectors():
        rotated = tagged_digest(f"rotated/{row['vector_id']}")
        assert _derive(row, adapter_profile_root=rotated) == row["effect_id"]


def test_i01_semantic_preimage_mutations_change_identity() -> None:
    for row in _vectors():
        baseline = _derive(row)
        commit_mutation = dict(row, commit_id=tagged_digest("mutation/commit"))
        ordinal_mutation = dict(row, ordinal=cast(int, row["ordinal"]) + 1)
        destination_mutation = dict(row, destination="destination.mutated")
        payload_mutation = dict(row, payload_root=tagged_digest("mutation/payload"))
        writer_mutation = dict(row, writer_profile_root=tagged_digest("mutation/writer"))
        for mutation in (
            commit_mutation,
            ordinal_mutation,
            destination_mutation,
            payload_mutation,
            writer_mutation,
        ):
            assert _derive(cast(dict[str, object], mutation)) != baseline
