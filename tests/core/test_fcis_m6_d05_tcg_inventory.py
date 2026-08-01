from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.fcis_tcg_inventory import (
    FCISM6TCGInventoryError,
    PublisherKindV1,
    PublisherSpecV1,
    TCGPublisherInventoryV1,
    inventory_payload_v1,
)
from tools.build_fcis_m6_d05_tcg_inventory import (
    DEFAULT_CONFIG_PATH,
    DEFAULT_OUTPUT_PATH,
    _load_inventory,
    build_payload,
)

_ROOT = Path(__file__).resolve().parents[2]


def _inventory() -> TCGPublisherInventoryV1:
    return _load_inventory(_ROOT / DEFAULT_CONFIG_PATH)


def test_source_derived_payload_matches_frozen_vector() -> None:
    expected = json.loads((_ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    assert build_payload(_ROOT / DEFAULT_CONFIG_PATH) == expected


def test_inserted_publisher_changes_both_external_roots() -> None:
    inventory = _inventory()
    baseline = inventory_payload_v1(inventory)
    inserted = PublisherSpecV1(
        publisher_id="inserted_api_surface",
        kind=PublisherKindV1.API,
        entrypoint="src.integration.api_server:inserted_surface",
        source_paths=("src/integration/api_server.py",),
        effect_capable=True,
        authority_sink=False,
    )
    mutated = replace(
        inventory,
        publishers=tuple(
            sorted(
                (*inventory.publishers, inserted),
                key=lambda item: item.publisher_id.encode("utf-8"),
            )
        ),
    )
    changed = inventory_payload_v1(mutated)
    assert changed["publisher_inventory_root"] != baseline["publisher_inventory_root"]
    assert changed["topology_root"] != baseline["topology_root"]


def test_omitted_required_publisher_rejects() -> None:
    inventory = _inventory()
    with pytest.raises(FCISM6TCGInventoryError, match="proof_verifier"):
        replace(
            inventory,
            publishers=tuple(
                item for item in inventory.publishers if item.publisher_id != "proof_verifier"
            ),
        )


def test_source_digest_substitution_changes_external_roots() -> None:
    inventory = _inventory()
    source = inventory.sources[0]
    replacement = "0" * 63 + ("1" if source.source_sha256 != "0" * 64 else "2")
    mutated = replace(
        inventory,
        sources=(replace(source, source_sha256=replacement), *inventory.sources[1:]),
    )
    baseline = inventory_payload_v1(inventory)
    changed = inventory_payload_v1(mutated)
    assert changed["publisher_inventory_root"] != baseline["publisher_inventory_root"]
    assert changed["topology_root"] != baseline["topology_root"]


def test_unanchored_publisher_source_rejects() -> None:
    inventory = _inventory()
    publisher = inventory.publishers[0]
    with pytest.raises(FCISM6TCGInventoryError, match="unanchored source"):
        replace(
            inventory,
            publishers=(
                replace(
                    publisher,
                    source_paths=("src/integration/missing_publisher.py",),
                ),
                *inventory.publishers[1:],
            ),
        )


def test_duplicate_publisher_id_rejects() -> None:
    inventory = _inventory()
    with pytest.raises(FCISM6TCGInventoryError, match="duplicate IDs"):
        replace(
            inventory,
            publishers=(inventory.publishers[0], inventory.publishers[0]),
        )
