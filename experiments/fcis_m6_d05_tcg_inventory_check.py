"""Deterministic D05 checker and adversarial source-inventory witness."""

from __future__ import annotations

import json
import sys
from dataclasses import replace
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fcis_tcg_inventory import (  # noqa: E402
    FCISM6TCGInventoryError,
    PublisherKindV1,
    PublisherSpecV1,
    inventory_payload_v1,
)
from tools.build_fcis_m6_d05_tcg_inventory import (  # noqa: E402
    DEFAULT_CONFIG_PATH,
    DEFAULT_OUTPUT_PATH,
    _load_inventory,
    build_payload,
)


def _read_vector() -> dict[str, object]:
    value = json.loads((_ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("D05 vector must be an object")
    return cast(dict[str, object], value)


def _assert_root_changes(
    label: str,
    baseline: dict[str, object],
    mutated: dict[str, object],
) -> None:
    if baseline["publisher_inventory_root"] == mutated["publisher_inventory_root"]:
        raise AssertionError(f"{label} did not change publisher inventory root")
    if baseline["topology_root"] == mutated["topology_root"]:
        raise AssertionError(f"{label} did not change anchored topology root")


def run_checks() -> None:
    baseline = build_payload(_ROOT / DEFAULT_CONFIG_PATH)
    vector = _read_vector()
    if baseline != vector:
        raise AssertionError("D05 vector is not the independently regenerated payload")
    if "instance_root" in baseline or "certificate" in baseline:
        raise AssertionError("D05 payload unexpectedly accepts a runtime certificate")

    inventory = _load_inventory(_ROOT / DEFAULT_CONFIG_PATH)
    inserted = PublisherSpecV1(
        publisher_id="inserted_api_surface",
        kind=PublisherKindV1.API,
        entrypoint="src.integration.api_server:inserted_surface",
        source_paths=("src/integration/api_server.py",),
        effect_capable=True,
        authority_sink=False,
    )
    inserted_inventory = replace(
        inventory,
        publishers=tuple(
            sorted(
                (*inventory.publishers, inserted),
                key=lambda item: item.publisher_id.encode("utf-8"),
            )
        ),
    )
    _assert_root_changes(
        "inserted publisher",
        baseline,
        inventory_payload_v1(inserted_inventory),
    )

    try:
        omitted_inventory = replace(
            inventory,
            publishers=tuple(
                item for item in inventory.publishers if item.publisher_id != "proof_verifier"
            ),
        )
        inventory_payload_v1(omitted_inventory)
    except FCISM6TCGInventoryError:
        pass
    else:
        raise AssertionError("omitted required publisher was accepted")

    source = inventory.sources[0]
    altered_source = replace(
        source,
        source_sha256=("0" * 63 + "1")
        if source.source_sha256 != ("0" * 63 + "1")
        else ("0" * 63 + "2"),
    )
    altered_source_inventory = replace(
        inventory,
        sources=(altered_source, *inventory.sources[1:]),
    )
    _assert_root_changes(
        "source-byte digest substitution",
        baseline,
        inventory_payload_v1(altered_source_inventory),
    )

    altered_configuration = replace(
        inventory,
        configuration_sha256=("f" * 64),
    )
    _assert_root_changes(
        "configuration substitution",
        baseline,
        inventory_payload_v1(altered_configuration),
    )

    try:
        replace(inventory, publishers=(inventory.publishers[0], inventory.publishers[0]))
        duplicate_inventory = replace(
            inventory,
            publishers=(inventory.publishers[0], inventory.publishers[0]),
        )
        inventory_payload_v1(duplicate_inventory)
    except FCISM6TCGInventoryError:
        pass
    else:
        raise AssertionError("duplicate publisher ID was accepted")


if __name__ == "__main__":
    run_checks()
    print("D05_TCG_INVENTORY_MATCH")
