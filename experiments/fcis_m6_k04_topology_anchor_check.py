"""Deterministic K04 topology-anchor checker and drift witnesses."""

from __future__ import annotations

import json
import sys
from dataclasses import replace
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fcis_m6_k04_topology_anchor import (  # noqa: E402
    K04Error,
    K04TopologyAnchorV1,
    topology_anchor_payload_v1,
    topology_anchor_root_v1,
)
from tools.build_fcis_m6_k04_topology_anchor import (  # noqa: E402
    DEFAULT_CONFIG_PATH,
    DEFAULT_OUTPUT_PATH,
    build_payload,
    derive_payload,
)


def _read_vector() -> dict[str, object]:
    value = json.loads((_ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("K04 vector must be an object")
    return cast(dict[str, object], value)


def _anchor(payload: dict[str, object]) -> K04TopologyAnchorV1:
    publisher_ids = payload.get("publisher_ids")
    source_paths = payload.get("source_paths")
    if type(publisher_ids) is not list or type(source_paths) is not list:
        raise AssertionError("K04 vector collections are malformed")
    return K04TopologyAnchorV1(
        d05_inventory_root=cast(str, payload["d05_inventory_root"]),
        d05_topology_root=cast(str, payload["d05_topology_root"]),
        k01_entrypoint_inventory_root=cast(str, payload["k01_entrypoint_inventory_root"]),
        unique_port_id=cast(str, payload["unique_port_id"]),
        publisher_ids=tuple(cast(str, item) for item in publisher_ids),
        source_paths=tuple(cast(str, item) for item in source_paths),
    )


def _assert_root_changes(
    label: str, baseline: dict[str, object], mutated: dict[str, object]
) -> None:
    if baseline["topology_anchor_root"] == mutated["topology_anchor_root"]:
        raise AssertionError(f"{label} did not change the topology anchor root")


def run_checks() -> None:
    baseline = build_payload(_ROOT / DEFAULT_CONFIG_PATH)
    vector = _read_vector()
    if baseline != vector:
        raise AssertionError("K04 vector is not the independently regenerated payload")
    if baseline["pinned_topology_anchor_root"] != baseline["topology_anchor_root"]:
        raise AssertionError("K04 derived root does not equal its pinned root")
    if len(cast(list[object], baseline["publisher_ids"])) != 15:
        raise AssertionError("K04 publisher set is not the K01 set")
    if len(cast(list[object], baseline["source_paths"])) < 20:
        raise AssertionError("K04 source union unexpectedly shrank")

    anchor = _anchor(baseline)
    inserted = replace(
        anchor,
        publisher_ids=tuple(
            sorted(
                (*anchor.publisher_ids, "inserted_unreviewed_publisher"),
                key=lambda item: item.encode("utf-8"),
            )
        ),
    )
    _assert_root_changes(
        "publisher insertion",
        topology_anchor_payload_v1(anchor),
        topology_anchor_payload_v1(inserted),
    )

    crossed_d05 = replace(
        anchor,
        d05_topology_root="0" * 64,
    )
    _assert_root_changes(
        "D05 topology substitution",
        topology_anchor_payload_v1(anchor),
        topology_anchor_payload_v1(crossed_d05),
    )

    crossed_source = replace(
        anchor,
        source_paths=tuple(
            sorted(
                (*anchor.source_paths, "src/core/unreviewed_writer.py"),
                key=lambda item: item.encode("utf-8"),
            )
        ),
    )
    _assert_root_changes(
        "source-set insertion",
        topology_anchor_payload_v1(anchor),
        topology_anchor_payload_v1(crossed_source),
    )

    try:
        K04TopologyAnchorV1(
            d05_inventory_root=anchor.d05_inventory_root,
            d05_topology_root=anchor.d05_topology_root,
            k01_entrypoint_inventory_root=anchor.k01_entrypoint_inventory_root,
            unique_port_id=anchor.unique_port_id,
            publisher_ids=tuple(reversed(anchor.publisher_ids)),
            source_paths=anchor.source_paths,
        )
    except K04Error:
        pass
    else:
        raise AssertionError("K04 accepted a noncanonical publisher ordering")

    if topology_anchor_root_v1(anchor) != baseline["topology_anchor_root"]:
        raise AssertionError("K04 root helper disagrees with generated vector")
    derived = derive_payload(_ROOT / DEFAULT_CONFIG_PATH)
    if derived["topology_anchor_root"] != baseline["topology_anchor_root"]:
        raise AssertionError("K04 derived and checked payloads differ")


if __name__ == "__main__":
    run_checks()
    print("K04_TOPOLOGY_ANCHOR_MATCH")
