"""Build the pinned K04 topology anchor from D05 and K01 evidence."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fcis_m6_k04_topology_anchor import (  # noqa: E402
    FCIS_M6_K04_SCHEMA_V1,
    K04Error,
    K04TopologyAnchorV1,
    topology_anchor_payload_v1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402
from tools.build_fcis_m6_d05_tcg_inventory import build_payload as build_d05_payload  # noqa: E402
from tools.build_fcis_m6_k01_entrypoint_inventory import (  # noqa: E402
    DEFAULT_CONFIG_PATH as K01_CONFIG_PATH,
)
from tools.build_fcis_m6_k01_entrypoint_inventory import (  # noqa: E402
    build_payload as build_k01_payload,
)

DEFAULT_CONFIG_PATH = Path("config/deploy/fcis_m6_k04_topology_anchor_v1.json")
DEFAULT_OUTPUT_PATH = Path("docs/research/m6_tasks/TASK_K04_TOPOLOGY_ANCHOR_V1.json")


def _text(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise K04Error(f"{name} must be a nonempty string")
    return value


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or value != value.lower()
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise K04Error(f"{name} must be a lowercase digest")
    return value


def _sorted_strings(value: object, name: str) -> tuple[str, ...]:
    if (
        type(value) is not list
        or not value
        or any(type(item) is not str or not item for item in value)
    ):
        raise K04Error(f"{name} must be a nonempty string list")
    values = tuple(cast(str, item) for item in value)
    if values != tuple(sorted(values, key=lambda item: item.encode("utf-8"))):
        raise K04Error(f"{name} is not canonically ordered")
    if len(set(values)) != len(values):
        raise K04Error(f"{name} contains duplicates")
    return values


def _load_json(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise K04Error(f"K04 config is not an object: {path}")
    return cast(dict[str, object], value)


def _load_config(path: Path) -> dict[str, object]:
    raw = _load_json(path)
    expected = {
        "schema",
        "profile_id",
        "expected_d05_inventory_root",
        "expected_d05_topology_root",
        "expected_k01_entrypoint_inventory_root",
        "unique_port_id",
        "expected_publisher_ids",
        "pinned_topology_anchor_root",
        "nonclaims",
    }
    if set(raw) != expected:
        raise K04Error("K04 config fields are not exact")
    if raw["schema"] != "zenodex/fcis/m6/k04/topology-anchor-config/v1":
        raise K04Error("K04 config schema is wrong")
    nonclaims = raw["nonclaims"]
    if (
        type(nonclaims) is not list
        or not nonclaims
        or any(type(item) is not str or not item for item in nonclaims)
    ):
        raise K04Error("K04 nonclaims must be a nonempty string list")
    _text(raw["profile_id"], "profile_id")
    _digest(raw["expected_d05_inventory_root"], "expected_d05_inventory_root")
    _digest(raw["expected_d05_topology_root"], "expected_d05_topology_root")
    _digest(raw["expected_k01_entrypoint_inventory_root"], "expected_k01_entrypoint_inventory_root")
    _text(raw["unique_port_id"], "unique_port_id")
    _sorted_strings(raw["expected_publisher_ids"], "expected_publisher_ids")
    _digest(raw["pinned_topology_anchor_root"], "pinned_topology_anchor_root")
    return raw


def _source_paths(payload: dict[str, object]) -> set[str]:
    raw = payload.get("sources")
    if type(raw) is not list:
        raise K04Error("upstream sources are not a list")
    paths: set[str] = set()
    for index, item in enumerate(raw):
        if type(item) is not dict or type(item.get("path")) is not str:
            raise K04Error(f"upstream source row {index} is malformed")
        paths.add(cast(str, item["path"]))
    return paths


def derive_payload(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Derive K04 without applying the external pinned-root comparison."""

    config = _load_config(config_path.resolve())
    d05 = build_d05_payload()
    k01 = build_k01_payload(_ROOT / K01_CONFIG_PATH)
    if d05["publisher_inventory_root"] != config["expected_d05_inventory_root"]:
        raise K04Error("D05 publisher inventory root differs from the K04 pin")
    if d05["topology_root"] != config["expected_d05_topology_root"]:
        raise K04Error("D05 topology root differs from the K04 pin")
    if k01["entrypoint_inventory_root"] != config["expected_k01_entrypoint_inventory_root"]:
        raise K04Error("K01 entrypoint inventory root differs from the K04 pin")
    publisher_rows = k01.get("entrypoints")
    if type(publisher_rows) is not list:
        raise K04Error("K01 entrypoints are not a list")
    publisher_ids = tuple(
        sorted(
            {
                cast(str, item["publisher_id"])
                for item in publisher_rows
                if type(item) is dict and type(item.get("publisher_id")) is str
            },
            key=lambda item: item.encode("utf-8"),
        )
    )
    expected_publisher_ids = _sorted_strings(
        config["expected_publisher_ids"], "expected_publisher_ids"
    )
    if publisher_ids != expected_publisher_ids:
        raise K04Error("K01 publisher IDs differ from the K04 pin")
    anchor = K04TopologyAnchorV1(
        d05_inventory_root=cast(str, d05["publisher_inventory_root"]),
        d05_topology_root=cast(str, d05["topology_root"]),
        k01_entrypoint_inventory_root=cast(str, k01["entrypoint_inventory_root"]),
        unique_port_id=_text(config["unique_port_id"], "unique_port_id"),
        publisher_ids=publisher_ids,
        source_paths=tuple(
            sorted(
                _source_paths(d05).union(_source_paths(k01)),
                key=lambda item: item.encode("utf-8"),
            )
        ),
    )
    return {
        **topology_anchor_payload_v1(anchor),
        "pinned_topology_anchor_root": cast(str, config["pinned_topology_anchor_root"]),
    }


def build_payload(config_path: Path = _ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Derive K04 and require the externally pinned topology anchor root."""

    payload = derive_payload(config_path)
    if payload["topology_anchor_root"] != payload["pinned_topology_anchor_root"]:
        raise K04Error("derived K04 topology anchor differs from the pinned root")
    if payload["schema"] != FCIS_M6_K04_SCHEMA_V1:
        raise K04Error("K04 output schema is wrong")
    return payload


def main(argv: list[str] | None = None) -> int:
    args = list(argv or sys.argv[1:])
    config = _ROOT / DEFAULT_CONFIG_PATH
    output = _ROOT / DEFAULT_OUTPUT_PATH
    check = False
    print_derived = False
    index = 0
    while index < len(args):
        token = args[index]
        if token == "--check":
            check = True
        elif token == "--print-derived":
            print_derived = True
        elif token == "--config" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            config = candidate if candidate.is_absolute() else _ROOT / candidate
        elif token == "--output" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            output = candidate if candidate.is_absolute() else _ROOT / candidate
        else:
            raise SystemExit(f"unknown or incomplete argument: {token}")
        index += 1
    payload = derive_payload(config) if print_derived else build_payload(config)
    if print_derived:
        print("K04_DERIVED_TOPOLOGY_ANCHOR", payload["topology_anchor_root"])
        return 0
    encoded = canonical_json_bytes(payload) + b"\n"
    if check:
        if output.read_bytes() != encoded:
            raise SystemExit("FAIL: K04 topology anchor vector is stale")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(encoded)
    print("K04_TOPOLOGY_ANCHOR_MATCH", payload["topology_anchor_root"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
