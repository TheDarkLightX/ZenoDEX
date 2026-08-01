"""Deterministic K01 inventory checker and adversarial source witness."""

from __future__ import annotations

import json
import sys
from dataclasses import replace
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fcis_m6_k01_entrypoint_inventory import (  # noqa: E402
    FCISM6K01Error,
    K01CommitRequirementV1,
    K01EntrypointV1,
    K01LegacyStatusV1,
    K01ReachabilityV1,
    entrypoint_inventory_root_v1,
    inventory_payload_v1,
)
from tools.build_fcis_m6_k01_entrypoint_inventory import (  # noqa: E402
    DEFAULT_CONFIG_PATH,
    DEFAULT_OUTPUT_PATH,
    _load_inventory,
    build_payload,
)


def _read_vector() -> dict[str, object]:
    value = json.loads((_ROOT / DEFAULT_OUTPUT_PATH).read_text(encoding="utf-8"))
    if type(value) is not dict:
        raise AssertionError("K01 vector must be an object")
    return cast(dict[str, object], value)


def _entries(payload: dict[str, object]) -> tuple[dict[str, object], ...]:
    raw = payload.get("entrypoints")
    if type(raw) is not list or not all(type(item) is dict for item in raw):
        raise AssertionError("K01 vector entrypoints are not object rows")
    return tuple(cast(dict[str, object], item) for item in raw)


def _assert_root_changes(
    label: str, baseline: dict[str, object], mutated: dict[str, object]
) -> None:
    if baseline["entrypoint_inventory_root"] == mutated["entrypoint_inventory_root"]:
        raise AssertionError(f"{label} did not change the K01 root")


def run_checks() -> None:
    baseline = build_payload(_ROOT / DEFAULT_CONFIG_PATH)
    vector = _read_vector()
    if baseline != vector:
        raise AssertionError("K01 vector is not the independently regenerated payload")
    rows = _entries(baseline)
    if len(rows) != 15:
        raise AssertionError(f"expected 15 K01 rows, found {len(rows)}")
    if baseline["coverage_status"] != "reviewed_source_set_only":
        raise AssertionError("K01 completeness boundary is not explicit")
    required = {
        "api_http_ingress",
        "background_outbox_delivery",
        "durable_recovery_worker",
        "durable_state_adapter",
        "entitlement_migration_worker",
        "governance_administrator",
        "legacy_fcis_runtime",
        "operator_cli",
        "proof_verifier",
    }
    if {cast(str, row["publisher_id"]) for row in rows}.intersection(required) != required:
        raise AssertionError("K01 omitted one of the required D05 publisher surfaces")
    if not any(row["value_moving"] is True for row in rows):
        raise AssertionError("K01 has no value-moving surface")
    if not any(row["legacy_status"] == "legacy_path" for row in rows):
        raise AssertionError("K01 has no explicit legacy path")
    if not any(row["runtime_reachability_evidence"] == "unmounted_research_model" for row in rows):
        raise AssertionError("K01 has no explicit unmounted research boundary")

    inventory = _load_inventory(_ROOT / DEFAULT_CONFIG_PATH)

    try:
        replace(
            inventory,
            entrypoints=tuple(
                item for item in inventory.entrypoints if item.publisher_id != "proof_verifier"
            ),
        )
    except FCISM6K01Error:
        pass
    else:
        raise AssertionError("K01 accepted an inventory missing the proof verifier surface")

    first = inventory.entrypoints[0]
    inserted = K01EntrypointV1(
        publisher_id="inserted_unreviewed_surface",
        kind=first.kind,
        symbol_path="src/integration/api_server.py:inserted_surface",
        caller="unreviewed caller",
        input_type="unreviewed input",
        state_effect_touched="unreviewed effect",
        required_anf_commit_port_call=K01CommitRequirementV1.AUTHENTICATED_COMMAND_TO_ANF_TO_UNIQUE_COMMIT_PORT,
        legacy_status=K01LegacyStatusV1.UNVERIFIED_REPOSITORY_CANDIDATE,
        runtime_reachability_evidence=K01ReachabilityV1.UNVERIFIED_REPOSITORY_CANDIDATE,
        value_moving=True,
        authority_sink=False,
        source_paths=("src/integration/api_server.py",),
    )
    inserted_inventory = replace(
        inventory,
        entrypoints=tuple(
            sorted(
                (*inventory.entrypoints, inserted),
                key=lambda item: item.publisher_id.encode("utf-8"),
            )
        ),
    )
    _assert_root_changes(
        "inserted unreviewed surface",
        inventory_payload_v1(inventory),
        inventory_payload_v1(inserted_inventory),
    )

    altered_source = replace(
        inventory.sources[0],
        source_sha256=("0" * 63 + "1")
        if inventory.sources[0].source_sha256 != ("0" * 63 + "1")
        else ("0" * 63 + "2"),
    )
    altered_sources_inventory = replace(
        inventory,
        sources=(altered_source, *inventory.sources[1:]),
    )
    _assert_root_changes(
        "source-byte digest substitution",
        inventory_payload_v1(inventory),
        inventory_payload_v1(altered_sources_inventory),
    )

    proof = next(item for item in inventory.entrypoints if item.publisher_id == "proof_verifier")
    try:
        replace(proof, value_moving=True)
    except FCISM6K01Error:
        pass
    else:
        raise AssertionError("K01 allowed the proof verifier to become value-moving")

    legacy = next(
        item for item in inventory.entrypoints if item.publisher_id == "legacy_fcis_runtime"
    )
    try:
        replace(
            legacy,
            required_anf_commit_port_call=K01CommitRequirementV1.ANF_VERIFIED_ATOMIC_PUBLICATION_PORT,
        )
    except FCISM6K01Error:
        pass
    else:
        raise AssertionError("K01 allowed a legacy path to bypass the post-switch rejection rule")

    if entrypoint_inventory_root_v1(inventory) != baseline["entrypoint_inventory_root"]:
        raise AssertionError("K01 root helper disagrees with the generated vector")


if __name__ == "__main__":
    run_checks()
    print("K01_ENTRYPOINT_INVENTORY_MATCH")
