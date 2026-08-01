"""Recompute and verify the retained C03 canonical vector."""
from __future__ import annotations

import json
from pathlib import Path

from src.core.fcis_entitlement_key_v1 import EntitlementKeyV1
from src.core.fcis_entitlement_migration_codec_v1 import (
    canonical_entitlement_state_root_v1,
    canonical_sha256_migration_manifest_v1,
    encode_entitlement_state_v1,
    encode_representation_migration_manifest_v1,
)
from src.core.fcis_entitlement_migration_values_v1 import (
    EntitlementStateEntryV1,
    EntitlementStateV1,
    RepresentationMigrationManifestV1,
)
from src.core.fcis_m6_profile_ids import (
    AGQE_REPRESENTATION_PROFILE_ID_V1,
    FIXED_ROLE_ORDER_ID_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
    SRGD_REPRESENTATION_PROFILE_ID_V1,
)

_VECTOR_PATH = Path("docs/research/m6_tasks/TASK_C03_MIGRATION_VECTOR.json")


def main() -> int:
    vector = json.loads(_VECTOR_PATH.read_text(encoding="utf-8"))
    key = EntitlementKeyV1(
        "protocol-fees",
        "USDC",
        SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
        FIXED_ROLE_ORDER_ID_V1,
    )
    old_state = EntitlementStateV1(
        key,
        SRGD_REPRESENTATION_PROFILE_ID_V1,
        (EntitlementStateEntryV1("entry-0", (3, -1, -2)),),
    )
    new_state = EntitlementStateV1(
        key,
        AGQE_REPRESENTATION_PROFILE_ID_V1,
        (EntitlementStateEntryV1("entry-0", (-3, 1, 2)),),
    )
    manifest = RepresentationMigrationManifestV1(
        old_state,
        new_state,
        "migration-map-v1",
        "0x" + "11" * 32,
        7,
    )
    assert encode_entitlement_state_v1(old_state).decode() == vector["old_state"][
        "canonical_bytes_utf8"
    ]
    assert canonical_entitlement_state_root_v1(old_state) == vector["old_state"]["root"]
    assert encode_entitlement_state_v1(new_state).decode() == vector["new_state"][
        "canonical_bytes_utf8"
    ]
    assert canonical_entitlement_state_root_v1(new_state) == vector["new_state"]["root"]
    assert encode_representation_migration_manifest_v1(manifest).decode() == vector[
        "manifest"
    ]["canonical_bytes_utf8"]
    assert canonical_sha256_migration_manifest_v1(manifest) == vector["manifest"][
        "sha256_hex"
    ]
    print("C03_VECTOR_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
