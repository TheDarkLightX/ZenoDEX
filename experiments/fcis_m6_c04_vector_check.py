"""Recompute and verify the retained C04 sign-dual transport vector."""
from __future__ import annotations

import json
from pathlib import Path

from src.core.fcis_entitlement_key_v1 import EntitlementKeyV1
from src.core.fcis_entitlement_migration_codec_v1 import (
    canonical_entitlement_state_root_v1,
    encode_entitlement_state_v1,
)
from src.core.fcis_entitlement_migration_values_v1 import (
    EntitlementStateEntryV1,
    EntitlementStateV1,
)
from src.core.fcis_entitlement_transport_v1 import (
    transport_agqe_to_srgd_v1,
    transport_srgd_to_agqe_v1,
)
from src.core.fcis_m6_profile_ids import (
    AGQE_REPRESENTATION_PROFILE_ID_V1,
    FIXED_ROLE_ORDER_ID_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
    SRGD_REPRESENTATION_PROFILE_ID_V1,
)

_VECTOR_PATH = Path("docs/research/m6_tasks/TASK_C04_SIGN_DUAL_VECTOR.json")


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
        (
            EntitlementStateEntryV1("entry-0", (3, -1, -2)),
            EntitlementStateEntryV1("entry-1", (-4, 2, 2)),
        ),
    )
    new_state = EntitlementStateV1(
        key,
        AGQE_REPRESENTATION_PROFILE_ID_V1,
        (
            EntitlementStateEntryV1("entry-0", (-3, 1, 2)),
            EntitlementStateEntryV1("entry-1", (4, -2, -2)),
        ),
    )
    assert vector["source_representation_id"] == old_state.representation_id
    assert vector["target_representation_id"] == new_state.representation_id
    assert transport_srgd_to_agqe_v1(old_state, expected_target=new_state) == (
        new_state
    )
    assert transport_agqe_to_srgd_v1(new_state, expected_target=old_state) == (
        old_state
    )
    assert encode_entitlement_state_v1(old_state).decode() == vector["old_state"][
        "canonical_bytes_utf8"
    ]
    assert canonical_entitlement_state_root_v1(old_state) == vector["old_state"][
        "root"
    ]
    assert encode_entitlement_state_v1(new_state).decode() == vector["new_state"][
        "canonical_bytes_utf8"
    ]
    assert canonical_entitlement_state_root_v1(new_state) == vector["new_state"][
        "root"
    ]
    expected_mappings = [
        {
            "entry_id": entry.entry_id,
            "source_coordinates": list(entry.coordinates),
            "target_coordinates": list(
                tuple(-coordinate for coordinate in entry.coordinates)
            ),
        }
        for entry in old_state.entries
    ]
    assert vector["entry_mappings"] == expected_mappings
    print("C04_VECTOR_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
