"""Regenerate the synthetic Python/Rust custody-binding correspondence vector.

Replay: python3 -B -m experiments.v3_custody_successor_v1.render_vectors
Fixture release metadata carries no cryptographic or publication authority.
"""

from __future__ import annotations

from pathlib import Path

from src.core.global_settlement_types_v1 import canonical_global_bytes_v1
from src.core.lane_module_release_route_binding_v1 import (
    bind_asset_transfer_lane_output_to_custody_release_route_v1,
)
from tests.core.test_asset_transfer_custody_release_route_binding_v1 import _honest_candidate
from tests.core.test_asset_transfer_custody_semantics_v1 import _governance

ROOT = Path(__file__).resolve().parents[2]
VECTOR_PATH = "tests/data/asset_transfer_custody_release_binding_v1_golden.json"


def vector_bytes() -> bytes:
    governance = _governance()
    occurrence, module_input, accepted, candidate = _honest_candidate(governance, custody_atoms=7)
    bound = bind_asset_transfer_lane_output_to_custody_release_route_v1(candidate)
    return canonical_global_bytes_v1({
        "schema": "zenodex/asset-transfer-custody-binding-test-vector/v1",
        "authority": "NONE",
        "profile": governance.profile,
        "lanes": governance.profile.lane_registry,
        "coordinators": governance.profile.lane_coordinator_registry,
        "routes": governance.profile.route_registry,
        "policy_registry": governance.policy_registry,
        "asset_policy_registry": governance.asset_policy_registry.to_canonical(),
        "occurrence": occurrence,
        "module_input": module_input.to_canonical(),
        "accepted": {
            "statement_root": accepted.statement_root,
            "post_state": accepted.post_state,
            "effects": accepted.effects,
            "module_journal": accepted.module_journal,
            "private_port": accepted.private_port,
        },
        "binding_root": bound.binding_root,
    })


def main() -> None:
    (ROOT / VECTOR_PATH).write_bytes(vector_bytes())
    print(VECTOR_PATH)


if __name__ == "__main__":
    main()
