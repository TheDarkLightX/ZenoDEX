from __future__ import annotations

import pytest

from src.core.confidential_extension_receipts import (
    CONFIDENTIAL_MEASUREMENT_REGISTRY_SCHEMA,
    confidential_measurement_registry_hash,
)

NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
POLICY_DIGEST = "0x" + ("d" * 64)


def _measurement_registry() -> dict:
    registry = {
        "schema": CONFIDENTIAL_MEASUREMENT_REGISTRY_SCHEMA,
        "registry_id": "confidential-beta-registry-v1",
        "entries": [
            {
                "provider_id": "provider-1",
                "measurement": f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
                "policy_digest": POLICY_DIGEST,
                "valid_from_epoch": 1,
                "valid_until_epoch": 20,
                "revoked": False,
            }
        ],
    }
    registry["registry_hash"] = confidential_measurement_registry_hash(registry)
    return registry


@pytest.mark.parametrize("field", ("valid_from_epoch", "valid_until_epoch"))
def test_confidential_measurement_registry_hash_rejects_bool_epoch_fields(field: str) -> None:
    registry = _measurement_registry()
    registry["entries"][0][field] = True

    with pytest.raises(ValueError, match=f"{field} must be an int"):
        confidential_measurement_registry_hash(registry)
