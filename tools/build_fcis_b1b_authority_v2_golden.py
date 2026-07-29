#!/usr/bin/env python3
"""Build/check the shared Python/Rust FCIS B1B-1 carrier fixture."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from src.core.fcis_b1b_authority_codec import (
    canonical_bootstrap_anchor_claim_root_v2,
    canonical_v1_to_v2_migration_manifest_root_v2,
    encode_fcis_b1b_authority_v2,
)
from src.core.fcis_b1b_authority_values import (
    DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2,
    FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2,
    FCIS_B1B_AUTHORITY_SCHEMA_REVISION_V2,
    MAX_B1B_TEXT_CHARACTERS_V2,
    MAX_U256_V2,
    V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
    DeploymentBootstrapAnchorClaimV2,
    FCISAuthorityHeaderV2,
    V1ToV2MigrationManifestV2,
)

REPO = Path(__file__).resolve().parents[1]
FIXTURE = REPO / "tests" / "fixtures" / "fcis_b1b_authority_v2_golden.json"
ZERO = "0x" + ("0" * 64)
ONE = "0x" + ("0" * 63) + "1"
TWO = "0x" + ("0" * 63) + "2"


def _entry(schema_id: str, value: object, *, root: str | None = None) -> dict[str, object]:
    encoded = encode_fcis_b1b_authority_v2(schema_id, value)
    result: dict[str, object] = {
        "schema_id": schema_id,
        "canonical_utf8": encoded.decode("utf-8"),
        "value": json.loads(encoded)["value"],
    }
    if root is not None:
        result["root"] = root
    return result


def build() -> dict[str, object]:
    header = FCISAuthorityHeaderV2("zenodex:testnet:α", 0, ONE)
    maximum_header = FCISAuthorityHeaderV2("zenodex:testnet:α", MAX_U256_V2, ONE)
    anchor = DeploymentBootstrapAnchorClaimV2("zenodex:testnet:α", TWO)
    manifest = V1ToV2MigrationManifestV2(
        "zenodex:testnet:α",
        ZERO,
        "protocol-fees:α",
        ONE,
        0,
        1,
        0,
        4,
        5,
    )
    structurally_exact_wrong_constants = V1ToV2MigrationManifestV2(
        "zenodex:testnet:α",
        ZERO,
        "protocol-fees:α",
        ONE,
        9,
        7,
        4,
        3,
        6,
    )
    return {
        "version": 2,
        "schema_revision": FCIS_B1B_AUTHORITY_SCHEMA_REVISION_V2,
        "u256_boundaries": [
            0,
            1,
            MAX_U256_V2 - 1,
            MAX_U256_V2,
        ],
        "negative_cases": [
            {
                "id": "identifier_empty",
                "kind": "identifier",
                "value": "",
                "languages": ["python", "rust"],
                "expected_code": "invalid_value",
            },
            {
                "id": "identifier_character_and_utf8_overflow",
                "kind": "identifier",
                "value": "🧪" * (MAX_B1B_TEXT_CHARACTERS_V2 + 1),
                "languages": ["python", "rust"],
                "expected_code": "invalid_value",
            },
            {
                "id": "digest_uppercase",
                "kind": "digest",
                "value": "0x" + ("A" * 64),
                "languages": ["python", "rust"],
                "expected_code": "invalid_value",
            },
            {
                "id": "digest_malformed_length",
                "kind": "digest",
                "value": "0x0",
                "languages": ["python", "rust"],
                "expected_code": "invalid_value",
            },
            {
                "id": "u256_boolean_alias",
                "kind": "u256",
                "value": True,
                "languages": ["python"],
                "rust_exclusion": "BigUint has no Boolean inhabitant",
                "expected_code": "invalid_value",
            },
            {
                "id": "u256_negative",
                "kind": "u256",
                "value": -1,
                "languages": ["python"],
                "rust_exclusion": "BigUint has no negative inhabitant",
                "expected_code": "invalid_value",
            },
            {
                "id": "u256_overflow",
                "kind": "u256",
                "value": MAX_U256_V2 + 1,
                "languages": ["python", "rust"],
                "expected_code": "invalid_value",
            },
            {
                "id": "positive_u256_zero",
                "kind": "positive_u256",
                "value": 0,
                "languages": ["python", "rust"],
                "expected_code": "invalid_value",
            },
        ],
        "cases": [
            {
                "id": "authority_header_initial",
                **_entry(FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2, header),
            },
            {
                "id": "authority_header_u256_maximum",
                **_entry(FCIS_AUTHORITY_HEADER_SCHEMA_ID_V2, maximum_header),
            },
            {
                "id": "bootstrap_anchor_claim",
                **_entry(
                    DEPLOYMENT_BOOTSTRAP_ANCHOR_CLAIM_SCHEMA_ID_V2,
                    anchor,
                    root=canonical_bootstrap_anchor_claim_root_v2(anchor),
                ),
            },
            {
                "id": "v1_to_v2_migration_manifest",
                **_entry(
                    V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
                    manifest,
                    root=canonical_v1_to_v2_migration_manifest_root_v2(manifest),
                ),
            },
            {
                "id": "structurally_exact_wrong_fixed_constants",
                "semantic_status": "carrier_only_not_migration_authority",
                **_entry(
                    V1_TO_V2_MIGRATION_MANIFEST_SCHEMA_ID_V2,
                    structurally_exact_wrong_constants,
                    root=canonical_v1_to_v2_migration_manifest_root_v2(
                        structurally_exact_wrong_constants
                    ),
                ),
            },
        ],
    }


def _serialized() -> str:
    return json.dumps(build(), sort_keys=True, indent=2, ensure_ascii=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = _serialized()
    if args.check:
        if not FIXTURE.exists() or FIXTURE.read_text(encoding="utf-8") != expected:
            print(f"stale fixture: {FIXTURE}")
            return 1
        return 0
    FIXTURE.write_text(expected, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
