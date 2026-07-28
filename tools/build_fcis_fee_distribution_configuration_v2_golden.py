#!/usr/bin/env python3
"""Build/check shared Python/Rust fee-configuration golden vectors."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from src.core.fcis_fee_apportionment_codec import (  # noqa: E402
    encode_fcis_fee_apportionment_v2,
)
from src.core.fcis_fee_apportionment_values import (  # noqa: E402
    FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
    MAX_FEE_AMOUNT_V2,
    SRGD_ALGORITHM_VERSION_V1,
    FeeDistributionPolicyV2,
)
from src.core.fcis_fee_distribution_configuration_codec import (  # noqa: E402
    canonical_fee_distribution_configuration_root_v2,
    canonical_fee_distribution_policy_root_v2,
    encode_fee_distribution_configuration_v2,
)
from src.core.fcis_fee_distribution_configuration_values import (  # noqa: E402
    FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
    FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2,
    PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2,
    VALIDATED_FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
    FeeDistributionConfigurationBodyV2,
    FeeDistributionConfigurationClaimV2,
    FeeDistributionConfigurationVerificationRejectV2,
    ValidatedFeeDistributionConfigurationClaimV2,
)
from src.core.fcis_fee_distribution_configuration_verification import (  # noqa: E402
    validate_fee_distribution_configuration_claim_v2,
)

OUTPUT = REPO / "tests" / "fixtures" / "fcis_fee_distribution_configuration_v2_golden.json"
CONTRACT = (
    REPO / "docs" / "research" / "FCIS_M5_P4B5A_CONFIGURATION_CLAIM_VALIDATION_CONTRACT_20260728.md"
)
BASE_HEAD = "d434d29673692ef78f2db5f7a7cfae7a737fb2d6"
ZERO_DIGEST = "0x" + ("0" * 64)
SOURCE_PATHS = (
    "src/core/fcis_fee_distribution_configuration_values.py",
    "src/core/fcis_fee_distribution_configuration_schema.py",
    "src/core/fcis_fee_distribution_configuration_codec.py",
    "src/core/fcis_fee_distribution_configuration_admission.py",
    "src/core/fcis_fee_distribution_configuration_verification.py",
)
RUST_SOURCE_PATH = (
    "rust-runtime/crates/zenodex-runtime-core/src/fcis_fee_distribution_configuration.rs"
)


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _policy(*, attacker: bool = False) -> FeeDistributionPolicyV2:
    if attacker:
        return FeeDistributionPolicyV2(
            10_000,
            0,
            0,
            "mallory",
            "unused-treasury",
            "unused-rewards",
        )
    return FeeDistributionPolicyV2(
        3_333,
        3_333,
        3_334,
        "buyback:α",
        "treasury",
        "rewards",
    )


def _claim(
    case_id: str,
) -> FeeDistributionConfigurationClaimV2:
    attacker = case_id == "self_consistent_attacker_configuration"
    policy = _policy(attacker=attacker)
    policy_root = canonical_fee_distribution_policy_root_v2(policy)
    algorithm = SRGD_ALGORITHM_VERSION_V1
    accepted_language = PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2
    activation_sequence = MAX_FEE_AMOUNT_V2
    if case_id == "algorithm_substitution":
        algorithm = "OTHER_ALGORITHM"
    elif case_id == "accepted_language_substitution":
        accepted_language = "OTHER_LANGUAGE"
    elif case_id == "policy_root_substitution":
        policy_root = ZERO_DIGEST
    elif case_id == "zero_activation":
        activation_sequence = 0
    body = FeeDistributionConfigurationBodyV2(
        "attacker:deployment" if attacker else "zenodex:testnet:α",
        7,
        "attacker-domain" if attacker else "protocol-fees",
        policy_root,
        policy,
        activation_sequence,
        algorithm,
        accepted_language,
    )
    configuration_root = canonical_fee_distribution_configuration_root_v2(body)
    if case_id == "configuration_root_substitution":
        configuration_root = ZERO_DIGEST
    return FeeDistributionConfigurationClaimV2(
        body,
        configuration_root,
    )


def _policy_projection(policy: FeeDistributionPolicyV2) -> dict[str, object]:
    return {
        "buyback_bps": policy.buyback_bps,
        "treasury_bps": policy.treasury_bps,
        "rewards_bps": policy.rewards_bps,
        "buyback_destination": policy.buyback_destination,
        "treasury_destination": policy.treasury_destination,
        "rewards_destination": policy.rewards_destination,
    }


def _body_projection(body: FeeDistributionConfigurationBodyV2) -> dict[str, object]:
    return {
        "chain_deployment_id": body.chain_deployment_id,
        "configuration_version": body.configuration_version,
        "fee_distribution_domain_id": body.fee_distribution_domain_id,
        "policy_root": body.policy_root,
        "policy": _policy_projection(body.policy),
        "activation_sequence": body.activation_sequence,
        "algorithm_version": body.algorithm_version,
        "accepted_language_version": body.accepted_language_version,
    }


def _input_projection(
    claim: FeeDistributionConfigurationClaimV2,
) -> dict[str, object]:
    return {
        "body": _body_projection(claim.body),
        "configuration_root": claim.configuration_root,
    }


def _evaluate(case_id: str) -> dict[str, object]:
    claim = _claim(case_id)
    result = validate_fee_distribution_configuration_claim_v2(claim)
    if type(result) is FeeDistributionConfigurationVerificationRejectV2:
        return {
            "input": _input_projection(claim),
            "expected": {
                "accept": False,
                "code": result.code.value,
                "path": list(result.path),
            },
        }
    if type(result) is not ValidatedFeeDistributionConfigurationClaimV2:
        raise AssertionError("unexpected fee configuration result")
    policy_bytes = encode_fcis_fee_apportionment_v2(
        FEE_DISTRIBUTION_POLICY_SCHEMA_ID_V2,
        result.body.policy,
    )
    body_bytes = encode_fee_distribution_configuration_v2(
        FEE_DISTRIBUTION_CONFIGURATION_BODY_SCHEMA_ID_V2,
        result.body,
    )
    claim_bytes = encode_fee_distribution_configuration_v2(
        FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
        claim,
    )
    validated_bytes = encode_fee_distribution_configuration_v2(
        VALIDATED_FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
        result,
    )
    return {
        "input": _input_projection(claim),
        "expected": {
            "accept": True,
            "policy_utf8": policy_bytes.decode("utf-8"),
            "policy_root": canonical_fee_distribution_policy_root_v2(result.body.policy),
            "body_utf8": body_bytes.decode("utf-8"),
            "configuration_root": canonical_fee_distribution_configuration_root_v2(result.body),
            "claim_utf8": claim_bytes.decode("utf-8"),
            "validated_claim_utf8": validated_bytes.decode("utf-8"),
        },
    }


def _document() -> dict[str, object]:
    case_ids = (
        "valid_u256_maximum",
        "zero_activation",
        "self_consistent_attacker_configuration",
        "algorithm_substitution",
        "accepted_language_substitution",
        "policy_root_substitution",
        "configuration_root_substitution",
    )
    return {
        "version": 2,
        "schema_revision": FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2,
        "base_head": BASE_HEAD,
        "implementation_contract_sha256": _sha256(CONTRACT.read_bytes()),
        "generator_sha256": _sha256(Path(__file__).read_bytes()),
        "python_source_sha256": {
            path: _sha256((REPO / path).read_bytes()) for path in SOURCE_PATHS
        },
        "rust_source_sha256": {RUST_SOURCE_PATH: _sha256((REPO / RUST_SOURCE_PATH).read_bytes())},
        "cases": [{"id": case_id, **_evaluate(case_id)} for case_id in case_ids],
    }


def _render() -> bytes:
    return (json.dumps(_document(), sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = _render()
    if args.check:
        if not args.output.exists() or args.output.read_bytes() != rendered:
            print(f"stale fee-configuration fixture: {args.output}")
            return 1
        print(f"fee-configuration fixture current: {args.output}")
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(rendered)
    print(f"wrote {args.output} (7 cases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
