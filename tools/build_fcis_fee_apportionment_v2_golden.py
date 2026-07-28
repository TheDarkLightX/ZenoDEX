#!/usr/bin/env python3
"""Build or check the shared Python/Rust SRGD-v1 golden-vector corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from src.core.fcis_fee_apportionment_allocator import (  # noqa: E402
    apply_fee_apportionment_v2,
)
from src.core.fcis_fee_apportionment_codec import (  # noqa: E402
    canonical_sha256_fcis_fee_apportionment_v2,
    encode_fcis_fee_apportionment_v2,
)
from src.core.fcis_fee_apportionment_values import (  # noqa: E402
    ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2,
    COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
    FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
    FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2,
    MAX_FEE_AMOUNT_V2,
    SRGD_ALGORITHM_VERSION_V1,
    CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2,
    FeeApportionmentKeyV2,
    FeeApportionmentTransitionOkV2,
    FeeApportionmentTransitionRejectV2,
    FeeDeficitEntryV2,
    FeeDistributionPolicyV2,
)

OUTPUT = REPO / "tests" / "fixtures" / "fcis_fee_apportionment_v2_golden.json"
CONTRACT = REPO / "docs" / "research" / "FCIS_M5_P4B5A_SRGD_V1_IMPLEMENTATION_CONTRACT_20260728.md"
ARCHITECTURE_HEAD = "371912c5cb25533a1b4e3523c478563991db25b0"
SOURCE_PATHS = (
    "src/core/fcis_fee_apportionment_values.py",
    "src/core/fcis_fee_apportionment_schema.py",
    "src/core/fcis_fee_apportionment_codec.py",
    "src/core/fcis_fee_apportionment_admission.py",
    "src/core/fcis_fee_apportionment_allocator.py",
)


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _exact_fixture_int(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")
    return value


def _exact_fixture_text(name: str, value: object) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be an exact string")
    return value


def _key(raw: dict[str, object]) -> FeeApportionmentKeyV2:
    return FeeApportionmentKeyV2(
        _exact_fixture_text(
            "fee_distribution_domain_id",
            raw["fee_distribution_domain_id"],
        ),
        _exact_fixture_text("asset", raw["asset"]),
    )


def _state(raw: dict[str, object]) -> CommittedFeeApportionmentStateV2:
    entries_raw = raw["entries"]
    if type(entries_raw) is not list:
        raise TypeError("fixture state entries must be a list")
    entries = tuple(
        FeeDeficitEntryV2(
            _key(entry["key"]),
            _exact_fixture_int("deficit_buyback", entry["deficit_buyback"]),
            _exact_fixture_int("deficit_treasury", entry["deficit_treasury"]),
        )
        for entry in entries_raw
    )
    return CommittedFeeApportionmentStateV2(
        _exact_fixture_text("algorithm_version", raw["algorithm_version"]),
        entries,
    )


def _policy(raw: dict[str, object]) -> FeeDistributionPolicyV2:
    return FeeDistributionPolicyV2(
        _exact_fixture_int("buyback_bps", raw["buyback_bps"]),
        _exact_fixture_int("treasury_bps", raw["treasury_bps"]),
        _exact_fixture_int("rewards_bps", raw["rewards_bps"]),
        _exact_fixture_text("buyback_destination", raw["buyback_destination"]),
        _exact_fixture_text("treasury_destination", raw["treasury_destination"]),
        _exact_fixture_text("rewards_destination", raw["rewards_destination"]),
    )


def _case(
    case_id: str,
    *,
    contributions: list[tuple[str, str, int]],
    weights: tuple[int, int, int] = (3_333, 3_333, 3_334),
    destinations: tuple[str, str, str] = ("buyback", "treasury", "rewards"),
    state_entries: list[tuple[str, str, int, int]] | None = None,
) -> dict[str, object]:
    return {
        "id": case_id,
        "input": {
            "contributions": [
                {
                    "key": {
                        "fee_distribution_domain_id": domain,
                        "asset": asset,
                    },
                    "amount": amount,
                }
                for domain, asset, amount in contributions
            ],
            "policy": {
                "buyback_bps": weights[0],
                "treasury_bps": weights[1],
                "rewards_bps": weights[2],
                "buyback_destination": destinations[0],
                "treasury_destination": destinations[1],
                "rewards_destination": destinations[2],
            },
            "state": {
                "algorithm_version": SRGD_ALGORITHM_VERSION_V1,
                "entries": [
                    {
                        "key": {
                            "fee_distribution_domain_id": domain,
                            "asset": asset,
                        },
                        "deficit_buyback": buyback,
                        "deficit_treasury": treasury,
                    }
                    for domain, asset, buyback, treasury in (state_entries or [])
                ],
            },
        },
    }


def _source_cases() -> list[dict[str, object]]:
    return [
        _case("zero", contributions=[("domain-a", "asset-a", 0)]),
        _case("one_atom", contributions=[("domain-a", "asset-a", 1)]),
        _case(
            "fixed_tie",
            contributions=[("domain-a", "asset-a", 1)],
            weights=(5_000, 5_000, 0),
        ),
        _case(
            "positive_support",
            contributions=[("domain-a", "asset-a", 2)],
            weights=(5_000, 2_500, 2_500),
        ),
        _case(
            "score_includes_fraction",
            contributions=[("domain-a", "asset-a", 1)],
            weights=(0, 3_333, 6_667),
            state_entries=[("domain-a", "asset-a", -6_666, 3_333)],
        ),
        _case(
            "two_bonuses",
            contributions=[("domain-a", "asset-a", 2)],
        ),
        _case(
            "denominator_minus_one",
            contributions=[("domain-a", "asset-a", 9_999)],
        ),
        _case(
            "denominator",
            contributions=[("domain-a", "asset-a", 10_000)],
            state_entries=[("domain-a", "asset-a", 3_333, 3_333)],
        ),
        _case(
            "denominator_plus_one",
            contributions=[("domain-a", "asset-a", 10_001)],
        ),
        _case(
            "u256_maximum",
            contributions=[("domain-a", "asset-a", MAX_FEE_AMOUNT_V2)],
            weights=(10_000, 0, 0),
        ),
        _case(
            "grouped_and_protocol_ordered",
            contributions=[
                ("domain-a", "asset-c", 3),
                ("domain-a", "asset-a", 1),
                ("domain-a", "asset-a", 2),
            ],
            destinations=("same", "same", "same"),
        ),
        _case(
            "aggregate_overflow",
            contributions=[
                ("domain-a", "asset-a", MAX_FEE_AMOUNT_V2),
                ("domain-a", "asset-a", 1),
            ],
        ),
    ]


def _evaluate_case(case: dict[str, object]) -> dict[str, object]:
    raw_input = case["input"]
    if type(raw_input) is not dict:
        raise TypeError("fixture input must be an object")
    contributions_raw = raw_input["contributions"]
    policy_raw = raw_input["policy"]
    state_raw = raw_input["state"]
    if (
        type(contributions_raw) is not list
        or type(policy_raw) is not dict
        or type(state_raw) is not dict
    ):
        raise TypeError("fixture input shape drift")
    contributions = tuple(
        FeeAmountCandidateV2(_key(item["key"]), int(item["amount"])) for item in contributions_raw
    )
    result = apply_fee_apportionment_v2(
        contributions=contributions,
        policy=_policy(policy_raw),
        state=_state(state_raw),
    )
    if type(result) is FeeApportionmentTransitionRejectV2:
        return {
            "accept": False,
            "code": result.code.value,
            "path": list(result.path),
        }
    if type(result) is not FeeApportionmentTransitionOkV2:
        raise AssertionError("unexpected fee-apportionment result")
    state_bytes = encode_fcis_fee_apportionment_v2(
        COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
        result.state,
    )
    allocations_bytes = encode_fcis_fee_apportionment_v2(
        ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2,
        result.allocations,
    )
    result_bytes = encode_fcis_fee_apportionment_v2(
        FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2,
        result,
    )
    return {
        "accept": True,
        "state": json.loads(state_bytes)["value"],
        "allocations": json.loads(allocations_bytes)["value"],
        "canonical": {
            "state_utf8": state_bytes.decode("utf-8"),
            "state_sha256": canonical_sha256_fcis_fee_apportionment_v2(
                COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
                result.state,
            ),
            "allocations_utf8": allocations_bytes.decode("utf-8"),
            "allocations_sha256": canonical_sha256_fcis_fee_apportionment_v2(
                ASSET_FEE_ALLOCATION_BATCH_SCHEMA_ID_V2,
                result.allocations,
            ),
            "result_utf8": result_bytes.decode("utf-8"),
            "result_sha256": canonical_sha256_fcis_fee_apportionment_v2(
                FEE_APPORTIONMENT_TRANSITION_RESULT_SCHEMA_ID_V2,
                result,
            ),
        },
    }


def _document() -> dict[str, object]:
    cases = _source_cases()
    for case in cases:
        case["expected"] = _evaluate_case(case)
    return {
        "version": 2,
        "kernel": "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1",
        "schema_revision": FEE_APPORTIONMENT_SCHEMA_REVISION_V2,
        "architecture_head": ARCHITECTURE_HEAD,
        "implementation_contract_sha256": _sha256(CONTRACT.read_bytes()),
        "generator_sha256": _sha256(Path(__file__).read_bytes()),
        "python_source_sha256": {
            path: _sha256((REPO / path).read_bytes()) for path in SOURCE_PATHS
        },
        "oracle_scope": (
            "Python whole-result bytes for cross-language refinement; "
            "the independent eight-bonus oracle is a separate test."
        ),
        "cases": cases,
    }


def _render() -> bytes:
    return (
        json.dumps(
            _document(),
            sort_keys=True,
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = _render()
    if args.check:
        if not args.output.exists() or args.output.read_bytes() != rendered:
            print(f"stale fee-apportionment fixture: {args.output}")
            return 1
        print(f"fee-apportionment fixture current: {args.output}")
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(rendered)
    print(f"wrote {args.output} ({len(_source_cases())} cases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
