"""Closed-shape and source-binding checks for the accounting source classification contract.

The contract is research text; this gate keeps it honest: its alias table must name
real V1 wire fields, its precedence must equal the closed guard enum order, its
normative partition must appear verbatim in the pinned safety claim, and it must
grant no authority.
"""

from __future__ import annotations

import dataclasses
import hashlib
import json
from pathlib import Path
from typing import Any

from src.core.global_economic_state_effect_refinement_v1 import (
    CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1,
    CLAIMANT_BACKING_VIEW_SCHEMA_V1,
    ClaimantBackingRejectCodeV1,
)
from src.core.global_settlement_types_v1 import EconomicAmountV1, GlobalEconomicStateV1

ROOT = Path(__file__).resolve().parents[1]
CONTRACT = ROOT / "docs/research/ZENODEX_ACCOUNTING_SOURCE_CLASSIFICATION_CONTRACT_V1.json"
COMPANION = ROOT / "docs/research/ZENODEX_ACCOUNTING_SOURCE_CLASSIFICATION_CONTRACT_V1.md"
EXPECTED_KEYS = {
    "schema",
    "created_date",
    "authority",
    "status",
    "normative_source",
    "normative_partition",
    "key_control_statement",
    "vocabulary",
    "v1_alias_table",
    "disjoint_partitions",
    "conservation",
    "source_classes",
    "exact_one_classification",
    "reserve_interpretation",
    "arithmetic",
    "claimant_backing_guard",
    "blocked_pending_policy",
    "nonclaims",
}


def _contract() -> dict[str, Any]:
    value = json.loads(CONTRACT.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_contract_has_the_closed_shape_and_no_authority() -> None:
    contract = _contract()
    assert set(contract) == EXPECTED_KEYS
    assert contract["schema"] == "zenodex/accounting-source-classification-contract/v1"
    assert contract["authority"] == "NONE"
    assert contract["reserve_interpretation"] == "NAMED_UNENCUMBERED_NO_CLAIMANT"
    assert contract["disjoint_partitions"] == ["balances", "custody", "reserves"]
    assert any("authority is granted" in item for item in contract["nonclaims"])
    assert COMPANION.is_file()


def test_normative_partition_is_pinned_to_the_safety_claim() -> None:
    contract = _contract()
    source = ROOT / contract["normative_source"]["path"]
    raw = source.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == contract["normative_source"]["sha256"]
    folded = " ".join(raw.decode("utf-8").split())
    assert " ".join(contract["normative_partition"].split()) in folded
    assert contract["key_control_statement"].split(";")[0] in folded


def test_alias_table_names_real_v1_wire_fields() -> None:
    contract = _contract()
    fields = {
        "EconomicAmountV1": {field.name for field in dataclasses.fields(EconomicAmountV1)},
        "GlobalEconomicStateV1": {field.name for field in dataclasses.fields(GlobalEconomicStateV1)},
    }
    for row in contract["v1_alias_table"]:
        assert row["byte_stable"] is True
        assert row["wire_field"] in fields[row["wire_type"]], row
    aliased = {row["wire_field"] for row in contract["v1_alias_table"]}
    assert {"custody_domain", "custody", "liabilities", "reserves", "balances"} <= aliased


def test_guard_binding_matches_the_closed_enum_and_constants() -> None:
    guard = _contract()["claimant_backing_guard"]
    assert guard["reject_precedence"] == [code.value for code in ClaimantBackingRejectCodeV1]
    assert guard["view_schema"] == CLAIMANT_BACKING_VIEW_SCHEMA_V1
    assert guard["view_hash_domain"] == CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1
    for key in ("python", "rust", "golden_vector", "renderer"):
        assert (ROOT / guard[key]).is_file(), guard[key]


def test_source_classes_are_closed_and_policy_gated() -> None:
    contract = _contract()
    classes = [row["class"] for row in contract["source_classes"]]
    assert classes == [
        "CLAIMANT_ENTITLEMENT",
        "UNENCUMBERED_CONTROLLED_LOCATION",
        "UNENCUMBERED_RESERVE",
        "PENDING_EXTERNAL_OBLIGATION",
        "TERMINAL_OBLIGATION",
    ]
    for row in contract["source_classes"]:
        assert {"asset", "u128_width", "canonical_order"} <= set(row["required_bindings"]), row
    assert all(key.startswith("UP-") for key in contract["blocked_pending_policy"])
    assert contract["arithmetic"] == {
        "width": "u128",
        "overflow": "REJECT",
        "rounding": "NONE",
        "residue": "carried explicitly as a named reserve row",
    }
