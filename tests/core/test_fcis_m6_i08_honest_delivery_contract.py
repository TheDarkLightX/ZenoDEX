"""I08 honest delivery contract checker and claim-boundary tests."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

import pytest

from tools.check_fcis_m6_i08_honest_contract import check_contract

_CONTRACT = (
    Path(__file__).resolve().parents[2]
    / "docs/research/m6_tasks/TASK_I08_HONEST_DELIVERY_CONTRACT_V1.json"
)


def _payload() -> dict[str, Any]:
    return cast(dict[str, Any], json.loads(_CONTRACT.read_text(encoding="utf-8")))


def _assert_rejected(payload: dict[str, Any], tmp_path: Path, message: str) -> None:
    mutated = tmp_path / "mutated-i08.json"
    mutated.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(ValueError, match=message):
        check_contract(mutated)


def test_i08_honest_contract_is_complete() -> None:
    check_contract(_CONTRACT)


def test_i08_rejects_exactly_once_claim_in_supported_phrase(tmp_path: Path) -> None:
    payload = _payload()
    claims = cast(list[dict[str, Any]], payload["claims"])
    claims[1]["phrase"] = "network-level exactly-once delivery"

    _assert_rejected(payload, tmp_path, "unsupported wording for AT_LEAST_ONCE_ATTEMPTS")


def test_i08_rejects_exactly_once_api_name(tmp_path: Path) -> None:
    payload = _payload()
    api_names = cast(dict[str, Any], payload["api_names"])
    api_names["attempt"] = "exactly_once_delivery"

    _assert_rejected(payload, tmp_path, "unsupported API name for attempt")


def test_i08_rejects_missing_claim_documentation(tmp_path: Path) -> None:
    payload = _payload()
    contract = tmp_path / "contract.json"
    docs = tmp_path / "TASK_I08_HONEST_DELIVERY_CONTRACT_V1.md"
    source_docs = _CONTRACT.parent / cast(str, payload["documentation_file"])
    docs.write_text(
        source_docs.read_text(encoding="utf-8").replace("- Claim: atomic enqueue\n", ""),
        encoding="utf-8",
    )
    payload["documentation_file"] = docs.name
    contract.write_text(json.dumps(payload), encoding="utf-8")

    with pytest.raises(ValueError, match="exactly four Claim lines"):
        check_contract(contract)


def test_i08_rejects_missing_exactly_once_nonclaim(tmp_path: Path) -> None:
    payload = _payload()
    nonclaims = cast(list[str], payload["nonclaims"])
    nonclaims.remove("network-level exactly-once delivery")

    _assert_rejected(payload, tmp_path, "omits required nonclaim")
