"""Fail-closed teeth for the WS2 client trust-root loaders.

A malformed trust root must abort loading (ClientPinsetError), never degrade to
permissive — the WS5-A browser-pinset lesson, enforced here for the Python side.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Callable

import pytest

from src.integration.client_pinned_registry import (
    DEFAULT_CONTRACT_PATH,
    ClientPinsetError,
    load_consensus_contract,
    load_pinned_registry,
)

PERPS_PT = "risc0.zenodex_perps_np_transition.v1"


def test_real_contract_loads_with_independent_proof_type_lookup() -> None:
    contract = load_consensus_contract(DEFAULT_CONTRACT_PATH)
    assert contract.required_level("perps_np", "deposit_collateral") == (
        "live_replay_authority_equivalent"
    )
    # The independent gate-10 lookup is live: proof_type -> level via the contract.
    assert contract.level_of_proof_type(PERPS_PT) == "live_replay_authority_equivalent"
    assert contract.admission_binding_status("perps_np", "deposit_collateral") == (
        "bound_to_replay_guard"
    )
    assert contract.rank("live_equivalent") is not None
    assert contract.rank("nonsense_level") is None


def _pin_row(**overrides: Any) -> dict[str, Any]:
    row: dict[str, Any] = {
        "surface": "perps_np",
        "operation": "deposit_collateral",
        "proof_type": PERPS_PT,
        "chain_id": "devnet",
        "risc0_image_id_words": [1, 2, 3, 4, 5, 6, 7, 8],
        "blessed_verifier": {"binary_path": "/usr/bin/r0vm", "sha256": "ab" * 32},
        "required_journal_fields": ["collateral_binding_hash", "oracle_binding_hash"],
        "expected_static": {},
        "recomputed_fields": ["collateral_binding_hash", "oracle_binding_hash"],
        "cross_field_equal": [],
        "head_equal_fields": [],
        "claim_level": "live_replay_authority_equivalent",
        "ceiling_level": "live_replay_authority_equivalent",
        "admission_threshold_level": "live_replay_authority_equivalent",
        "admission_proof_gated_statuses": [],
    }
    row.update(overrides)
    return row


def _write_pinset(tmp_path: Path, row: dict[str, Any], *, schema: str = "zenodex/client-pinset/v1") -> Path:
    path = tmp_path / "pinset.json"
    path.write_text(json.dumps({"schema": schema, "pins": [row]}))
    return path


def test_valid_pinset_loads(tmp_path: Path) -> None:
    registry = load_pinned_registry(_write_pinset(tmp_path, _pin_row()))
    pins = registry.get("perps_np", "deposit_collateral")
    assert pins is not None
    assert pins.pinned_image_id == (1, 2, 3, 4, 5, 6, 7, 8)
    assert pins.blessed_verifier.allow_path_lookup is False
    assert pins.admission_proof_gated_statuses == ()


@pytest.mark.parametrize(
    "mutate",
    [
        lambda r: r.update(risc0_image_id_words=[1, 2, 3]),
        lambda r: r.update(risc0_image_id_words=[True, 2, 3, 4, 5, 6, 7, 8]),
        lambda r: r.update(risc0_image_id_words=[-1, 2, 3, 4, 5, 6, 7, 8]),
        lambda r: r.update(blessed_verifier={"binary_path": "r0vm", "sha256": "ab" * 32}),
        lambda r: r.update(blessed_verifier={"binary_path": "/usr/bin/r0vm", "sha256": "xyz"}),
        lambda r: r.update(
            blessed_verifier={"binary_path": "/usr/bin/r0vm", "sha256": "ab" * 32, "extra": 1}
        ),
        lambda r: r.update(required_journal_fields=[]),
        lambda r: r.update(required_journal_fields=["a", "a"]),
        lambda r: r.update(expected_static={"field": "zz" * 32}),
        lambda r: r.update(expected_static={"field": 123}),
        lambda r: r.update(cross_field_equal=[["only-one"]]),
        lambda r: r.update(claim_level=""),
        lambda r: r.update(admission_proof_gated_statuses=[""]),
        lambda r: r.update(unknown_key=1),
        lambda r: r.pop("chain_id"),
    ],
)
def test_malformed_pin_rows_fail_closed(tmp_path: Path, mutate: Callable[[dict[str, Any]], Any]) -> None:
    row = _pin_row()
    mutate(row)
    with pytest.raises(ClientPinsetError):
        load_pinned_registry(_write_pinset(tmp_path, row))


def test_wrong_schema_fails_closed(tmp_path: Path) -> None:
    with pytest.raises(ClientPinsetError):
        load_pinned_registry(_write_pinset(tmp_path, _pin_row(), schema="zenodex/other/v1"))


def test_duplicate_pin_fails_closed(tmp_path: Path) -> None:
    path = tmp_path / "pinset.json"
    path.write_text(
        json.dumps({"schema": "zenodex/client-pinset/v1", "pins": [_pin_row(), _pin_row()]})
    )
    with pytest.raises(ClientPinsetError):
        load_pinned_registry(path)


def test_empty_pinset_fails_closed(tmp_path: Path) -> None:
    path = tmp_path / "pinset.json"
    path.write_text(json.dumps({"schema": "zenodex/client-pinset/v1", "pins": []}))
    with pytest.raises(ClientPinsetError):
        load_pinned_registry(path)


def test_contract_with_conflicting_proof_type_levels_fails_closed(tmp_path: Path) -> None:
    contract = {
        "claim_levels": {"core_equivalent": "x", "live_equivalent": "y"},
        "operations": {
            "a.op1": {"guest": {"proof_type": "pt.v1", "live_equivalence_claim_level": "core_equivalent"}},
            "a.op2": {"guest": {"proof_type": "pt.v1", "live_equivalence_claim_level": "live_equivalent"}},
        },
    }
    path = tmp_path / "contract.json"
    path.write_text(json.dumps(contract))
    with pytest.raises(ClientPinsetError):
        load_consensus_contract(path)
