from __future__ import annotations

from copy import deepcopy

import pytest

from src.core import oracle_current_dispute_status_v1 as status_core
from src.core.oracle_current_dispute_status_v1 import (
    GLOBAL_CURRENT_DISPUTE_STATUS_ORACLE_ID_V1,
    _status_root,
    build_oracle_current_dispute_status_v1,
    current_dispute_status_root_from_global_root_v1,
    global_root_from_current_dispute_status_root_v1,
    verify_oracle_current_dispute_status_v1,
)

REPORT_IDS = (
    "sha256:" + "11" * 32,
    "sha256:" + "22" * 32,
    "sha256:" + "33" * 32,
)


def _entry(*, status: str, report_id: str = REPORT_IDS[0]) -> dict[str, object]:
    return {
        "dispute_id": "sha256:" + "44" * 32,
        "report_id": report_id,
        "status": status,
    }


def _verify(witness: dict[str, object], *, now_epoch: int = 7):
    return verify_oracle_current_dispute_status_v1(
        witness,
        expected_report_ids=REPORT_IDS,
        expected_root=str(witness["current_dispute_status_root"]),
        now_epoch=now_epoch,
    )


def test_clean_current_status_accepts_at_exact_runtime_epoch() -> None:
    # Given a root-selected snapshot for the complete report scope.
    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(),
        as_of_epoch=7,
    )

    # When the critical consumer verifies it at the same epoch.
    result = _verify(witness)

    # Then the absence of an active dispute is accepted.
    assert result.ok is True
    assert result.errors == ()
    assert result.disputed_report_ids == ()


def test_clean_status_has_stable_independent_root_vector() -> None:
    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(),
        as_of_epoch=7,
    )

    assert witness["current_dispute_status_root"] == (
        "sha256:22daec7d7fce0963414c8737e4046476de0527cdd7a9e25fe5af051b84d5d0f2"
    )


def test_current_status_root_has_exact_global_abi_representation() -> None:
    status_root = (
        "sha256:22daec7d7fce0963414c8737e4046476de0527cdd7a9e25fe5af051b84d5d0f2"
    )

    global_root = global_root_from_current_dispute_status_root_v1(status_root)

    assert GLOBAL_CURRENT_DISPUTE_STATUS_ORACLE_ID_V1 == (
        "zenodex.oracle.current-dispute-status.v1"
    )
    assert global_root == (
        "0x22daec7d7fce0963414c8737e4046476de0527cdd7a9e25fe5af051b84d5d0f2"
    )
    assert current_dispute_status_root_from_global_root_v1(global_root) == status_root


@pytest.mark.parametrize(
    "invalid_root",
    [
        "0x" + "11" * 32,
        "sha256:" + "AA" * 32,
        "sha256:" + "00" * 32,
        object(),
    ],
)
def test_invalid_status_root_cannot_cross_global_abi_boundary(invalid_root: object) -> None:
    with pytest.raises((TypeError, ValueError)):
        global_root_from_current_dispute_status_root_v1(invalid_root)


@pytest.mark.parametrize("status", ["open", "upheld"])
def test_active_dispute_status_rejects_critical_consumption(status: str) -> None:
    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(_entry(status=status),),
        as_of_epoch=7,
    )

    result = _verify(witness)

    assert result.ok is False
    assert result.disputed_report_ids == (REPORT_IDS[0],)
    assert result.errors == ("current dispute status includes open or upheld reports",)


def test_rejected_dispute_does_not_revoke_report() -> None:
    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(_entry(status="rejected"),),
        as_of_epoch=7,
    )

    result = _verify(witness)

    assert result.ok is True
    assert result.disputed_report_ids == ()


def test_builder_rejects_noncanonical_dispute_identity() -> None:
    with pytest.raises(
        ValueError,
        match="dispute_id must be a canonical sha256 reference",
    ):
        build_oracle_current_dispute_status_v1(
            report_ids=REPORT_IDS,
            dispute_entries=(
                {
                    "dispute_id": "local-unbounded-identity",
                    "report_id": REPORT_IDS[0],
                    "status": "open",
                },
            ),
            as_of_epoch=7,
        )


@pytest.mark.parametrize("now_epoch", [6, 8])
def test_status_witness_rejects_adjacent_stale_or_future_epoch(now_epoch: int) -> None:
    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(),
        as_of_epoch=7,
    )

    result = _verify(witness, now_epoch=now_epoch)

    assert result.ok is False
    assert "current dispute status as_of_epoch does not match runtime epoch" in result.errors


def test_epoch_zero_is_a_valid_boundary() -> None:
    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(),
        as_of_epoch=0,
    )

    result = verify_oracle_current_dispute_status_v1(
        witness,
        expected_report_ids=REPORT_IDS,
        expected_root=str(witness["current_dispute_status_root"]),
        now_epoch=0,
    )

    assert result.ok is True


def test_caller_selected_clean_root_cannot_replace_authoritative_open_root() -> None:
    authoritative = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(_entry(status="open"),),
        as_of_epoch=7,
    )
    caller_clean = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(),
        as_of_epoch=7,
    )

    result = verify_oracle_current_dispute_status_v1(
        caller_clean,
        expected_report_ids=REPORT_IDS,
        expected_root=str(authoritative["current_dispute_status_root"]),
        now_epoch=7,
    )

    assert result.ok is False
    assert "current dispute status root does not match verifier-selected root" in result.errors


def test_status_root_binds_the_complete_authorization_report_scope() -> None:
    subset = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS[:2],
        dispute_entries=(),
        as_of_epoch=7,
    )

    result = verify_oracle_current_dispute_status_v1(
        subset,
        expected_report_ids=REPORT_IDS,
        expected_root=str(subset["current_dispute_status_root"]),
        now_epoch=7,
    )

    assert result.ok is False
    assert "current dispute status report scope mismatch" in result.errors


def test_reordered_report_scope_rejects_even_with_recomputed_root() -> None:
    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(),
        as_of_epoch=7,
    )
    witness["included_report_ids"].reverse()
    body = {
        key: value
        for key, value in witness.items()
        if key != "current_dispute_status_root"
    }
    witness["current_dispute_status_root"] = _status_root(body)

    result = _verify(witness)

    assert result.ok is False
    assert (
        "current dispute status included_report_ids must be canonically sorted"
        in result.errors
    )


def test_mutated_status_is_rejected_even_when_disputed_ids_are_erased() -> None:
    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(_entry(status="open"),),
        as_of_epoch=7,
    )
    mutated = deepcopy(witness)
    mutated["disputed_report_ids"] = []

    result = _verify(mutated)

    assert result.ok is False
    assert "current dispute status disputed_report_ids mismatch" in result.errors
    assert "current dispute status root mismatch" in result.errors


def test_hostile_non_exact_json_value_rejects_before_hashing() -> None:
    class AlwaysEqualInt(int):
        def __eq__(self, other: object) -> bool:
            return True

    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(),
        as_of_epoch=7,
    )
    witness["as_of_epoch"] = AlwaysEqualInt(999)

    result = _verify(witness)

    assert result.ok is False
    assert result.errors == (
        "current dispute status.as_of_epoch contains a non-exact JSON primitive: AlwaysEqualInt",
    )


def test_status_witness_rejects_aggregate_exact_json_node_exhaustion() -> None:
    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(),
        as_of_epoch=7,
    )
    witness["expansion"] = [[0] * 10 for _ in range(9_100)]

    result = _verify(witness)

    assert result.ok is False
    assert len(result.errors) == 1
    assert "exceeds exact JSON node budget" in result.errors[0]


def test_unhashable_witness_cannot_borrow_verifier_selected_root() -> None:
    # Given an authoritative root that revokes one report.
    authoritative = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(_entry(status="open"),),
        as_of_epoch=7,
    )
    # And a forged clean projection whose lone surrogate prevents canonical
    # root recomputation while copying the verifier-selected root.
    forged = {
        "schema": "zenodex.oracle.current_dispute_status.v1",
        "as_of_epoch": 7,
        "included_report_ids": sorted(REPORT_IDS),
        "disputes": [
            {
                "dispute_id": "\ud800",
                "report_id": REPORT_IDS[0],
                "status": "rejected",
            }
        ],
        "disputed_report_ids": [],
        "current_dispute_status_root": authoritative[
            "current_dispute_status_root"
        ],
    }

    result = verify_oracle_current_dispute_status_v1(
        forged,
        expected_report_ids=REPORT_IDS,
        expected_root=str(authoritative["current_dispute_status_root"]),
        now_epoch=7,
    )

    assert result.ok is False
    assert result.errors == (
        "current dispute status.disputes[0].dispute_id contains a surrogate code point",
    )


def test_root_recomputation_exception_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    witness = build_oracle_current_dispute_status_v1(
        report_ids=REPORT_IDS,
        dispute_entries=(),
        as_of_epoch=7,
    )

    def fail_root_recomputation(_body: object) -> str:
        raise ValueError("injected canonical encoder failure")

    monkeypatch.setattr(status_core, "_status_root", fail_root_recomputation)

    result = verify_oracle_current_dispute_status_v1(
        witness,
        expected_report_ids=REPORT_IDS,
        expected_root=str(witness["current_dispute_status_root"]),
        now_epoch=7,
    )

    assert result.ok is False
    assert "current dispute status root could not be computed" in result.errors
