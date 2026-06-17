from __future__ import annotations

from functools import lru_cache

import pytest

import src.integration.cantor_shapeforge_bridge_verify as bridge_verify
from src.integration.cantor_shapeforge_bridge_report import build_cantor_shapeforge_bridge_report
from src.integration.cantor_shapeforge_bridge_verify import (
    verify_cantor_shapeforge_bridge_report_payload,
)


@lru_cache(maxsize=1)
def _payload() -> dict[str, object]:
    return build_cantor_shapeforge_bridge_report().to_dict()


def test_verify_accepts_current_bridge_report() -> None:
    ok, err = verify_cantor_shapeforge_bridge_report_payload(_payload())
    assert ok, err


def test_verify_rejects_status_mismatch() -> None:
    payload = dict(_payload())
    mapped_surfaces = [dict(item) for item in payload["mapped_surfaces"]]  # type: ignore[index]
    mapped_surfaces[0]["current_slice_status"] = "hypothesis"
    payload["mapped_surfaces"] = mapped_surfaces

    ok, err = verify_cantor_shapeforge_bridge_report_payload(payload)
    assert not ok
    assert err == "mapped surface 'settlement_witness_lifecycle' status mismatch"


def test_verify_rejects_missing_suggested_evidence() -> None:
    payload = dict(_payload())
    mapped_surfaces = [dict(item) for item in payload["mapped_surfaces"]]  # type: ignore[index]
    evidence_items = [dict(item) for item in mapped_surfaces[1]["suggested_evidence"]]  # type: ignore[index]
    evidence_items[0]["claim"] = "tampered claim"
    mapped_surfaces[1]["suggested_evidence"] = evidence_items
    payload["mapped_surfaces"] = mapped_surfaces

    ok, err = verify_cantor_shapeforge_bridge_report_payload(payload)
    assert not ok
    assert err == "mapped surface 'exact_out_adaptive_liveness' suggested evidence missing from world model"


def test_verify_rejects_current_mismatch_when_required() -> None:
    payload = dict(_payload())
    payload["bundle_schema"] = "tampered"

    ok, err = verify_cantor_shapeforge_bridge_report_payload(payload, require_current=True)
    assert not ok
    assert err == "unexpected bundle schema"


def test_verify_propagates_world_model_loader_programmer_errors(monkeypatch: pytest.MonkeyPatch) -> None:
    payload = dict(_payload())

    def programmer_error(_path: object) -> dict[str, object]:
        raise RuntimeError("unexpected world-model loader bug")

    monkeypatch.setattr(bridge_verify, "_load_json_object", programmer_error)

    with pytest.raises(RuntimeError, match="unexpected world-model loader bug"):
        verify_cantor_shapeforge_bridge_report_payload(payload)
