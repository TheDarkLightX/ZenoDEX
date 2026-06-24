from __future__ import annotations

from functools import lru_cache

import src.integration.cantor_shapeforge_bridge_verify as cantor_shapeforge_bridge_verify
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


def test_verify_reports_expected_world_model_json_error(tmp_path) -> None:
    world_model = tmp_path / "world-model.json"
    world_model.write_text("[", encoding="utf-8")
    payload = dict(_payload())
    payload["world_model_path"] = str(world_model)

    ok, err = verify_cantor_shapeforge_bridge_report_payload(payload)

    assert ok is False
    assert err is not None
    assert "Expecting value" in err


def test_verify_sanitizes_unexpected_world_model_loader_fault(monkeypatch) -> None:
    def _faulting_loader(_path):
        raise RuntimeError("do not leak shapeforge internals")

    monkeypatch.setattr(
        cantor_shapeforge_bridge_verify,
        "_load_json_object",
        _faulting_loader,
    )

    ok, err = verify_cantor_shapeforge_bridge_report_payload(_payload())

    assert ok is False
    assert err == "world_model_load_internal_error:RuntimeError"
