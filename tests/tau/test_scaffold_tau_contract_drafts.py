from __future__ import annotations

import json
from pathlib import Path

from src.integration.tau_runner import ROOT
from tools.check_tau_formal_plan import DEFAULT_PLAN
from tools.scaffold_tau_contract_drafts import build_scaffold_bundle


def test_scaffold_tau_contract_drafts_bundle() -> None:
    semantic_view_path = ROOT / "formal" / "tau" / "recommended_semantic_view.json"
    semantic_view = json.loads(semantic_view_path.read_text(encoding="utf-8"))
    proof_plan = json.loads(Path(DEFAULT_PLAN).read_text(encoding="utf-8"))

    packets = semantic_view.get("packets", [])
    assert isinstance(packets, list) and packets
    host_projected = next(
        str(packet["spec_id"])
        for packet in packets
        if isinstance(packet, dict) and all(str(ty) == "sbf" for ty in packet.get("input_streams", {}).values())
    )
    native = next(
        str(packet["spec_id"])
        for packet in packets
        if isinstance(packet, dict) and any(str(ty) != "sbf" for ty in packet.get("input_streams", {}).values())
    )

    bundle = build_scaffold_bundle(
        semantic_view=semantic_view,
        proof_plan=proof_plan,
        include_spec_ids={host_projected, native},
    )
    assert bundle["schema"] == "zenodex/tau/contract-scaffold-bundle/v1"
    assert bundle["spec_count"] == 2
    assert bundle["formal_contract_draft_count"] == 2
    assert bundle["formal_atlas_draft_count"] == 2
    assert bundle["lightweight_draft_count"] >= 1

    formal_ids = {row["spec_id"] for row in bundle["formal_contract_drafts"]}
    assert formal_ids == {host_projected, native}
    assert all(row["contract_status"] == "draft" for row in bundle["formal_contract_drafts"])
    assert all(row["atlas_status"] == "draft" for row in bundle["formal_atlas_drafts"])
