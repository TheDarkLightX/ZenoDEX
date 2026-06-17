from __future__ import annotations

import json
from pathlib import Path

import pytest

import src.agents.zenograph_fact_pack as fact_pack_module
from src.agents.krr_bundle_artifacts import KRRReviewRecord
from src.agents.zenograph_fact_pack import (
    ZenoGraphFactRecord,
    build_zenograph_fact_pack,
    load_zenograph_fact_pack_file,
    sign_zenograph_fact_pack,
    verify_zenograph_fact_pack_signature,
    zenograph_runtime_facts,
)


def _runtime_review(pack_name: str) -> KRRReviewRecord:
    return KRRReviewRecord(
        review_id=f"{pack_name}.review.runtime",
        target_kind="bundle",
        target_id=pack_name,
        decision="approve",
        reviewer="security.review",
        reviewed_at="2026-03-26T00:10:00Z",
        rationale="fact pack provenance complete and safe for advisory runtime use",
        approved_for_runtime=True,
        provenance_ok=True,
    )


def _signed_runtime_fact_pack():
    pack = build_zenograph_fact_pack(
        pack_name="zenograph.shadow.1",
        built_at="2026-03-26T00:15:00Z",
        compiler_version="zenograph_fact_pack_v1",
        facts=(
            ZenoGraphFactRecord(
                fact_id="protocol.governance_attack_risk",
                subject_id="protocol",
                predicate="governance_attack_risk",
                value="elevated",
                source_id="feed.news.alpha",
                microtheory="RiskPolicy",
                observed_at="2026-03-26T00:00:00Z",
            ),
        ),
        review_records=(_runtime_review("zenograph.shadow.1"),),
    )
    return sign_zenograph_fact_pack(pack, privkey=21)


def test_zenograph_fact_pack_roundtrip_signature_and_runtime_facts(tmp_path: Path) -> None:
    signed = _signed_runtime_fact_pack()
    assert verify_zenograph_fact_pack_signature(signed) is True

    path = tmp_path / "fact_pack.json"
    path.write_text(json.dumps(signed.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    loaded = load_zenograph_fact_pack_file(path)
    assert zenograph_runtime_facts(loaded) == {
        ("protocol", "governance_attack_risk"): "elevated"
    }


def test_zenograph_fact_pack_requires_runtime_review() -> None:
    with pytest.raises(ValueError, match="approved runtime review"):
        build_zenograph_fact_pack(
            pack_name="zenograph.no.review",
            built_at="2026-03-26T00:15:00Z",
            compiler_version="zenograph_fact_pack_v1",
            facts=(
                ZenoGraphFactRecord(
                    fact_id="protocol.governance_attack_risk",
                    subject_id="protocol",
                    predicate="governance_attack_risk",
                    value="elevated",
                ),
            ),
            review_records=(),
        )


def test_zenograph_fact_pack_signature_propagates_backend_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    signed = _signed_runtime_fact_pack()

    class BrokenBLS:
        @staticmethod
        def Verify(_pk: bytes, _message: bytes, _sig: bytes) -> bool:
            raise RuntimeError("broken BLS verifier")

    monkeypatch.setattr(fact_pack_module, "G2Basic", BrokenBLS)

    with pytest.raises(RuntimeError, match="broken BLS verifier"):
        verify_zenograph_fact_pack_signature(signed)
