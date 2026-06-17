from __future__ import annotations

import json
from pathlib import Path

import pytest

import src.agents.krr_bundle_artifacts as krr_bundle_artifacts
from src.agents.krr_bundle_artifacts import (
    KRRCanonicalClaim,
    KRREvidenceRecord,
    KRRReviewRecord,
    KRRSourceSnapshot,
    build_autotrader_krr_bundle,
    bundle_runtime_artifacts,
    load_autotrader_krr_bundle_file,
    sign_autotrader_krr_bundle,
    verify_autotrader_krr_bundle_signature,
)
from src.state.canonical import sha256_hex


def _snapshot(*, source_id: str = "feed.news.alpha") -> KRRSourceSnapshot:
    body = b"macro regime note"
    return KRRSourceSnapshot(
        snapshot_id=f"{source_id}.snap1",
        source_id=source_id,
        source_class="research_paper",
        source_uri="https://example.com/research/note",
        fetched_at="2026-03-12T00:00:00Z",
        observed_at="2026-03-12T00:00:00Z",
        media_type="text/plain",
        content_sha256=sha256_hex(body),
        content_bytes=len(body),
        trust_ceiling="advisory",
        parser_id="raw_snapshot",
        parser_version="v1",
        text_sha256=sha256_hex(body),
        title="Macro Note",
    )


def _evidence(snapshot: KRRSourceSnapshot, *, text: str = "Spread widening observed.") -> KRREvidenceRecord:
    return KRREvidenceRecord(
        evidence_id=f"{snapshot.snapshot_id}.e1",
        snapshot_id=snapshot.snapshot_id,
        locator={"kind": "paragraph", "index": 1},
        extracted_at="2026-03-12T00:05:00Z",
        excerpt_sha256=sha256_hex(text.encode("utf-8")),
        excerpt_text=text,
        claim_family="market_regime",
    )


def _claim(
    snapshot: KRRSourceSnapshot,
    evidence: KRREvidenceRecord,
) -> KRRCanonicalClaim:
    return KRRCanonicalClaim(
        claim_id="claim.market_regime.1",
        entity_id="market.btcusd",
        fact_family="market_regime",
        attribute_key="regime",
        value="volatile",
        evidence_ids=(evidence.evidence_id,),
        source_ids=(snapshot.source_id,),
        valid_from="2026-03-12T00:00:00Z",
        unit=None,
        currency=None,
        jurisdiction="global",
    )


def _bundle_review(bundle_name: str) -> KRRReviewRecord:
    return KRRReviewRecord(
        review_id=f"{bundle_name}.review.runtime",
        target_kind="bundle",
        target_id=bundle_name,
        decision="approve",
        reviewer="security.review",
        reviewed_at="2026-03-12T00:10:00Z",
        rationale="provenance complete and runtime safe",
        approved_for_runtime=True,
        provenance_ok=True,
    )


def _claim_review(claim_id: str) -> KRRReviewRecord:
    return KRRReviewRecord(
        review_id=f"{claim_id}.review",
        target_kind="claim",
        target_id=claim_id,
        decision="approve",
        reviewer="research.review",
        reviewed_at="2026-03-12T00:12:00Z",
        rationale="claim supported by cited excerpt",
        approved_for_runtime=False,
        provenance_ok=True,
    )


def test_autotrader_krr_bundle_roundtrip_signature_and_runtime_artifacts(tmp_path: Path) -> None:
    snapshot = _snapshot()
    evidence = _evidence(snapshot)
    claim = _claim(snapshot, evidence)
    bundle = build_autotrader_krr_bundle(
        bundle_name="bundle.shadow.1",
        built_at="2026-03-12T00:15:00Z",
        compiler_version="bundle_builder_v1",
        policy_version="policy_v1",
        runtime_krr_kb={
            "check_priors": {"policy::budget_guard": {"base_weight": 1.5}},
            "operator_priors": {},
            "semantic_rules": [],
            "check_family_priors": {},
        },
        runtime_external_signals={
            "external_signals": [
                {
                    "signal_id": "sig.news.1",
                    "source_id": snapshot.source_id,
                    "source_kind": "advisory_external",
                    "trust_tier": "advisory",
                    "freshness_ok": True,
                    "auth_ok": False,
                    "advisory_only": True,
                    "tags": ["macro"],
                }
            ]
        },
        runtime_signal_source_registry={
            "entries": [
                {
                    "source_id": snapshot.source_id,
                    "source_kind": "advisory_external",
                    "allowed_trust_tiers": ["advisory"],
                    "require_advisory_only": True,
                }
            ]
        },
        runtime_history={
            "history_source_stats": {snapshot.source_id: {"submit": 5, "reject": 1, "skip": 2}}
        },
        source_snapshots=(snapshot,),
        evidence_records=(evidence,),
        canonical_claims=(claim,),
        review_records=(_bundle_review("bundle.shadow.1"), _claim_review(claim.claim_id)),
    )

    signed = sign_autotrader_krr_bundle(bundle, privkey=21)
    assert verify_autotrader_krr_bundle_signature(signed) is True

    bundle_path = tmp_path / "bundle.json"
    bundle_path.write_text(json.dumps(signed.to_dict(), indent=2, sort_keys=True), encoding="utf-8")

    loaded = load_autotrader_krr_bundle_file(bundle_path)
    runtime_krr_kb, external_signals, signal_source_registry, runtime_history = bundle_runtime_artifacts(
        loaded
    )
    assert runtime_krr_kb is not None
    assert float(runtime_krr_kb["check_priors"]["policy::budget_guard"]["base_weight"]) == 1.5
    assert len(external_signals) == 1
    assert external_signals[0].source_id == snapshot.source_id
    assert signal_source_registry is not None
    assert len(signal_source_registry.entries) == 1
    assert runtime_history is not None
    assert loaded.bundle_hash_hex() == signed.bundle_hash_hex()


def test_autotrader_krr_bundle_signature_propagates_unexpected_bls_backend_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class ExplodingBLS:
        @staticmethod
        def Verify(*_args: object) -> bool:
            raise RuntimeError("backend invariant failure")

    snapshot = _snapshot()
    evidence = _evidence(snapshot)
    claim = _claim(snapshot, evidence)
    bundle = build_autotrader_krr_bundle(
        bundle_name="bundle.shadow.backend.failure",
        built_at="2026-03-12T00:15:00Z",
        compiler_version="bundle_builder_v1",
        policy_version="policy_v1",
        runtime_krr_kb={"check_priors": {}, "operator_priors": {}, "semantic_rules": [], "check_family_priors": {}},
        runtime_external_signals={"external_signals": []},
        runtime_signal_source_registry={"entries": []},
        runtime_history={"history_source_stats": {}},
        source_snapshots=(snapshot,),
        evidence_records=(evidence,),
        canonical_claims=(claim,),
        review_records=(_bundle_review("bundle.shadow.backend.failure"), _claim_review(claim.claim_id)),
    )
    signed = sign_autotrader_krr_bundle(bundle, privkey=21)
    monkeypatch.setattr(krr_bundle_artifacts, "G2Basic", ExplodingBLS)

    with pytest.raises(RuntimeError, match="backend invariant failure"):
        verify_autotrader_krr_bundle_signature(signed)


def test_autotrader_krr_bundle_requires_approved_runtime_review() -> None:
    snapshot = _snapshot()
    with pytest.raises(ValueError, match="approved runtime review"):
        build_autotrader_krr_bundle(
            bundle_name="bundle.no.review",
            built_at="2026-03-12T00:15:00Z",
            compiler_version="bundle_builder_v1",
            policy_version="policy_v1",
            source_snapshots=(snapshot,),
        )


def test_autotrader_krr_bundle_rejects_runtime_signal_source_without_snapshot() -> None:
    with pytest.raises(ValueError, match="missing a source snapshot"):
        build_autotrader_krr_bundle(
            bundle_name="bundle.bad.signal",
            built_at="2026-03-12T00:15:00Z",
            compiler_version="bundle_builder_v1",
            policy_version="policy_v1",
            runtime_external_signals={
                "external_signals": [
                    {
                        "signal_id": "sig.news.1",
                        "source_id": "feed.news.alpha",
                        "source_kind": "advisory_external",
                        "trust_tier": "advisory",
                        "freshness_ok": True,
                        "auth_ok": False,
                        "advisory_only": True,
                    }
                ]
            },
            runtime_signal_source_registry={
                "entries": [
                    {
                        "source_id": "feed.news.alpha",
                        "source_kind": "advisory_external",
                        "allowed_trust_tiers": ["advisory"],
                        "require_advisory_only": True,
                    }
                ]
            },
            review_records=(_bundle_review("bundle.bad.signal"),),
        )


def test_autotrader_krr_bundle_derives_source_quality_from_history_and_reviews() -> None:
    snapshot = _snapshot(source_id="oracle.alpha")
    source_review = KRRReviewRecord(
        review_id="oracle.alpha.review",
        target_kind="source",
        target_id=snapshot.source_id,
        decision="approve",
        reviewer="ops.review",
        reviewed_at="2026-03-12T00:20:00Z",
        rationale="source has stable provenance",
        approved_for_runtime=False,
        provenance_ok=True,
    )
    bundle = build_autotrader_krr_bundle(
        bundle_name="bundle.source.quality",
        built_at="2026-03-12T00:15:00Z",
        compiler_version="bundle_builder_v1",
        policy_version="policy_v1",
        runtime_history={
            "history_source_stats": {
                snapshot.source_id: {"submit": 4, "reject": 1, "skip": 2}
            }
        },
        source_snapshots=(snapshot,),
        review_records=(_bundle_review("bundle.source.quality"), source_review),
    )
    assert len(bundle.derived_source_quality) == 1
    row = bundle.derived_source_quality[0]
    assert row.source_id == snapshot.source_id
    assert row.sample_size == 5
    assert row.submit_count == 4
    assert row.reject_count == 1
    assert row.skip_count == 2
    assert row.posterior_alpha == 6.0
    assert row.posterior_beta == 2.0
    assert 0.0 <= row.posterior_lower_95 <= row.posterior_mean <= 1.0
