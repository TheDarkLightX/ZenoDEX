from __future__ import annotations

import pytest

from src.integration.settlement_strong_certificate import (
    SettlementPriceHistoryCertificate,
    SettlementProofFlags,
    SettlementSemanticSummary,
    SettlementStrongCertificate,
)


def _minimal_payload() -> dict[str, object]:
    return SettlementStrongCertificate(
        settlement_commitment_sha256="0" * 64,
        delta_commitment_sha256="1" * 64,
        proof_flags=SettlementProofFlags.all_true(),
        core_module_ok=1,
        feature_extension_ok=1,
        proof_binding_ok=1,
        module_bundle_ok=1,
        core_module_step={},
        feature_extension_step={},
        proof_binding_step={},
        module_bundle_step={},
    ).to_dict()


def _semantic_payload() -> dict[str, object]:
    summary = SettlementSemanticSummary(
        a=1,
        b=2,
        c=3,
        d=4,
        price_pp=5,
        price_prev=6,
        price_curr=7,
    )
    return SettlementStrongCertificate(
        settlement_commitment_sha256="0" * 64,
        delta_commitment_sha256="1" * 64,
        proof_flags=SettlementProofFlags.all_true(),
        core_module_ok=1,
        feature_extension_ok=1,
        proof_binding_ok=1,
        module_bundle_ok=1,
        core_module_step={},
        feature_extension_step={},
        proof_binding_step={},
        module_bundle_step={},
        semantic_summary=summary,
        price_history_certificate=SettlementPriceHistoryCertificate(
            price_pp=summary.price_pp,
            price_prev=summary.price_prev,
            price_curr=summary.price_curr,
            price_trace_sha256="2" * 64,
        ),
        compact_bundle_step={},
        compact_bundle_ok=1,
        full_price_rails_step={},
        full_price_rails_ok=1,
    ).to_dict()


@pytest.mark.parametrize("field", ("cpmm_ok", "balance_ok", "binding_ok"))
def test_settlement_proof_flags_from_dict_rejects_bool_fields(field: str) -> None:
    payload = _minimal_payload()
    proof_flags = dict(payload["proof_flags"])  # type: ignore[arg-type]
    proof_flags[field] = True
    payload["proof_flags"] = proof_flags

    with pytest.raises(ValueError, match=f"{field} must be an int"):
        SettlementStrongCertificate.from_dict(payload)


@pytest.mark.parametrize("field", ("core_module_ok", "feature_extension_ok", "proof_binding_ok", "module_bundle_ok"))
def test_settlement_strong_certificate_from_dict_rejects_bool_ok_fields(field: str) -> None:
    payload = _minimal_payload()
    payload[field] = True

    with pytest.raises(ValueError, match=f"{field} must be an int"):
        SettlementStrongCertificate.from_dict(payload)


@pytest.mark.parametrize("field", ("a", "price_pp", "price_curr"))
def test_settlement_semantic_summary_from_dict_rejects_bool_fields(field: str) -> None:
    payload = _semantic_payload()
    semantic_summary = dict(payload["semantic_summary"])  # type: ignore[arg-type]
    semantic_summary[field] = True
    payload["semantic_summary"] = semantic_summary

    with pytest.raises(ValueError, match=f"{field} must be an int"):
        SettlementStrongCertificate.from_dict(payload)


@pytest.mark.parametrize("field", ("price_pp", "price_curr"))
def test_settlement_price_history_certificate_from_dict_rejects_bool_fields(field: str) -> None:
    payload = _semantic_payload()
    price_history = dict(payload["price_history_certificate"])  # type: ignore[arg-type]
    price_history[field] = True
    payload["price_history_certificate"] = price_history

    with pytest.raises(ValueError, match=f"{field} must be an int"):
        SettlementStrongCertificate.from_dict(payload)


@pytest.mark.parametrize("field", ("compact_bundle_ok", "full_price_rails_ok"))
def test_settlement_strong_certificate_from_dict_rejects_bool_optional_ok_fields(field: str) -> None:
    payload = _semantic_payload()
    payload[field] = True

    with pytest.raises(ValueError, match=f"{field} must be an int"):
        SettlementStrongCertificate.from_dict(payload)
