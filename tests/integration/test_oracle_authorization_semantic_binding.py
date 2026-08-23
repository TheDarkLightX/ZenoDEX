from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from dataclasses import asdict, replace
from pathlib import Path

from src.integration.zeno_oracle_authorization import (
    ZUSD_COLLATERAL_QUERY_ID,
    ZUSD_LIQUIDATE_VAULT_PROFILE_ID,
    ZUSD_MINT_PROFILE_ID,
)
from src.integration.zeno_oracle_settlement_authorization import critical_settlement_profile_id
from tests.integration.oracle_authorization_test_helpers import authorization_bundle
from tools.check_oracle_authorization_semantic_binding import (
    SCHEMA,
    OracleAuthorization,
    RuntimeActionFacts,
    check_authorization_for_runtime,
    check_authorization_payload,
    check_critical_consumer_authorization,
    economic_envelope_hash,
    oracle_value_hash,
    semantic_hash,
    verify_opaque_authorization,
    verify_typed_authorization,
)


def _hash(domain: str, name: str) -> str:
    return semantic_hash(domain, {"name": name})


def test_zusd_bridge_identifiers_match_canonical_oracle_policy_vectors() -> None:
    expected_query_id = "sha256:" + hashlib.sha256(
        b"zenodex.oracle.query.zusd.collateral_price_e8"
    ).hexdigest()

    def expected_profile_id(*, action_kind: str, freshness: int) -> str:
        payload = {
            "schema": "zenodex.oracle.consumer_profile.v1",
            "consumer_module": "zenodex.zusd",
            "action_kind": action_kind,
            "query_id": expected_query_id,
            "required_evidence_floor": "O3",
            "max_freshness_window_epochs": freshness,
            "critical": True,
        }
        encoded = json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode("utf-8")
        return "sha256:" + hashlib.sha256(encoded).hexdigest()

    assert ZUSD_COLLATERAL_QUERY_ID == expected_query_id
    assert ZUSD_MINT_PROFILE_ID == expected_profile_id(
        action_kind="mint",
        freshness=2,
    )
    assert ZUSD_LIQUIDATE_VAULT_PROFILE_ID == expected_profile_id(
        action_kind="liquidate_vault",
        freshness=1,
    )


def _refresh_terminal_graph_roots(bundle: dict) -> None:
    graph = bundle["receipt_graph"]
    graph["report_leaf_root"] = semantic_hash(
        "zeno_oracle.report_leaf_root.v1",
        {"reports": graph["report_leaf_commitments"]},
    )
    body = {key: value for key, value in graph.items() if key != "receipt_graph_root"}
    graph["receipt_graph_root"] = semantic_hash("zeno_oracle.receipt_graph.v1", body)
    bundle["authorization"]["receipt_graph_root"] = graph["receipt_graph_root"]


def _valid_pair() -> tuple[OracleAuthorization, RuntimeActionFacts]:
    query_id = "query:AGRS/ZDEX"
    value_e8 = 123_456_789
    observed_epoch = 42
    action_facts_hash = _hash("zenodex.action_facts.v1", "zusd-mint-vault-7")
    pre_state_hash = _hash("zenodex.pre_state.v1", "vault-7-state-a")
    action_id = _hash(
        "zenodex.action_id.v1",
        f"{action_facts_hash}:{pre_state_hash}:{query_id}:{value_e8}",
    )
    authorization = OracleAuthorization(
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id=action_id,
        action_facts_hash=action_facts_hash,
        pre_state_hash=pre_state_hash,
        profile_id="critical-zusd-v1",
        query_id=query_id,
        value_e8=value_e8,
        value_hash=oracle_value_hash(
            query_id=query_id,
            value_e8=value_e8,
            observed_epoch=observed_epoch,
        ),
        confidence_e8=10_000,
        deviation_bps=32,
        observed_epoch=observed_epoch,
        expires_at_epoch=44,
        feed_id="feed:agrs-zdex:v1",
        feed_registry_root=_hash("zenodex.feed_registry.v1", "r1"),
        query_policy_root=_hash("zenodex.query_policy.v1", "q1"),
        source_registry_root=_hash("zenodex.source_registry.v1", "s1"),
        reporter_registry_root=_hash("zenodex.reporter_registry.v1", "p1"),
        evidence_class="O3",
        economic_envelope_id="econ:small-notional-v1",
        receipt_graph_root=_hash("zenodex.receipt_graph.v1", "g1"),
    )
    runtime = RuntimeActionFacts(
        consumer_module=authorization.consumer_module,
        action_kind=authorization.action_kind,
        action_id=authorization.action_id,
        action_facts_hash=authorization.action_facts_hash,
        pre_state_hash=authorization.pre_state_hash,
        profile_id=authorization.profile_id,
        query_id=authorization.query_id,
        runtime_value_e8=authorization.value_e8,
        now_epoch=43,
    )
    return authorization, runtime


def _economic_envelope_for(
    authorization: OracleAuthorization,
    *,
    notional_value_e8: int = 1_000,
    max_extractable_value_e8: int = 100,
    action_kind: str | None = None,
    reporter_count: int = 3,
    reporter_bond_required_e8: int = 1_000,
) -> dict:
    return {
        "schema": "zenodex.oracle.economic_security_envelope.v1",
        "query_id": authorization.query_id,
        "consumer_module": authorization.consumer_module,
        "action_kind": action_kind or authorization.action_kind,
        "notional_value_e8": notional_value_e8,
        "max_extractable_value_e8": max_extractable_value_e8,
        "reporter_count": reporter_count,
        "reporter_bond_required_e8": reporter_bond_required_e8,
        "slash_fraction_bps": 10_000,
        "deterrence_margin_bps": 0,
    }


def _check_with_runtime(
    authorization_payload: dict,
    runtime: RuntimeActionFacts,
    *,
    runtime_notional_value_e8: int | None = None,
) -> dict:
    return check_critical_consumer_authorization(
        authorization_payload,
        consumer_module=runtime.consumer_module,
        action_kind=runtime.action_kind,
        action_id=runtime.action_id,
        action_facts_hash=runtime.action_facts_hash,
        pre_state_hash=runtime.pre_state_hash,
        query_id=runtime.query_id,
        runtime_value_e8=runtime.runtime_value_e8,
        now_epoch=runtime.now_epoch,
        runtime_notional_value_e8=runtime_notional_value_e8,
    )


def test_typed_authorization_accepts_matching_runtime_facts() -> None:
    authorization, runtime = _valid_pair()

    opaque_ok, opaque_errors = verify_opaque_authorization(authorization, runtime)
    typed_ok, typed_errors = verify_typed_authorization(authorization, runtime)

    assert opaque_ok is True
    assert opaque_errors == ()
    assert typed_ok is True
    assert typed_errors == ()


def test_typed_authorization_accepts_bound_economic_envelope() -> None:
    authorization, runtime = _valid_pair()
    envelope = _economic_envelope_for(authorization, notional_value_e8=1_000)
    authorization = replace(authorization, economic_envelope_id=economic_envelope_hash(envelope))
    bundle = authorization_bundle(asdict(authorization), include_economic_envelope=False)
    bundle["economic_envelope"] = envelope

    result = _check_with_runtime(bundle, runtime, runtime_notional_value_e8=999)

    assert result["typed_ok"] is True
    assert result["economic_envelope_ok"] is True
    assert result["economic_envelope_errors"] == []


def test_typed_authorization_rejects_runtime_notional_above_economic_envelope() -> None:
    authorization, runtime = _valid_pair()
    envelope = _economic_envelope_for(authorization, notional_value_e8=1_000)
    authorization = replace(authorization, economic_envelope_id=economic_envelope_hash(envelope))
    bundle = authorization_bundle(asdict(authorization), include_economic_envelope=False)
    bundle["economic_envelope"] = envelope

    result = _check_with_runtime(bundle, runtime, runtime_notional_value_e8=1_001)

    assert result["typed_ok"] is False
    assert result["economic_envelope_ok"] is False
    assert "runtime_notional_value_e8 exceeds economic envelope" in result["economic_envelope_errors"]


def test_typed_authorization_rejects_unbound_economic_envelope_id() -> None:
    authorization, runtime = _valid_pair()
    envelope = _economic_envelope_for(authorization, notional_value_e8=1_000)
    authorization = replace(authorization, economic_envelope_id="econ:small-notional-v1")
    bundle = authorization_bundle(asdict(authorization), include_economic_envelope=False)
    bundle["economic_envelope"] = envelope

    result = _check_with_runtime(bundle, runtime, runtime_notional_value_e8=999)

    assert result["typed_ok"] is False
    assert result["economic_envelope_ok"] is False
    assert "economic_envelope_id does not bind economic_envelope" in result["economic_envelope_errors"]


def test_typed_authorization_rejects_economic_envelope_action_mismatch() -> None:
    authorization, runtime = _valid_pair()
    envelope = _economic_envelope_for(authorization, action_kind="liquidate")
    authorization = replace(authorization, economic_envelope_id=economic_envelope_hash(envelope))
    bundle = authorization_bundle(asdict(authorization), include_economic_envelope=False)
    bundle["economic_envelope"] = envelope

    result = _check_with_runtime(bundle, runtime, runtime_notional_value_e8=999)

    assert result["typed_ok"] is False
    assert result["economic_envelope_ok"] is False
    assert "economic_envelope action_kind does not match authorization" in result["economic_envelope_errors"]


def test_critical_consumer_requires_economic_envelope() -> None:
    authorization, runtime = _valid_pair()
    bundle = authorization_bundle(asdict(authorization), include_economic_envelope=False)

    result = _check_with_runtime(bundle, runtime)

    assert result["typed_ok"] is False
    assert result["economic_envelope_ok"] is False
    assert "economic_envelope required" in result["economic_envelope_errors"]


def test_critical_consumer_rejects_economic_envelope_reporter_count_mismatch() -> None:
    authorization, runtime = _valid_pair()
    bundle = authorization_bundle(asdict(authorization))
    bundle["economic_envelope"]["reporter_count"] = 2
    bundle["authorization"]["economic_envelope_id"] = economic_envelope_hash(bundle["economic_envelope"])

    result = _check_with_runtime(bundle, runtime)

    assert result["typed_ok"] is False
    assert result["economic_envelope_ok"] is False
    assert "economic_envelope reporter_count does not match receipt_graph" in result["economic_envelope_errors"]


def test_critical_consumer_rejects_economic_envelope_bond_requirement_mismatch() -> None:
    authorization, runtime = _valid_pair()
    bundle = authorization_bundle(asdict(authorization))
    bundle["economic_envelope"]["reporter_bond_required_e8"] = 2_000
    bundle["authorization"]["economic_envelope_id"] = economic_envelope_hash(bundle["economic_envelope"])

    result = _check_with_runtime(bundle, runtime)

    assert result["typed_ok"] is False
    assert result["economic_envelope_ok"] is False
    assert (
        "economic_envelope reporter_bond_required_e8 does not match receipt_graph required_bond_e8"
        in result["economic_envelope_errors"]
    )


def test_opaque_action_id_does_not_prove_runtime_value_matches() -> None:
    authorization, runtime = _valid_pair()
    runtime = replace(runtime, runtime_value_e8=authorization.value_e8 + 1)

    opaque_ok, opaque_errors = verify_opaque_authorization(authorization, runtime)
    typed_ok, typed_errors = verify_typed_authorization(authorization, runtime)

    assert opaque_ok is True
    assert opaque_errors == ()
    assert typed_ok is False
    assert "runtime_value_e8 mismatch" in typed_errors


def test_opaque_authorization_rejects_bool_epoch_fields() -> None:
    authorization, runtime = _valid_pair()
    authorization = replace(authorization, expires_at_epoch=True)
    runtime = replace(runtime, now_epoch=True)

    opaque_ok, opaque_errors = verify_opaque_authorization(authorization, runtime)

    assert opaque_ok is False
    assert "expires_at_epoch must be an int" in opaque_errors
    assert "now_epoch must be an int" in opaque_errors


def test_typed_authorization_rejects_bool_numeric_fields() -> None:
    authorization, runtime = _valid_pair()
    authorization = replace(
        authorization,
        value_e8=True,
        confidence_e8=True,
        deviation_bps=True,
        observed_epoch=True,
        expires_at_epoch=True,
        value_hash=oracle_value_hash(
            query_id=authorization.query_id,
            value_e8=1,
            observed_epoch=1,
        ),
    )
    runtime = replace(runtime, runtime_value_e8=True, now_epoch=True)

    typed_ok, typed_errors = verify_typed_authorization(authorization, runtime)

    assert typed_ok is False
    assert "value_e8 must be an int" in typed_errors
    assert "runtime_value_e8 must be an int" in typed_errors
    assert "confidence_e8 must be an int" in typed_errors
    assert "deviation_bps must be an int" in typed_errors
    assert "observed_epoch must be an int" in typed_errors
    assert "expires_at_epoch must be an int" in typed_errors
    assert "now_epoch must be an int" in typed_errors


def test_opaque_action_id_does_not_prove_pre_state_or_action_facts_match() -> None:
    authorization, runtime = _valid_pair()
    runtime = replace(
        runtime,
        action_facts_hash=_hash("zenodex.action_facts.v1", "different-action-facts"),
        pre_state_hash=_hash("zenodex.pre_state.v1", "different-pre-state"),
    )

    opaque_ok, opaque_errors = verify_opaque_authorization(authorization, runtime)
    typed_ok, typed_errors = verify_typed_authorization(authorization, runtime)

    assert opaque_ok is True
    assert opaque_errors == ()
    assert typed_ok is False
    assert "action_facts_hash mismatch" in typed_errors
    assert "pre_state_hash mismatch" in typed_errors


def test_cli_rejects_semantic_mismatch_even_when_opaque_fields_match(tmp_path: Path) -> None:
    authorization, runtime = _valid_pair()
    runtime = replace(runtime, runtime_value_e8=authorization.value_e8 + 1)
    payload_path = tmp_path / "oracle_authorization.json"
    payload_path.write_text(
        json.dumps(
            {
                "authorization": asdict(authorization),
                "runtime_action": asdict(runtime),
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_oracle_authorization_semantic_binding.py",
            str(payload_path),
            "--format",
            "json",
        ],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    result = json.loads(proc.stdout)

    assert proc.returncode == 1
    assert result["schema"] == SCHEMA
    assert result["opaque_ok"] is True
    assert result["typed_ok"] is False
    assert "runtime_value_e8 mismatch" in result["typed_errors"]


def test_payload_checker_reports_typed_success() -> None:
    authorization, runtime = _valid_pair()

    result = check_authorization_payload(
        {"authorization": asdict(authorization), "runtime_action": asdict(runtime)}
    )

    assert result["schema"] == SCHEMA
    assert result["opaque_ok"] is True
    assert result["typed_ok"] is True


def test_typed_authorization_rejects_future_observation() -> None:
    authorization, runtime = _valid_pair()
    authorization = replace(authorization, observed_epoch=runtime.now_epoch + 1)

    typed_ok, typed_errors = verify_typed_authorization(authorization, runtime)

    assert typed_ok is False
    assert "authorization observed in the future" in typed_errors


def test_typed_authorization_rejects_invalid_uncertainty_domain() -> None:
    authorization, runtime = _valid_pair()
    authorization = replace(authorization, confidence_e8=-1, deviation_bps=10_001)

    typed_ok, typed_errors = verify_typed_authorization(authorization, runtime)

    assert typed_ok is False
    assert "confidence_e8 must be non-negative" in typed_errors
    assert "deviation_bps must be in [0, 10000]" in typed_errors


def test_typed_authorization_rejects_malformed_hash_roots() -> None:
    authorization, runtime = _valid_pair()
    authorization = replace(
        authorization,
        receipt_graph_root="receipt-root-without-hash-domain",
        query_policy_root="sha256:not-hex",
    )

    typed_ok, typed_errors = verify_typed_authorization(authorization, runtime)

    assert typed_ok is False
    assert "receipt_graph_root must be a sha256 reference" in typed_errors
    assert "query_policy_root must be a sha256 reference" in typed_errors


def test_typed_authorization_rejects_below_o3_evidence() -> None:
    authorization, runtime = _valid_pair()
    authorization = replace(authorization, evidence_class="O2")

    typed_ok, typed_errors = verify_typed_authorization(authorization, runtime)

    assert typed_ok is False
    assert "evidence_class below required O3" in typed_errors


def test_runtime_adapter_uses_actual_runtime_facts_not_bundle_claims() -> None:
    authorization, bundled_runtime = _valid_pair()
    actual_runtime = replace(bundled_runtime, runtime_value_e8=authorization.value_e8 + 10)
    bundle = {
        "authorization": asdict(authorization),
        "runtime_action": asdict(bundled_runtime),
        **authorization_bundle(asdict(authorization)),
    }

    bundle_result = check_authorization_payload(bundle)
    adapter_result = check_authorization_for_runtime(bundle, actual_runtime)

    assert bundle_result["typed_ok"] is True
    assert adapter_result["opaque_ok"] is True
    assert adapter_result["typed_ok"] is False
    assert "runtime_value_e8 mismatch" in adapter_result["typed_errors"]


def test_critical_consumer_wrapper_accepts_zusd_mint_and_rejects_wrong_profile() -> None:
    authorization, runtime = _valid_pair()
    accepted = check_critical_consumer_authorization(
        authorization_bundle(asdict(authorization)),
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id=runtime.action_id,
        action_facts_hash=runtime.action_facts_hash,
        pre_state_hash=runtime.pre_state_hash,
        query_id=runtime.query_id,
        runtime_value_e8=runtime.runtime_value_e8,
        now_epoch=runtime.now_epoch,
    )
    wrong_profile = replace(authorization, profile_id="critical-perps-v1")
    rejected = check_critical_consumer_authorization(
        authorization_bundle(asdict(wrong_profile)),
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id=runtime.action_id,
        action_facts_hash=runtime.action_facts_hash,
        pre_state_hash=runtime.pre_state_hash,
        query_id=runtime.query_id,
        runtime_value_e8=runtime.runtime_value_e8,
        now_epoch=runtime.now_epoch,
    )

    assert accepted["typed_ok"] is True
    assert accepted["critical_consumer_profile"] == "critical-zusd-v1"
    assert rejected["typed_ok"] is False
    assert "profile_id mismatch" in rejected["opaque_errors"]
    assert "critical profile mismatch" in rejected["typed_errors"]


def test_critical_consumer_rejects_receipt_outside_profile_freshness_window() -> None:
    authorization, runtime = _valid_pair()
    stale_observed_epoch = runtime.now_epoch - 3
    stale_authorization = replace(
        authorization,
        observed_epoch=stale_observed_epoch,
        expires_at_epoch=runtime.now_epoch + 1,
        value_hash=oracle_value_hash(
            query_id=authorization.query_id,
            value_e8=authorization.value_e8,
            observed_epoch=stale_observed_epoch,
        ),
    )

    result = check_critical_consumer_authorization(
        authorization_bundle(asdict(stale_authorization)),
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id=runtime.action_id,
        action_facts_hash=runtime.action_facts_hash,
        pre_state_hash=runtime.pre_state_hash,
        query_id=runtime.query_id,
        runtime_value_e8=runtime.runtime_value_e8,
        now_epoch=runtime.now_epoch,
    )

    assert result["typed_ok"] is False
    assert "authorization freshness window exceeds runtime profile" in result["typed_errors"]
    assert "authorization observed_epoch outside runtime freshness window" in result["typed_errors"]


def test_critical_consumer_wrapper_covers_named_surfaces() -> None:
    authorization, runtime = _valid_pair()
    surfaces = [
        ("zenodex.zusd", "liquidate", "critical-zusd-v1", 1),
        ("zenodex.perps", "settle_epoch", "critical-perps-v1", 2),
        ("zenodex.perps", "liquidate", "critical-perps-v1", 1),
        ("zenodex.routing", "protected_swap", "critical-routing-v1", 4),
        ("zenodex.trigger", "execute", "critical-trigger-v1", 2),
        ("zenodex.settlement", "critical_settlement", critical_settlement_profile_id(), 1),
    ]
    for consumer_module, action_kind, profile_id, max_window in surfaces:
        surface_auth = replace(
            authorization,
            consumer_module=consumer_module,
            action_kind=action_kind,
            profile_id=profile_id,
            expires_at_epoch=authorization.observed_epoch + max_window,
        )
        surface_runtime = replace(
            runtime,
            consumer_module=consumer_module,
            action_kind=action_kind,
            profile_id=profile_id,
        )

        result = check_critical_consumer_authorization(
            authorization_bundle(asdict(surface_auth)),
            consumer_module=consumer_module,
            action_kind=action_kind,
            action_id=surface_runtime.action_id,
            action_facts_hash=surface_runtime.action_facts_hash,
            pre_state_hash=surface_runtime.pre_state_hash,
            query_id=surface_runtime.query_id,
            runtime_value_e8=surface_runtime.runtime_value_e8,
            now_epoch=surface_runtime.now_epoch,
        )

        assert result["typed_ok"] is True
        assert result["receipt_graph_ok"] is True
        assert result["critical_consumer_profile"] == profile_id


def test_critical_consumer_requires_terminal_receipt_graph() -> None:
    authorization, runtime = _valid_pair()

    result = check_critical_consumer_authorization(
        asdict(authorization),
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id=runtime.action_id,
        action_facts_hash=runtime.action_facts_hash,
        pre_state_hash=runtime.pre_state_hash,
        query_id=runtime.query_id,
        runtime_value_e8=runtime.runtime_value_e8,
        now_epoch=runtime.now_epoch,
    )

    assert result["typed_ok"] is False
    assert result["receipt_graph_ok"] is False
    assert "receipt_graph required" in result["receipt_graph_errors"]


def test_critical_consumer_rejects_bool_runtime_fields() -> None:
    authorization, runtime = _valid_pair()
    authorization = replace(
        authorization,
        value_e8=1,
        observed_epoch=0,
        expires_at_epoch=1,
        value_hash=oracle_value_hash(
            query_id=authorization.query_id,
            value_e8=1,
            observed_epoch=0,
        ),
    )

    result = check_critical_consumer_authorization(
        authorization_bundle(asdict(authorization)),
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id=runtime.action_id,
        action_facts_hash=runtime.action_facts_hash,
        pre_state_hash=runtime.pre_state_hash,
        query_id=runtime.query_id,
        runtime_value_e8=True,
        now_epoch=True,
    )

    assert result["typed_ok"] is False
    assert "runtime_value_e8 must be an int" in result["typed_errors"]
    assert "now_epoch must be an int" in result["typed_errors"]


def test_critical_consumer_rejects_bool_runtime_notional_without_envelope() -> None:
    authorization, runtime = _valid_pair()

    result = check_critical_consumer_authorization(
        authorization_bundle(asdict(authorization)),
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id=runtime.action_id,
        action_facts_hash=runtime.action_facts_hash,
        pre_state_hash=runtime.pre_state_hash,
        query_id=runtime.query_id,
        runtime_value_e8=runtime.runtime_value_e8,
        now_epoch=runtime.now_epoch,
        runtime_notional_value_e8=True,
    )

    assert result["typed_ok"] is False
    assert "runtime_notional_value_e8 must be an int when present" in result["typed_errors"]


def test_critical_consumer_rejects_terminal_graph_value_mismatch() -> None:
    authorization, runtime = _valid_pair()
    bundle = authorization_bundle(asdict(authorization))
    bundle["receipt_graph"]["value_e8"] = int(authorization.value_e8) + 1

    result = check_critical_consumer_authorization(
        bundle,
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id=runtime.action_id,
        action_facts_hash=runtime.action_facts_hash,
        pre_state_hash=runtime.pre_state_hash,
        query_id=runtime.query_id,
        runtime_value_e8=runtime.runtime_value_e8,
        now_epoch=runtime.now_epoch,
    )

    assert result["typed_ok"] is False
    assert result["receipt_graph_ok"] is False
    assert "receipt_graph value_e8 does not match authorization" in result["receipt_graph_errors"]


def test_critical_consumer_rejects_coerced_terminal_graph_active_leaf() -> None:
    authorization, runtime = _valid_pair()
    bundle = authorization_bundle(asdict(authorization))
    bundle["receipt_graph"]["report_leaf_commitments"][0]["active"] = "yes"
    _refresh_terminal_graph_roots(bundle)

    result = check_critical_consumer_authorization(
        bundle,
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id=runtime.action_id,
        action_facts_hash=runtime.action_facts_hash,
        pre_state_hash=runtime.pre_state_hash,
        query_id=runtime.query_id,
        runtime_value_e8=runtime.runtime_value_e8,
        now_epoch=runtime.now_epoch,
    )

    assert result["typed_ok"] is False
    assert result["receipt_graph_ok"] is False
    assert any(
        error.endswith("active must be true")
        for error in result["receipt_graph_errors"]
    )


def test_critical_consumer_rejects_terminal_graph_fake_control_group_diversity() -> None:
    authorization, runtime = _valid_pair()
    bundle = authorization_bundle(asdict(authorization))
    for leaf in bundle["receipt_graph"]["report_leaf_commitments"]:
        leaf["control_group_id"] = "operator:shared-control"
    _refresh_terminal_graph_roots(bundle)

    result = check_critical_consumer_authorization(
        bundle,
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id=runtime.action_id,
        action_facts_hash=runtime.action_facts_hash,
        pre_state_hash=runtime.pre_state_hash,
        query_id=runtime.query_id,
        runtime_value_e8=runtime.runtime_value_e8,
        now_epoch=runtime.now_epoch,
    )

    assert result["typed_ok"] is False
    assert result["receipt_graph_ok"] is False
    assert (
        "receipt_graph reporter_control_group_count does not match distinct report leaf control groups"
        in result["receipt_graph_errors"]
    )
    assert "receipt_graph distinct control groups below min_reporters" in result["receipt_graph_errors"]
