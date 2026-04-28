from __future__ import annotations

from dataclasses import replace

import pytest

from src.fire.verifier.cert_v1 import (
    FireCertEnv,
    FireCertNode,
    FireInstanceGateClaims,
    FireInterval,
    FireIntervalCertificate,
    binary_node,
    const_node,
    exact_param_node,
    fire_cert_sha256,
    source_bound_node,
    verify_instance_gate_claims,
    verify_interval_certificate,
)


def test_fire_interval_certificate_round_trip_and_hash() -> None:
    left = exact_param_node("x", 7)
    right = const_node(3)
    certificate = FireIntervalCertificate(root=binary_node("sub", left, right))

    payload = certificate.to_dict()
    restored = FireIntervalCertificate.from_dict(payload)

    assert restored == certificate
    assert fire_cert_sha256(restored) == fire_cert_sha256(certificate)


def test_fire_interval_certificate_round_trip_preserves_instance_gate_claims() -> None:
    certificate = FireIntervalCertificate(
        root=const_node(0),
        instance_gate_claims=FireInstanceGateClaims(
            param_ok="implemented",
            authorization_ok="implemented",
            nonce_ok="implemented",
            maturity_ok="implemented",
            window_ok="implemented",
        ),
    )

    restored = FireIntervalCertificate.from_dict(certificate.to_dict())

    assert restored == certificate
    assert restored.instance_gate_claims is not None
    assert restored.instance_gate_claims.param_ok == "implemented"


def test_verify_interval_certificate_accepts_generic_burn_style_tree() -> None:
    burn = source_bound_node("burn_final", FireInterval(lower=0, upper=9))
    strike = exact_param_node("strike_index", 4)
    cap = exact_param_node("cap_index", 3)
    n = exact_param_node("n_notional", 10)
    zero = const_node(0)

    spread = binary_node("sub", burn, strike)
    positive_spread = binary_node("max", spread, zero)
    capped_spread = binary_node("min", positive_spread, cap)
    payoff = binary_node("mul", n, capped_spread)
    certificate = FireIntervalCertificate(root=payoff)

    ok, err, interval = verify_interval_certificate(
        certificate,
        FireCertEnv(
            exact_values={"n_notional": 10, "strike_index": 4, "cap_index": 3},
            source_bounds={"burn_final": FireInterval(lower=0, upper=9)},
        ),
    )

    assert ok is True
    assert err is None
    assert interval == FireInterval(lower=0, upper=30)


def test_verify_interval_certificate_rejects_tampered_claim() -> None:
    certificate = FireIntervalCertificate(root=binary_node("add", exact_param_node("x", 2), const_node(5)))
    bad_certificate = replace(certificate, root=replace(certificate.root, upper=8))

    ok, err, interval = verify_interval_certificate(
        bad_certificate,
        FireCertEnv(exact_values={"x": 2}, source_bounds={}),
    )

    assert ok is False
    assert interval is None
    assert err is not None
    assert "claimed interval" in err


def test_verify_interval_certificate_rejects_missing_exact_binding() -> None:
    certificate = FireIntervalCertificate(root=binary_node("add", exact_param_node("x", 2), const_node(5)))

    ok, err, interval = verify_interval_certificate(
        certificate,
        FireCertEnv(exact_values={}, source_bounds={}),
    )

    assert ok is False
    assert interval is None
    assert err == "root.0:'missing exact value: x'"


def test_verify_interval_certificate_rejects_missing_source_binding() -> None:
    certificate = FireIntervalCertificate(root=binary_node("sub", source_bound_node("burn_final", FireInterval(0, 9)), const_node(4)))

    ok, err, interval = verify_interval_certificate(
        certificate,
        FireCertEnv(exact_values={}, source_bounds={}),
    )

    assert ok is False
    assert interval is None
    assert err == "root.0:'missing source bound: burn_final'"


def test_verify_interval_certificate_rejects_wrong_source_bound_type() -> None:
    certificate = FireIntervalCertificate(root=source_bound_node("burn_final", FireInterval(0, 9)))

    ok, err, interval = verify_interval_certificate(
        certificate,
        FireCertEnv(exact_values={}, source_bounds={"burn_final": "bad"}),  # type: ignore[dict-item]
    )

    assert ok is False
    assert interval is None
    assert err == "root:source bound burn_final must be a FireInterval"


def test_fire_interval_certificate_from_dict_rejects_bad_children_shape() -> None:
    with pytest.raises(TypeError, match="children must be a sequence"):
        FireIntervalCertificate.from_dict(
            {
                "schema": "zenodex/fire-interval-certificate/v1",
                "root": {
                    "rule": "add",
                    "lower": 0,
                    "upper": 1,
                    "children": "bad",
                },
            }
        )


def test_fire_interval_certificate_from_dict_rejects_non_string_schema() -> None:
    with pytest.raises(TypeError, match="schema must be a non-empty string"):
        FireIntervalCertificate.from_dict({"schema": 1, "root": const_node(0).to_dict()})


def test_fire_cert_node_from_dict_rejects_non_string_rule() -> None:
    with pytest.raises(TypeError, match="rule must be a non-empty string"):
        FireCertNode.from_dict({"rule": 1, "lower": 0, "upper": 0, "children": []})


def test_fire_cert_node_from_dict_rejects_non_string_name() -> None:
    with pytest.raises(TypeError, match="name must be a non-empty string"):
        FireCertNode.from_dict({"rule": "exact_param", "lower": 0, "upper": 0, "name": True, "children": []})


def test_fire_cert_node_rejects_wrong_child_count() -> None:
    with pytest.raises(ValueError, match="add node requires two children"):
        FireCertNode(rule="add", lower=0, upper=1, children=(const_node(0),))


def test_verify_instance_gate_claims_rejects_mismatch() -> None:
    certificate = FireIntervalCertificate(
        root=const_node(0),
        instance_gate_claims=FireInstanceGateClaims(
            param_ok="implemented",
            authorization_ok="implemented",
            nonce_ok="implemented",
            maturity_ok="implemented",
            window_ok="implemented",
        ),
    )

    ok, err, claims = verify_instance_gate_claims(
        certificate,
        expected=FireInstanceGateClaims(
            param_ok="proved",
            authorization_ok="implemented",
            nonce_ok="implemented",
            maturity_ok="implemented",
            window_ok="implemented",
        ),
        require_present=True,
    )

    assert ok is False
    assert err == "instance_gate_claims_mismatch"
    assert claims == certificate.instance_gate_claims
