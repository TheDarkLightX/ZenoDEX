from __future__ import annotations

from src.fire.verifier.cert_v1 import (
    FireCertEnv,
    FireCertNode,
    FireIntervalCertificate,
    verify_interval_certificate,
)


def _malformed_node(**fields: object) -> FireCertNode:
    node = object.__new__(FireCertNode)
    defaults = {
        "rule": "const",
        "lower": 0,
        "upper": 0,
        "value": None,
        "name": None,
        "children": (),
    }
    defaults.update(fields)
    for name, value in defaults.items():
        object.__setattr__(node, name, value)
    return node


def test_verify_interval_certificate_rejects_const_node_missing_value_without_assert() -> None:
    certificate = FireIntervalCertificate(root=_malformed_node(rule="const", value=None))

    ok, err, interval = verify_interval_certificate(certificate, FireCertEnv({}, {}))

    assert ok is False
    assert err == "root:const node missing value"
    assert interval is None


def test_verify_interval_certificate_rejects_exact_param_missing_name_without_assert() -> None:
    certificate = FireIntervalCertificate(root=_malformed_node(rule="exact_param", name=None))

    ok, err, interval = verify_interval_certificate(certificate, FireCertEnv({}, {}))

    assert ok is False
    assert err == "root:exact_param node missing name"
    assert interval is None


def test_verify_interval_certificate_rejects_source_bound_missing_name_without_assert() -> None:
    certificate = FireIntervalCertificate(root=_malformed_node(rule="source_bound", name=None))

    ok, err, interval = verify_interval_certificate(certificate, FireCertEnv({}, {}))

    assert ok is False
    assert err == "root:source_bound node missing name"
    assert interval is None
