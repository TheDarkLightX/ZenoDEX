from __future__ import annotations

import pytest

from src.fire.verifier.cert_v1 import FireCertNode, FireIntervalCertificate
from src.fire.verifier.proof_tree_cert_v1 import summarize_fire_interval_certificate


def _malformed_node(**fields: object) -> FireCertNode:
    node = object.__new__(FireCertNode)
    defaults = {
        "rule": "exact_param",
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


def test_summarize_fire_interval_certificate_rejects_missing_exact_param_name_without_assert() -> None:
    certificate = FireIntervalCertificate(root=_malformed_node(rule="exact_param", name=None))

    with pytest.raises(ValueError, match="exact_param runtime certificate node missing name"):
        summarize_fire_interval_certificate(certificate)


def test_summarize_fire_interval_certificate_rejects_missing_source_bound_name_without_assert() -> None:
    certificate = FireIntervalCertificate(root=_malformed_node(rule="source_bound", name=None))

    with pytest.raises(ValueError, match="source_bound runtime certificate node missing name"):
        summarize_fire_interval_certificate(certificate)
