from __future__ import annotations

import pytest

from tools.check_claims_registry import CheckError, validate_registry


def _registry_text(*, cmd: str) -> str:
    return f"""
schema: zenodex/claims-registry/v1
meta: {{}}
claims:
  - id: smt:test:drift
    status: supported
    layer: spec
    statement: test claim
    evidence:
      kind: smt
      check:
        - cmd: {cmd}
      files:
        - src/kernels/dex/perp_epoch_isolated_v2.yaml
"""


def test_smt_claim_rejects_command_that_does_not_reference_evidence_file(tmp_path):
    registry = tmp_path / "claims.yaml"
    registry.write_text(_registry_text(cmd="'bash tools/check_deployment_profiles.py'"), encoding="utf-8")

    with pytest.raises(CheckError, match="smt evidence command does not reference evidence file"):
        validate_registry(registry)


def test_smt_claim_allows_script_that_references_evidence_file(tmp_path):
    registry = tmp_path / "claims.yaml"
    registry.write_text(_registry_text(cmd="'bash tools/run_perps_evidence.sh'"), encoding="utf-8")

    validate_registry(registry)
