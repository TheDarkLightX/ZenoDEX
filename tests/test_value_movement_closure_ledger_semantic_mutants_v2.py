from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest

from tools import value_movement_closure_ledger_v2 as ledger

ROOT = Path(__file__).resolve().parents[1]


def _sources() -> dict[str, bytes]:
    return {path: (ROOT / path).read_bytes() for path in ledger.SOURCE_PATHS_V2}


def _artifact() -> dict[str, object]:
    return ledger.build_ledger_artifact_from_sources_v2("a" * 40, _sources())


def _reject_artifact(mutant: dict[str, object], code: str) -> None:
    with pytest.raises(ledger.ValueMovementClosureLedgerRejectV2) as captured:
        ledger.validate_ledger_artifact_v2(mutant)
    assert captured.value.code == code


def _replace_json_source(sources: dict[str, bytes], path: str, mutate: object) -> dict[str, bytes]:
    value = json.loads(sources[path])
    assert type(value) is dict
    mutate(value)
    sources[path] = ledger.canonical_json_bytes_v2(value)
    return sources


def test_stale_subject_and_gate_promotion_mutants_reject() -> None:
    mutant = _artifact()
    mutant["implementation_subject"] = "b" * 40
    _reject_artifact(mutant, "ADMITTED_LINEAGE")

    mutant = _artifact()
    gates = mutant["current_gate_rows"]
    assert type(gates) is list
    gates[0]["closed"] = True
    gates[0]["status"] = "PASS"
    _reject_artifact(mutant, "CURRENT_GATE_PROMOTION")


def test_authority_and_historical_laundering_mutants_reject() -> None:
    mutant = _artifact()
    authority = mutant["authority"]
    assert type(authority) is dict
    authority["production"] = "GLOBAL_EPOCH"
    _reject_artifact(mutant, "AUTHORITY_DRIFT")

    mutant = _artifact()
    donors = mutant["historical_donor_rows"]
    assert type(donors) is list
    donors[0]["disposition"] = "CURRENT_EVIDENCE"
    _reject_artifact(mutant, "HISTORICAL_DISPOSITION")


def test_dependency_and_manifest_denominator_mutants_reject() -> None:
    mutant = _artifact()
    dependencies = mutant["dependency_rows"]
    assert type(dependencies) is list
    dependencies.pop()
    _reject_artifact(mutant, "DEPENDENCY_DENOMINATOR")

    mutant = _artifact()
    manifest = mutant["source_manifest"]
    assert type(manifest) is list
    manifest[0]["sha256"] = "0" * 64
    _reject_artifact(mutant, "SOURCE_MANIFEST_SHAPE")


def test_duplicate_json_key_and_noncanonical_bytes_reject() -> None:
    with pytest.raises(ledger.ValueMovementClosureLedgerRejectV2) as captured:
        ledger.decode_json_object_v2(b'{"schema":"a","schema":"b"}', "mutant")
    assert captured.value.code == "JSON_DUPLICATE_KEY"
    encoded = ledger.canonical_json_bytes_v2(_artifact())
    assert encoded == ledger.canonical_json_bytes_v2(
        ledger.decode_json_object_v2(encoded, "ledger")
    )


def test_plan_and_historical_subject_source_mutants_reject() -> None:
    sources = _sources()

    def mutate_plan(value: dict[str, object]) -> None:
        verdict = value["baseline_verdict"]
        assert type(verdict) is dict
        verdict["current_ledger_status"] = "CURRENT"

    with pytest.raises(ledger.ValueMovementClosureLedgerRejectV2) as captured:
        ledger.build_ledger_artifact_from_sources_v2(
            "a" * 40,
            _replace_json_source(sources, ledger.PLAN_PATH_V2, mutate_plan),
        )
    assert captured.value.code == "ACTIVE_PLAN_SUBJECT"

    sources = _sources()

    def mutate_historical(value: dict[str, object]) -> None:
        subject = value["subject"]
        assert type(subject) is dict
        subject["commit"] = "0" * 40

    with pytest.raises(ledger.ValueMovementClosureLedgerRejectV2) as captured:
        ledger.build_ledger_artifact_from_sources_v2(
            "a" * 40,
            _replace_json_source(
                sources,
                ledger.HISTORICAL_LEDGER_PATH_V2,
                mutate_historical,
            ),
        )
    assert captured.value.code == "HISTORICAL_BINDING"


def test_dependency_promotion_source_mutant_rejects() -> None:
    sources = _sources()
    path = "docs/research/ZENODEX_OPERATOR_SURFACE_REGISTRY_V2.json"

    def mutate(value: dict[str, object]) -> None:
        value["vm_gates_closed"] = ["VM-01"]

    with pytest.raises(ledger.ValueMovementClosureLedgerRejectV2) as captured:
        ledger.build_ledger_artifact_from_sources_v2(
            "a" * 40,
            _replace_json_source(sources, path, mutate),
        )
    assert captured.value.code == "DEPENDENCY_PROMOTION"


def test_claim_ceiling_mutant_rejects() -> None:
    mutant = deepcopy(_artifact())
    nonclaims = mutant["nonclaims"]
    assert type(nonclaims) is list
    nonclaims.append("production ready")
    _reject_artifact(mutant, "CLAIM_CEILING")
