from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Callable

import pytest

from tools import check_production_readiness_architecture_tournament_v1 as checker


def _document() -> dict[str, Any]:
    return json.loads(checker.DEFAULT_ARTIFACT.read_text(encoding="utf-8"))


def _candidate(document: dict[str, Any], candidate_id: str) -> dict[str, Any]:
    return next(candidate for candidate in document["candidates"] if candidate["id"] == candidate_id)


def _leader(document: dict[str, Any]) -> dict[str, Any]:
    return _candidate(document, "TYPED_SETTLEMENT_MICROKERNEL_V2")


def _row(rows: list[dict[str, Any]], row_id: str) -> dict[str, Any]:
    return next(row for row in rows if row["id"] == row_id)


def _mutate_multiple_writers(document: dict[str, Any]) -> None:
    domain = _row(_leader(document)["state_domains"], "PERPS")
    domain["durable_writers"] = ["PERPS_MODULE", "ZENO_LEDGER"]


def _mutate_foreign_state_owner(document: dict[str, Any]) -> None:
    domain = _row(_leader(document)["state_domains"], "PERPS")
    domain["semantic_owners"] = ["PERPS_MODULE", "ZUSD_MODULE"]


def _mutate_untyped_port(document: dict[str, Any]) -> None:
    port = _row(_leader(document)["ports"], "ledger_intent")
    port["request_type"] = "UNTYPED_EVENT"
    port["closed_variants"] = False


def _mutate_dependency_cycle(document: dict[str, Any]) -> None:
    component = _row(_leader(document)["components"], "SETTLEMENT_ABI")
    component["depends_on"] = ["SETTLEMENT_KERNEL"]


def _mutate_order(document: dict[str, Any]) -> None:
    _leader(document)["composition"]["order_rule"] = "ARRIVAL_ORDER"


def _mutate_partial_commit(document: dict[str, Any]) -> None:
    _leader(document)["composition"]["partial_commit_possible"] = True


def _mutate_reject_effect(document: dict[str, Any]) -> None:
    _leader(document)["composition"]["reject_emits_effects"] = True


def _mutate_caller_witness(document: dict[str, Any]) -> None:
    port = _row(_leader(document)["ports"], "policy_verifier")
    port["caller_constructible_authority"] = True


def _mutate_verifier_mismatch(document: dict[str, Any]) -> None:
    _leader(document)["composition"]["verifier_mismatch_policy"] = "PREFER_TAU"


def _mutate_no_drain(document: dict[str, Any]) -> None:
    lifecycle = _leader(document)["composition"]["release_lifecycle"]
    lifecycle.remove("DRAIN_ONLY")


def _mutate_replay_scope(document: dict[str, Any]) -> None:
    fields = _leader(document)["composition"]["replay_key_fields"]
    fields.remove("CREATOR_RELEASE")


def _mutate_module_delta(document: dict[str, Any]) -> None:
    _leader(document)["composition"]["value_delta_source"] = "MODULE_DECLARATION"


def _mutate_second_writer_capability(document: dict[str, Any]) -> None:
    capabilities = _leader(document)["composition"]["mounted_writer_capabilities"]
    capabilities.insert(0, "DIRECT_MODULE_WRITE")


def _mutate_zrpf_core(document: dict[str, Any]) -> None:
    _leader(document)["composition"]["zrpf_core_id"] = "DIFFERENT_GUEST_CORE"


MUTANTS: tuple[tuple[str, Callable[[dict[str, Any]], None], str], ...] = (
    ("MULTIPLE_DURABLE_WRITERS", _mutate_multiple_writers, "SOLE_DURABLE_WRITER"),
    ("MODULE_WRITES_FOREIGN_STATE", _mutate_foreign_state_owner, "UNIQUE_STATE_OWNERSHIP"),
    ("UNTYPED_OPEN_EVENT_PORT", _mutate_untyped_port, "TYPED_CLOSED_PORTS"),
    ("CYCLIC_MODULE_DEPENDENCY", _mutate_dependency_cycle, "ACYCLIC_DEPENDENCIES"),
    ("NONDETERMINISTIC_MODULE_ORDER", _mutate_order, "DETERMINISTIC_COMPOSITION_ORDER"),
    ("PARTIAL_CROSS_MODULE_COMMIT", _mutate_partial_commit, "ATOMIC_GLOBAL_RECONCILIATION"),
    ("REJECT_EMITS_EFFECT", _mutate_reject_effect, "REJECT_NO_COMMIT"),
    ("CALLER_CONSTRUCTED_VERIFIED_WITNESS", _mutate_caller_witness, "OPAQUE_VERIFIER_WITNESS"),
    ("VERIFIER_MISMATCH_FAILS_OPEN", _mutate_verifier_mismatch, "VERIFIER_BACKEND_SUBSTITUTION"),
    ("MIGRATION_WITHOUT_DRAIN", _mutate_no_drain, "VERSION_COEXISTENCE_AND_DRAIN"),
    ("REPLAY_SCOPE_OMITS_RELEASE", _mutate_replay_scope, "REPLAY_IDEMPOTENCY"),
    ("DELTA_TRUSTED_FROM_MODULE", _mutate_module_delta, "ATOMIC_GLOBAL_RECONCILIATION"),
    ("SECOND_MOUNTED_WRITER_CAPABILITY", _mutate_second_writer_capability, "NO_BYPASS_MOUNT"),
    ("ZRPF_USES_DIFFERENT_CORE", _mutate_zrpf_core, "DIRECT_ZRPF_CORE_PARITY"),
)


def test_tournament_is_exact_research_only_and_unselected() -> None:
    report = checker.check_artifact()

    assert report["ok"] is True
    assert report["candidate_count"] == 4
    assert report["research_leader_id"] == "TYPED_SETTLEMENT_MICROKERNEL_V2"
    assert report["promotable_candidate_count"] == 0
    assert report["selected_candidate_id"] is None
    assert report["architecture_frozen"] is False
    assert report["production_ready"] is False


def test_research_leader_wins_maximin_before_weighted_score() -> None:
    report = checker.check_artifact()
    candidates = {row["id"]: row for row in report["candidate_reports"]}

    leader = candidates["TYPED_SETTLEMENT_MICROKERNEL_V2"]
    monolith = candidates["GLOBAL_MONOLITH_V2"]
    assert leader["design_gate_pass_count"] == leader["design_gate_count"] == 13
    assert leader["minimum_metric_milli"] == 700
    assert leader["weighted_metric_milli"] == 872
    assert monolith["minimum_metric_milli"] == 350
    assert monolith["weighted_metric_milli"] == 679


@pytest.mark.parametrize(
    ("mutant_id", "mutate", "expected_gate"),
    MUTANTS,
    ids=[mutant_id for mutant_id, _, _ in MUTANTS],
)
def test_named_structural_mutants_fail_closed(
    mutant_id: str,
    mutate: Callable[[dict[str, Any]], None],
    expected_gate: str,
) -> None:
    document = _document()
    mutate(document)

    report = checker.check_document(document)

    assert mutant_id in checker.EXPECTED_MUTANTS
    assert report["ok"] is False
    assert any(expected_gate in error for error in report["errors"])
    assert report["selected_candidate_id"] is None
    assert report["production_ready"] is False


def test_advisory_metric_change_cannot_silently_change_the_leader() -> None:
    document = _document()
    metric = _row(_leader(document)["metrics"], "OPERATIONAL_SIMPLICITY")
    metric["value_milli"] = 100

    report = checker.check_document(document)

    assert report["ok"] is False
    assert report["research_leader_id"] == "GLOBAL_MONOLITH_V2"
    assert any("research leader differs" in error for error in report["errors"])


def test_unverified_candidate_cannot_be_selected_or_frozen() -> None:
    document = _document()
    document["selection"]["selected_candidate_id"] = "TYPED_SETTLEMENT_MICROKERNEL_V2"
    document["architecture_frozen"] = True

    report = checker.check_document(document)

    assert report["ok"] is False
    assert report["promotable_candidate_count"] == 0
    assert any("not promotion eligible" in error for error in report["errors"])


def test_source_pin_tampering_fails_closed() -> None:
    document = _document()
    document["source_pins"][0]["sha256"] = "0" * 64

    report = checker.check_document(document)

    assert report["ok"] is False
    assert any("source pin digest mismatch" in error for error in report["errors"])


def test_candidate_evolution_cycle_fails_closed() -> None:
    document = _document()
    global_candidate = _candidate(document, "GLOBAL_MONOLITH_V2")
    global_candidate["parents"] = ["TYPED_SETTLEMENT_MICROKERNEL_V2"]
    global_candidate["operator"] = "COMPOSE"

    report = checker.check_document(document)

    assert report["ok"] is False
    assert "candidate evolution graph is cyclic" in report["errors"]


def test_mutant_registry_matches_executable_mutations() -> None:
    document = _document()
    declared = {row["id"] for row in document["named_mutants"]}
    executable = {mutant_id for mutant_id, _, _ in MUTANTS}

    assert declared == executable == checker.EXPECTED_MUTANTS


def test_duplicate_json_key_is_rejected(tmp_path: Path) -> None:
    artifact = tmp_path / "duplicate.json"
    artifact.write_text('{"schema":"first","schema":"second"}\n', encoding="utf-8")

    report = checker.check_artifact(artifact)

    assert report["ok"] is False
    assert "duplicate JSON keys" in report["errors"][0]
