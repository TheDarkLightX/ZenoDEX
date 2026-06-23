from __future__ import annotations

from pathlib import Path
from typing import cast

from tools.stateful_feedback import (
    DangerousSurface,
    Mutation,
    build_exploit_proximity_report,
    build_guard_attribution_report,
    build_introspection_report,
    build_surface_suggestions,
    build_weird_machine_atlas,
    explore_bounded_frontier,
    load_dangerous_surface_manifest,
)


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_load_dangerous_surface_manifest_reads_current_schema() -> None:
    surfaces = load_dangerous_surface_manifest(MANIFEST_PATH)
    ids = {surface.id for surface in surfaces}
    assert "nonce_replay_guard" in ids
    assert "route_canonicalization_boundary" in ids
    assert "settlement_attestation_policy_boundary" in ids



def test_explore_bounded_frontier_is_deterministic_and_hits_targets() -> None:
    surfaces = (
        DangerousSurface(
            id="danger_surface",
            machine_family="demo",
            invariant_boundary="demo boundary",
            action_grammar="seed -> mutate -> reject",
            harnesses=("demo:harness",),
            trace_tokens=("danger.py",),
            outcome_tokens=("danger",),
            waypoint_tags=("demo",),
            witness_ids=(),
        ),
    )

    def _to_int(payload: object) -> int:
        assert isinstance(payload, int)
        return payload

    def trace(payload: object) -> tuple[str, str, int, tuple[str, ...]]:
        value = _to_int(payload)
        if value == 0:
            return ("ok", "path-ok", 1, ("seed.py:1",))
        if value == 1:
            return ("reject:danger", "path-danger", 2, ("danger.py:7",))
        return (f"ok:{value}", f"path-{value}", 1, ("other.py:1",))

    report_left = explore_bounded_frontier(
        harness_id="demo:harness",
        seed=0,
        mutations=(Mutation(name="inc", apply=lambda payload: _to_int(payload) + 1),),
        trace_fn=trace,
        expandable=lambda payload: _to_int(payload) < 1,
        max_depth=1,
        max_frontier=8,
        feedback_mode="stateful",
        dangerous_surfaces=surfaces,
        target_id="danger_surface",
    )
    report_right = explore_bounded_frontier(
        harness_id="demo:harness",
        seed=0,
        mutations=(Mutation(name="inc", apply=lambda payload: _to_int(payload) + 1),),
        trace_fn=trace,
        expandable=lambda payload: _to_int(payload) < 1,
        max_depth=1,
        max_frontier=8,
        feedback_mode="stateful",
        dangerous_surfaces=surfaces,
        target_id="danger_surface",
    )
    assert report_left == report_right
    assert report_left.reached_target_ids == ("danger_surface",)
    assert {case.outcome_label for case in report_left.cases} == {"ok", "reject:danger"}


def test_explore_bounded_frontier_uses_semantic_state_and_action_summaries() -> None:
    def _to_int(payload: object) -> int:
        assert isinstance(payload, int)
        return payload

    def trace(payload: object) -> tuple[str, str, int]:
        value = _to_int(payload)
        return (f"ok:{value}", f"path-{value}", 1)

    def semantic_state(
        payload: object,
        outcome_label: str,
        _path_id: str,
        _line_trace: tuple[str, ...],
        _target_hits: tuple[str, ...],
        _waypoint_tags: tuple[str, ...],
        _harness_id: str,
    ) -> object:
        value = _to_int(payload)
        return {
            "bucket": "even" if value % 2 == 0 else "odd",
            "outcome": outcome_label.split(":", 1)[0],
        }

    def action_summary(prev_payload: object, next_payload: object, mutation_name: str) -> object:
        return {
            "kind": mutation_name,
            "delta": _to_int(next_payload) - _to_int(prev_payload),
        }

    report = explore_bounded_frontier(
        harness_id="demo:semantic",
        seed=0,
        mutations=(
            Mutation(name="plus_one", apply=lambda payload: _to_int(payload) + 1),
            Mutation(name="plus_three", apply=lambda payload: _to_int(payload) + 3),
        ),
        trace_fn=trace,
        expandable=lambda payload: _to_int(payload) == 0,
        max_depth=1,
        max_frontier=8,
        feedback_mode="stateful",
        semantic_state_fn=semantic_state,
        action_summary_fn=action_summary,
    )
    assert report.unique_state_count == 2
    assert report.unique_transition_count == 3
    odd_cases = [case for case in report.cases if case.state_summary == {"bucket": "odd", "outcome": "ok"}]
    assert len(odd_cases) == 2
    assert {cast(dict[str, int], case.action_summary)["delta"] for case in odd_cases} == {1, 3}


def test_introspection_and_weird_machine_atlas_classify_surfaces() -> None:
    surfaces = (
        DangerousSurface(
            id="witnessed_surface",
            machine_family="family.a",
            invariant_boundary="boundary a",
            action_grammar="a",
            harnesses=("h1",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("tag-a",),
            witness_ids=("w1",),
        ),
        DangerousSurface(
            id="reached_surface",
            machine_family="family.b",
            invariant_boundary="boundary b",
            action_grammar="b",
            harnesses=("h2",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("tag-b",),
            witness_ids=(),
        ),
        DangerousSurface(
            id="harnessed_surface",
            machine_family="family.c",
            invariant_boundary="boundary c",
            action_grammar="c",
            harnesses=("h3",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("tag-c",),
            witness_ids=(),
        ),
        DangerousSurface(
            id="unharnessed_surface",
            machine_family="family.d",
            invariant_boundary="boundary d",
            action_grammar="d",
            harnesses=("h4",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("tag-d",),
            witness_ids=(),
        ),
    )
    report_payloads = [
        {
            "reports": [
                {"harness_id": "h1", "reached_target_ids": ["witnessed_surface"], "cases": []},
                {"harness_id": "h2", "reached_target_ids": ["reached_surface"], "cases": []},
                {"harness_id": "h3", "reached_target_ids": [], "cases": []},
            ]
        }
    ]
    shared_witness_index = {"witnesses": [{"id": "w1", "derivation": "seed->witness"}]}

    introspection = build_introspection_report(
        dangerous_surfaces=surfaces,
        shared_witness_index=shared_witness_index,
        report_payloads=report_payloads,
    )
    by_surface = {row["surface_id"]: row["status"] for row in introspection["surfaces"]}
    assert by_surface == {
        "witnessed_surface": "witnessed",
        "reached_surface": "reached_no_witness",
        "harnessed_surface": "harnessed_unreached",
        "unharnessed_surface": "unharnessed",
    }
    assert introspection["status_counts"] == {
        "unharnessed": 1,
        "harnessed_unreached": 1,
        "reached_no_witness": 1,
        "witnessed": 1,
    }
    assert introspection["target_count"] == 4
    assert introspection["report_count"] == 3
    assert introspection["witness_count"] == 1
    assert introspection["atlas_status"] == "partial"

    atlas = build_weird_machine_atlas(
        dangerous_surfaces=surfaces,
        shared_witness_index=shared_witness_index,
        report_payloads=[
            {
                "reports": [
                    {
                        "harness_id": "h2",
                        "reached_target_ids": ["reached_surface"],
                        "cases": [
                            {
                                "mutation": "valid_seed->flip",
                                "outcome_label": "reject:route mismatch",
                                "target_hits": ["reached_surface"],
                                "state_summary": {"bucket": "bad"},
                                "action_summary": {"kind": "flip"},
                            }
                        ],
                    }
                ]
            }
        ],
    )
    atlas_entries = {entry["surface_id"]: entry for entry in atlas["entries"]}
    assert atlas_entries["witnessed_surface"]["witness_status"] == "witnessed"
    assert atlas_entries["reached_surface"]["witness_status"] == "reached"
    assert atlas_entries["reached_surface"]["sample_outcomes"] == ["reject:route mismatch"]
    assert atlas_entries["reached_surface"]["sample_state_summaries"] == [{"bucket": "bad"}]
    assert atlas_entries["reached_surface"]["sample_action_summaries"] == [{"kind": "flip"}]
    assert atlas["witnessed_count"] == 1
    assert atlas["atlas_status"] == "partial"


def test_build_surface_suggestions_mines_cross_surface_compositions() -> None:
    surfaces = (
        DangerousSurface(
            id="transport",
            machine_family="receipt/transport",
            invariant_boundary="transport boundary",
            action_grammar="receipt -> hash check -> reject",
            harnesses=("h1",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("receipt", "transport"),
            witness_ids=("w-transport",),
        ),
        DangerousSurface(
            id="certificate",
            machine_family="receipt/certificate",
            invariant_boundary="certificate boundary",
            action_grammar="receipt -> certificate bind -> reject",
            harnesses=("h1",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("receipt", "certificate"),
            witness_ids=("w-certificate",),
        ),
        DangerousSurface(
            id="stale",
            machine_family="receipt/stale",
            invariant_boundary="stale boundary",
            action_grammar="receipt -> drift -> reject",
            harnesses=("h1",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("receipt", "stale"),
            witness_ids=(),
        ),
    )
    report_payloads = [
        {
            "reports": [
                {
                    "harness_id": "h1",
                    "reached_target_ids": ["transport", "certificate", "stale"],
                    "cases": [
                        {
                            "outcome_label": "reject:step=2:certificate mismatch",
                            "target_hits": ["transport", "certificate", "stale"],
                            "action_summary": {"kind": "rehash"},
                            "state_summary": {"transport_relation": "hash_match", "certificate_relation": "amount_out_mismatch"},
                        }
                    ],
                }
            ]
        }
    ]
    suggestions = build_surface_suggestions(
        dangerous_surfaces=surfaces,
        shared_witness_index={"witnesses": [{"id": "w-transport"}, {"id": "w-certificate"}]},
        report_payloads=report_payloads,
    )
    assert suggestions["suggestion_count"] == 1
    row = suggestions["suggestions"][0]
    assert row["kind"] == "cross_surface_composition"
    assert row["actionability"] == "already_in_harness"
    assert row["surface_ids"] == ["certificate", "stale", "transport"]
    assert row["confidence"] == "high"
    assert row["multi_hit_case_count"] == 1
    assert row["report_support_count"] == 1
    assert row["witness_ids"] == ["w-certificate", "w-transport"]


def test_build_guard_attribution_report_groups_witnesses_by_guard_family() -> None:
    surfaces = (
        DangerousSurface(
            id="transport",
            machine_family="receipt/transport",
            invariant_boundary="transport boundary",
            action_grammar="receipt -> hash check -> reject",
            harnesses=("h1",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("receipt", "transport"),
            witness_ids=("w-transport",),
        ),
        DangerousSurface(
            id="signature",
            machine_family="ops/signature",
            invariant_boundary="signature boundary",
            action_grammar="ops -> signature verify -> reject",
            harnesses=("h2",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("ops", "signature"),
            witness_ids=("w-signature",),
        ),
    )
    report = build_guard_attribution_report(
        dangerous_surfaces=surfaces,
        shared_witness_index={
            "witnesses": [
                {
                    "id": "w-transport",
                    "derivation": "seed->drop_hash",
                    "outcome_label": "reject:missing_receipt_hash",
                    "path_length": 1,
                    "witness_out": "a.json",
                },
                {
                    "id": "w-signature",
                    "derivation": "seed->dup",
                    "outcome_label": "reject:step=1:settlement spot price attestation signature invalid",
                    "path_length": 1,
                    "witness_out": "b.json",
                },
            ]
        },
    )
    assert report["witness_count"] == 2
    assert report["guard_family_count"] == 2
    families = {row["guard_family"]: row for row in report["guards"]}
    assert families["receipt_transport_guard"]["witness_ids"] == ["w-transport"]
    assert families["signature_guard"]["witness_ids"] == ["w-signature"]
    witnesses = {row["witness_id"]: row for row in report["witnesses"]}
    assert witnesses["w-transport"]["guard_reason"] == "missing_receipt_hash"
    assert witnesses["w-signature"]["guard_family"] == "signature_guard"



def test_build_exploit_proximity_report_ranks_stateful_settlement_above_transport() -> None:
    surfaces = (
        DangerousSurface(
            id="stale_settlement_boundary",
            machine_family="settlement/staleness",
            invariant_boundary="settlements must remain bound to the current state",
            action_grammar="settlement -> warmup -> stale replay -> reject",
            harnesses=("h1",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("settlement", "stale"),
            witness_ids=("w-settlement",),
        ),
        DangerousSurface(
            id="quote_receipt_transport_boundary",
            machine_family="receipt/transport",
            invariant_boundary="receipt hashes must bind the transport envelope",
            action_grammar="receipt -> drop hash -> reject",
            harnesses=("h2",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("receipt", "transport"),
            witness_ids=("w-transport",),
        ),
    )
    report = build_exploit_proximity_report(
        dangerous_surfaces=surfaces,
        shared_witness_index={
            "witnesses": [
                {
                    "id": "w-settlement",
                    "derivation": "SettlementSeq->WarmupThenStaleProvidedAbWithDeadTail",
                    "outcome_label": "reject:step=1:settlement mismatch",
                    "minimized_size": 2048,
                    "witness_out": "settlement.json",
                },
                {
                    "id": "w-transport",
                    "derivation": "QuoteReceipt->ExactOut ; ReceiptHash->MissingWithDeadBlob",
                    "outcome_label": "reject:missing_receipt_hash",
                    "minimized_size": 64,
                    "witness_out": "transport.json",
                },
            ]
        },
    )
    assert report["witness_count"] == 2
    assert report["hotspot_count"] == 2
    top = report["top_witnesses"][0]
    assert top["witness_id"] == "w-settlement"
    assert top["severity_band"] in {"high", "critical"}
    assert top["flags"]["state_carryover"] is True
    by_id = {row["witness_id"]: row for row in report["top_witnesses"]}
    assert by_id["w-settlement"]["proximity_score"] > by_id["w-transport"]["proximity_score"]


def test_build_exploit_proximity_report_marks_repair_after_tamper() -> None:
    surfaces = (
        DangerousSurface(
            id="quote_receipt_certificate_boundary",
            machine_family="route-certificate/receipt-binding",
            invariant_boundary="route certificates must remain bound to the quoted body",
            action_grammar="receipt -> tamper -> rehash -> reject",
            harnesses=("h1",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("receipt", "certificate"),
            witness_ids=("w-certificate",),
        ),
    )
    report = build_exploit_proximity_report(
        dangerous_surfaces=surfaces,
        shared_witness_index={
            "witnesses": [
                {
                    "id": "w-certificate",
                    "derivation": "tamper_then_rehash",
                    "outcome_label": "reject:step=1:canonical_route_certificate_amount_out_mismatch",
                    "minimized_size": 512,
                    "witness_out": "certificate.json",
                }
            ]
        },
    )
    row = report["top_witnesses"][0]
    assert row["flags"]["repair_after_tamper"] is True
    assert row["flags"]["post_verification_binding"] is True
    assert row["guard_family"] == "route_certificate_binding_guard"



def test_build_exploit_proximity_report_dedupes_witness_ids_across_campaigns() -> None:
    surfaces = (
        DangerousSurface(
            id="quote_receipt_certificate_boundary",
            machine_family="route-certificate/receipt-binding",
            invariant_boundary="route certificates must remain bound to the quoted body",
            action_grammar="receipt -> tamper -> rehash -> reject",
            harnesses=("h1",),
            trace_tokens=(),
            outcome_tokens=(),
            waypoint_tags=("receipt", "certificate"),
            witness_ids=("w-certificate",),
        ),
    )
    report = build_exploit_proximity_report(
        dangerous_surfaces=surfaces,
        shared_witness_index={
            "witnesses": [
                {
                    "id": "w-certificate",
                    "campaign_dir": "internal/fuzz_campaigns/deep/20260408T010000Z_a",
                    "derivation": "tamper_then_rehash",
                    "outcome_label": "reject:step=1:canonical_route_certificate_amount_out_mismatch",
                    "minimized_size": 768,
                    "witness_out": "a.json",
                },
                {
                    "id": "w-certificate",
                    "campaign_dir": "internal/fuzz_campaigns/deep/20260408T020000Z_b",
                    "derivation": "tamper_then_rehash",
                    "outcome_label": "reject:step=1:canonical_route_certificate_amount_out_mismatch",
                    "minimized_size": 512,
                    "witness_out": "b.json",
                },
            ]
        },
    )
    assert report["witness_count"] == 1
    assert report["top_witnesses"][0]["campaign_dir"] == "internal/fuzz_campaigns/deep/20260408T020000Z_b"
