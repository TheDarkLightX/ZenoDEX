"""AAA/RIPR evidence for the O005 source-resolution bijection registry."""

from __future__ import annotations

import hashlib
import json
from copy import deepcopy
from pathlib import Path, PosixPath
from typing import Any, cast

import pytest

import tools.build_m6_o005_semantic_resolutions_v1 as build_shell
import tools.check_m6_o005_semantic_resolutions_v1 as check_shell
import tools.m6_o005_semantic_resolutions_v1 as core

REPO_ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_PATH = REPO_ROOT / build_shell.JSON_OUTPUT
EXPECTED_ARTIFACT_SHA256 = "001ddc29a48275ddae0a93b180ef827b0488b55ea97485810ca0a4a246a48341"

_RESOLUTION_ORACLE = {
    "pending_asset_intent_terminal_coverage": (
        "pending_asset_bearing_intent_terminal_owner",
        "GLOBAL_OBLIGATION",
        "global_obligation:pending_asset_intent_terminal_coverage",
        None,
        (),
    ),
    "perps_request_terminal_disposition": (
        "perps_request_terminal_owner",
        "REQUESTED_CAPABILITY",
        "lane_capability:PERPS_MARKET:request_terminal_disposition",
        "PERPS_MARKET",
        ("UP-05",),
    ),
    "profiled_non_managed_issue": (
        "generic_non_managed_issue",
        "REQUESTED_CAPABILITY",
        "lane_capability:ASSET_TRANSFER:profiled_non_managed_issue",
        "ASSET_TRANSFER",
        ("NAMED_VERSIONED_ASSET_PROFILE_REGISTRY_REQUIRED",),
    ),
    "profiled_non_managed_burn": (
        "generic_non_managed_burn",
        "REQUESTED_CAPABILITY",
        "lane_capability:ASSET_TRANSFER:profiled_non_managed_burn",
        "ASSET_TRANSFER",
        ("NAMED_VERSIONED_ASSET_PROFILE_REGISTRY_REQUIRED",),
    ),
    "perps_realized_pnl_settlement": (
        "perps_realized_pnl_settlement",
        "REQUESTED_CAPABILITY",
        "lane_capability:PERPS_MARKET:realized_pnl_settlement",
        "PERPS_MARKET",
        ("UP-05", "UP-17"),
    ),
    "zusd_faucet_issuance": (
        "zusd_faucet_issuance_rejection",
        "EXCLUSION",
        "exclusion:zusd_faucet_issuance",
        "ZUSD_MONETARY",
        ("UP-19",),
    ),
    "sealed_auction_fee_allocation": (
        "sealed_auction_fee_allocation",
        "REQUESTED_CAPABILITY",
        "lane_capability:SEALED_AUCTION:sealed_auction_fee_allocation",
        "SEALED_AUCTION",
        ("UP-07", "FEE_POLICY_UNRESOLVED"),
    ),
    "sealed_auction_residue_terminal_disposition": (
        "sealed_auction_residue_terminal_disposition",
        "REQUESTED_CAPABILITY",
        "lane_capability:SEALED_AUCTION:sealed_auction_residue_terminal_disposition",
        "SEALED_AUCTION",
        ("UP-07",),
    ),
    "sealed_auction_batch_terminal_state": (
        "sealed_auction_batch_terminal_state",
        "REQUESTED_CAPABILITY",
        "lane_capability:SEALED_AUCTION:sealed_auction_batch_terminal_state",
        "SEALED_AUCTION",
        ("UP-07",),
    ),
    "sealed_auction_fee_terminal_disposition": (
        "sealed_auction_fee_terminal_disposition",
        "REQUESTED_CAPABILITY",
        "lane_capability:SEALED_AUCTION:sealed_auction_fee_terminal_disposition",
        "SEALED_AUCTION",
        ("UP-07", "FEE_POLICY_UNRESOLVED"),
    ),
    "sealed_auction_reservation_terminal_disposition": (
        "sealed_auction_commitment_bond_inventory_payment_reservation_terminal_disposition",
        "REQUESTED_CAPABILITY",
        "lane_capability:SEALED_AUCTION:sealed_auction_reservation_terminal_disposition",
        "SEALED_AUCTION",
        ("UP-07",),
    ),
    "external_effect_delivery": (
        "external_effect_delivery",
        "REQUESTED_CAPABILITY",
        "lane_capability:EXTERNAL_CUSTODY:external_effect_delivery",
        "EXTERNAL_CUSTODY",
        ("COMPLETE_REGISTERED_EXTERNAL_PROFILE_REQUIRED",),
    ),
}

_ROUTE_ORACLE = {
    "fee_funded_zdex_purchase_and_burn": (
        "fee_funded_zdex_purchase_and_burn",
        (
            "UP-01",
            "UP-12",
            "UP-14",
            "SPOT_OUTPUT_SIZING_BINDING_UNRESOLVED",
            "MISSING_WORKFLOW_BDD",
            "MISSING_ATOMIC_FAILURE_BDD",
            "MISSING_TERMINAL_BDD",
            "MISSING_BVA_EVIDENCE",
            "MISSING_STATEFUL_HISTORY_EVIDENCE",
        ),
    ),
    "zusd_liquidation": ("zusd_liquidation_settlement", ("UP-04", "UP-17")),
    "perps_epoch_settlement": ("perps_epoch_settlement", ("UP-05", "UP-17")),
    "strategy_triggered_spot_swap": (
        "strategy_triggered_spot_swap",
        ("UP-08", "UP-12", "MISSING_WORKFLOW_BDD"),
    ),
}


def _artifact_bytes() -> bytes:
    return ARTIFACT_PATH.read_bytes()


def _artifact_object() -> dict[str, Any]:
    return cast(dict[str, Any], json.loads(_artifact_bytes().decode("utf-8")))


def _canonical_artifact(value: dict[str, Any]) -> bytes:
    return core.canonical_json_bytes_v1(value)


def _canonical_rerooted_artifact(value: dict[str, Any]) -> bytes:
    unsigned = {key: item for key, item in value.items() if key != "registry_root"}
    value["registry_root"] = hashlib.sha256(core.canonical_json_bytes_v1(unsigned)).hexdigest()
    return _canonical_artifact(value)


def _report(value: dict[str, object]) -> dict[str, Any]:
    return cast(dict[str, Any], value)


def _source_bytes() -> bytes:
    return build_shell.load_o005_source_bytes_v1(REPO_ROOT)


def test_given_fixed_json_vector_when_canonicalized_then_literal_oracle_matches() -> None:
    # Arrange
    value = {"unicode": "é", "x": [None, True, 0]}

    # Act
    encoded = core.canonical_json_bytes_v1(value)

    # Assert
    assert encoded == b'{"unicode":"\\u00e9","x":[null,true,0]}'


def test_given_non_bmp_expansion_over_byte_ceiling_when_checked_then_typed_reject_returns() -> None:
    # Arrange
    hostile = {"x": "\U00010000" * 87_381}
    raw = json.dumps(
        hostile,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")

    # Act
    report = _report(core.check_semantic_resolution_artifact_v1(raw, _source_bytes()))

    # Assert
    assert report["ok"] is False
    assert report["source_resolution_bijection_verified"] is False
    assert report["findings"] == [
        {
            "code": "JSON_BYTE_LIMIT",
            "detail": "upstream canonical JSON boundary rejected value",
            "path": "semantic_resolution_artifact",
        }
    ]


def test_given_oversized_ingress_when_rejected_then_sha256_never_observes_oversized_bytes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    oversized = b"x" * (core.MAX_ARTIFACT_BYTES_V1 + 1)
    real_sha256 = hashlib.sha256
    observed_sizes: list[int] = []

    def bounded_sha256(raw: bytes = b"") -> Any:
        observed_sizes.append(len(raw))
        if len(raw) > core.MAX_ARTIFACT_BYTES_V1:
            raise AssertionError("oversized bytes reached SHA-256")
        return real_sha256(raw)

    monkeypatch.setattr(core.hashlib, "sha256", bounded_sha256)

    # Act
    report = _report(core.check_semantic_resolution_artifact_v1(oversized, _source_bytes()))
    with pytest.raises(core.SemanticResolutionRejectV1) as source_rejected:
        core.parse_o005_source_snapshot_v1(oversized)

    # Assert
    assert report["ok"] is False
    assert report["artifact_sha256"] == ""
    assert report["findings"][0]["code"] == "JSON_BYTE_LIMIT"
    assert source_rejected.value.code == "JSON_BYTE_LIMIT"
    assert all(size <= core.MAX_ARTIFACT_BYTES_V1 for size in observed_sizes)


def test_given_caller_constructed_source_snapshot_when_building_then_typed_reject_returns() -> None:
    # Arrange
    forged = core.parse_o005_source_snapshot_v1(_source_bytes())

    # Act / Assert
    with pytest.raises(core.SemanticResolutionRejectV1) as rejected:
        core.build_semantic_resolution_artifact_v1(forged)  # type: ignore[arg-type]
    assert rejected.value.code == "JSON_BYTES_TYPE"
    report = _report(
        core.check_semantic_resolution_artifact_v1(
            _artifact_bytes(),
            forged,  # type: ignore[arg-type]
        )
    )
    assert report["ok"] is False
    assert report["source_resolution_bijection_verified"] is False
    assert report["findings"][0]["code"] == "JSON_BYTES_TYPE"


def test_given_pinned_o005_source_when_built_then_exact_generated_bytes_and_hash_match() -> None:
    # Arrange
    source_raw = _source_bytes()

    # Act
    built = core.build_semantic_resolution_artifact_v1(source_raw)

    # Assert
    assert built == _artifact_bytes()
    assert hashlib.sha256(built).hexdigest() == EXPECTED_ARTIFACT_SHA256
    assert build_shell.main(["--root", str(REPO_ROOT), "--check"]) == 0
    assert check_shell.main(["--root", str(REPO_ROOT)]) == 0


def test_given_stale_generated_bytes_when_build_check_runs_then_actual_and_expected_hashes_are_distinct(
    capsys: pytest.CaptureFixture[str], tmp_path: Path
) -> None:
    # Arrange
    source_path = tmp_path / core.SOURCE_ARTIFACT_PATH_V1
    source_path.parent.mkdir(parents=True)
    source_path.write_bytes(_source_bytes())
    artifact_path = tmp_path / build_shell.JSON_OUTPUT
    artifact_path.parent.mkdir(parents=True, exist_ok=True)
    stale = b'{"stale":true}'
    artifact_path.write_bytes(stale)
    expected = build_shell.build_artifact_v1(tmp_path)

    # Act
    status = build_shell.main(["--root", str(tmp_path), "--check"])
    report = _report(cast(dict[str, object], json.loads(capsys.readouterr().out)))

    # Assert
    assert status == 1
    assert report["ok"] is False
    assert report["artifact_sha256"] == hashlib.sha256(stale).hexdigest()
    assert report["expected_artifact_sha256"] == hashlib.sha256(expected).hexdigest()
    assert report["artifact_sha256"] != report["expected_artifact_sha256"]
    assert report["finding"] == {
        "code": "GENERATED_ARTIFACT_DRIFT",
        "detail": "actual bytes do not equal source-bound generated bytes",
        "path": str(build_shell.JSON_OUTPUT),
    }
    assert report["production_authority"] == "NONE"
    assert report["settlement_authority"] == "NONE"
    assert report["closed_value_movement_gates"] == 0


def test_given_hostile_path_objects_when_o005_shells_receive_them_then_rejection_precedes_hooks() -> (
    None
):
    # Arrange
    hook_calls: list[str] = []

    class HostilePath(PosixPath):
        def __bool__(self) -> bool:
            hook_calls.append("bool")
            raise RuntimeError("PATH_BOOL_HOOK")

        def __truediv__(self, other: object) -> HostilePath:
            hook_calls.append("truediv")
            raise RuntimeError("PATH_TRUEDIV_HOOK")

        def __str__(self) -> str:
            hook_calls.append("str")
            raise RuntimeError("PATH_STR_HOOK")

        def __fspath__(self) -> str:
            hook_calls.append("fspath")
            raise RuntimeError("PATH_FSPATH_HOOK")

    class HostilePathLike:
        def __bool__(self) -> bool:
            hook_calls.append("pathlike-bool")
            raise RuntimeError("PATHLIKE_BOOL_HOOK")

        def __truediv__(self, other: object) -> Path:
            hook_calls.append("pathlike-truediv")
            raise RuntimeError("PATHLIKE_TRUEDIV_HOOK")

        def __str__(self) -> str:
            hook_calls.append("pathlike-str")
            raise RuntimeError("PATHLIKE_STR_HOOK")

        def __fspath__(self) -> str:
            hook_calls.append("pathlike-fspath")
            raise RuntimeError("PATHLIKE_FSPATH_HOOK")

    hostile_values = (HostilePath(str(REPO_ROOT)), HostilePathLike())

    # Act / Assert
    for hostile in hostile_values:
        with pytest.raises(build_shell.ShellRejectV1) as source_rejected:
            build_shell.load_o005_source_bytes_v1(cast(Path, hostile))
        with pytest.raises(build_shell.ShellRejectV1) as reader_rejected:
            build_shell._read_bounded_regular_file_v1(cast(Path, hostile), 1, "hostile")
        root_report = _report(
            check_shell.check_m6_o005_semantic_resolutions_v1(cast(Path, hostile))
        )
        artifact_report = _report(
            check_shell.check_m6_o005_semantic_resolutions_v1(REPO_ROOT, cast(Path, hostile))
        )
        assert source_rejected.value.code == "FILE_PATH_TYPE"
        assert reader_rejected.value.code == "FILE_PATH_TYPE"
        assert root_report["findings"][0]["code"] == "FILE_PATH_TYPE"
        assert artifact_report["findings"][0]["code"] == "FILE_PATH_TYPE"

    # Assert
    assert hook_calls == []


@pytest.mark.parametrize("hostile_path", ("\x00", "prefix\x00suffix", "\ud800"))
def test_given_unencodable_path_text_when_o005_shells_receive_it_then_typed_rejection_returns(
    hostile_path: str,
) -> None:
    # Arrange / Act.
    with pytest.raises(build_shell.ShellRejectV1) as source_rejected:
        build_shell.load_o005_source_bytes_v1(hostile_path)
    root_report = _report(check_shell.check_m6_o005_semantic_resolutions_v1(hostile_path))
    artifact_report = _report(
        check_shell.check_m6_o005_semantic_resolutions_v1(REPO_ROOT, hostile_path)
    )

    # Assert.
    assert source_rejected.value.code == "FILE_PATH_ENCODING"
    assert root_report["ok"] is False
    assert artifact_report["ok"] is False
    assert root_report["findings"][0]["code"] == "FILE_PATH_ENCODING"
    assert artifact_report["findings"][0]["code"] == "FILE_PATH_ENCODING"
    assert root_report["production_authority"] == "NONE"
    assert artifact_report["closed_value_movement_gates"] == 0


def test_given_generated_registry_when_checked_then_only_source_resolution_bijection_is_positive() -> (
    None
):
    # Arrange
    report = _report(check_shell.check_m6_o005_semantic_resolutions_v1(REPO_ROOT))

    # Act
    ceiling = {
        key: report[key]
        for key in (
            "manifest_complete",
            "production_promotion",
            "release_eligible",
            "requirements_closed",
            "semantic_capability_coverage_complete",
            "semantic_closure_complete",
            "semantic_target_inventory_complete",
            "structural_mapping_complete",
            "value_movement_claim_allowed",
        )
    }

    # Assert
    assert report["ok"] is True
    assert report["source_resolution_bijection_verified"] is True
    assert all(value is False for value in ceiling.values())
    assert report["production_authority"] == "NONE"
    assert report["settlement_authority"] == "NONE"
    assert report["closed_value_movement_gates"] == 0
    assert report["vm_ledger_closed_gate_count"] == 0


def test_given_pinned_requirements_source_when_classified_then_all_twenty_policies_remain_unknown() -> (
    None
):
    # Arrange.
    source = cast(dict[str, Any], json.loads(_source_bytes()))
    expected_ids = tuple(f"UP-{ordinal:02d}" for ordinal in range(1, 21))

    # Act.
    source_policies = tuple(
        (row["requirement_id"], row["status"])
        for row in source["rows"]
        if row["kind"] == "UNRESOLVED_POLICY"
    )
    pins = _artifact_object()["source_pins"]

    # Assert.
    assert source_policies == tuple(
        (policy_id, "UNRESOLVED_POLICY_NOT_SELECTABLE") for policy_id in expected_ids
    )
    assert tuple(pins["unresolved_policy_ids"]) == expected_ids
    assert pins["unresolved_policy_status"] == "UNRESOLVED_POLICY_NOT_SELECTABLE"
    assert (
        pins["unresolved_policy_ids_root"]
        == hashlib.sha256(core.canonical_json_bytes_v1(list(expected_ids))).hexdigest()
    )


def test_given_registry_when_read_then_every_missing_concept_has_the_fixed_classification() -> None:
    # Arrange
    rows = _artifact_object()["resolution_rows"]

    # Act
    observed = {
        row["resolution_id"]: (
            row["source_missing_target_concept_id"],
            row["resolution_kind"],
            row["target_id"],
            row["lane_id"],
            tuple(row["blockers"]),
        )
        for row in rows
    }

    # Assert
    assert observed == _RESOLUTION_ORACLE


def test_given_resolution_rows_when_read_then_source_and_future_targets_are_bijective() -> None:
    # Arrange
    artifact = _artifact_object()
    rows = artifact["resolution_rows"]

    # Act
    source_ids = tuple(row["source_missing_target_concept_id"] for row in rows)
    resolution_ids = tuple(row["resolution_id"] for row in rows)
    target_ids = tuple(row["target_id"] for row in rows)

    # Assert
    assert source_ids == tuple(artifact["source_pins"]["missing_target_concept_ids"])
    assert len(source_ids) == len(set(source_ids)) == 12
    assert len(resolution_ids) == len(set(resolution_ids)) == 12
    assert len(target_ids) == len(set(target_ids)) == 12
    assert artifact["source_resolution_bijection_verified"] is True
    assert artifact["resolution_to_future_target_relation"] == "ONE_TO_ONE_FUTURE_TARGETS"


@pytest.mark.parametrize(
    ("collection", "expected_count", "neighbor_counts"),
    (
        ("resolution_rows", 12, (11, 13)),
        ("route_resolution_rows", 4, (3, 5)),
    ),
)
def test_given_classification_row_count_neighbors_when_parsed_then_only_exact_count_accepts(
    collection: str,
    expected_count: int,
    neighbor_counts: tuple[int, int],
) -> None:
    # Arrange.
    valid = _artifact_object()
    valid_rows = valid[collection]
    outcomes: list[tuple[int, str]] = []

    # Act.
    core.parse_semantic_resolution_artifact_v1(_artifact_bytes())
    outcomes.append((len(valid_rows), "ACCEPTED"))
    for count in neighbor_counts:
        candidate = _artifact_object()
        rows = candidate[collection]
        if count < expected_count:
            del rows[count:]
        else:
            rows.append(deepcopy(rows[-1]))
        with pytest.raises(core.SemanticResolutionRejectV1) as rejected:
            core.parse_semantic_resolution_artifact_v1(_canonical_rerooted_artifact(candidate))
        outcomes.append((count, rejected.value.code))

    # Assert.
    expected_code = "RESOLUTION_ROW_COUNT" if collection == "resolution_rows" else "ROUTE_ROW_COUNT"
    assert outcomes == [
        (expected_count, "ACCEPTED"),
        (neighbor_counts[0], expected_code),
        (neighbor_counts[1], expected_code),
    ]


def test_given_unprofiled_generic_rows_when_read_then_managed_issue_and_burn_remain_forbidden_aliases() -> (
    None
):
    # Arrange
    rows = {row["resolution_id"]: row for row in _artifact_object()["resolution_rows"]}

    # Act
    issue_rules = rows["profiled_non_managed_issue"]["policy_rules"]
    burn_rules = rows["profiled_non_managed_burn"]["policy_rules"]

    # Assert
    assert (
        rows["profiled_non_managed_issue"]["disposition"]
        == "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED"
    )
    assert (
        rows["profiled_non_managed_burn"]["disposition"]
        == "RESEARCH_ONLY_REQUESTED_CAPABILITY_UNMOUNTED"
    )
    assert "registered_ordinary_tokens_default_to_transfer_only" in issue_rules
    assert "registered_ordinary_tokens_default_to_transfer_only" in burn_rules
    assert "managed_issue_is_not_an_alias_for_generic_non_managed_issue" in issue_rules
    assert "managed_burn_is_not_an_alias_for_generic_non_managed_burn" in burn_rules
    assert "unprofiled_arbitrary_generic_issue_rejects_without_mutation" in issue_rules
    assert "unprofiled_arbitrary_generic_burn_rejects_without_mutation" in burn_rules


def test_given_registry_when_read_then_every_route_has_its_fixed_blockers_and_source_binding() -> (
    None
):
    # Arrange
    rows = _artifact_object()["route_resolution_rows"]

    # Act
    observed = {
        row["resolution_id"]: (row["source_route_id"], tuple(row["blockers"])) for row in rows
    }

    # Assert
    assert observed == _ROUTE_ORACLE


def test_given_buy_and_burn_route_when_read_then_only_exact_output_burn_is_declared() -> None:
    # Arrange
    rows = {row["resolution_id"]: row for row in _artifact_object()["route_resolution_rows"]}
    route = rows["fee_funded_zdex_purchase_and_burn"]

    # Act
    steps = tuple(route["route_steps"])
    substitutions = tuple(route["forbidden_substitutions"])
    retained_supply = route["retained_supply_policy"]

    # Assert
    assert steps == (
        "consume_only_governed_buyback_quote_asset_fee_allocation",
        "preserve_separate_hosting_staking_treasury_reserve_and_residue_allocations",
        "authenticated_release_selected_spot_purchase",
        "exact_received_zdex_atoms",
        "atomic_burn_of_exact_received_zdex_atoms",
    )
    assert substitutions == ("treasury_burn_substitution", "transfer_burn_substitution")
    assert retained_supply == {
        "authoritative_fixed_percentage_floor": False,
        "formula": "R(S)=ceil(p*S/q)",
        "p_and_q_domain": "EXACT_INTEGERS",
        "q_positive": True,
        "selection": "GOVERNED_POLICY",
        "strict_inequality": "0 < p < q",
    }


def test_given_buy_and_burn_constraint_when_read_then_spot_output_binding_remains_release_blocking() -> (
    None
):
    # Arrange
    artifact = _artifact_object()
    route = artifact["route_resolution_rows"][0]

    # Act
    nonclaims = tuple(artifact["nonclaims"])

    # Assert
    assert route["retained_supply_policy"]["p_and_q_domain"] == "EXACT_INTEGERS"
    assert route["retained_supply_policy"]["strict_inequality"] == "0 < p < q"
    assert route["retained_supply_policy"]["q_positive"] is True
    assert route["retained_supply_policy"]["selection"] == "GOVERNED_POLICY"
    assert "SPOT_OUTPUT_SIZING_BINDING_UNRESOLVED" in route["blockers"]
    assert (
        "The registry does not define how Spot output sizing enforces R(S)=ceil(p*S/q) while burning exact received zDEX atoms; clipping and residue behavior remain unresolved and release-blocking."
        in nonclaims
    )
    assert artifact["release_eligible"] is False
    assert artifact["value_movement_claim_allowed"] is False


def test_given_o010b_evidence_requirements_when_unbound_then_each_deficit_is_explicit() -> None:
    # Arrange
    route = _artifact_object()["route_resolution_rows"][0]

    # Act
    blockers = tuple(route["blockers"])

    # Assert
    assert route["resolution_id"] == "fee_funded_zdex_purchase_and_burn"
    assert route["missing_workflow_bdd"] is True
    assert blockers[-5:] == (
        "MISSING_WORKFLOW_BDD",
        "MISSING_ATOMIC_FAILURE_BDD",
        "MISSING_TERMINAL_BDD",
        "MISSING_BVA_EVIDENCE",
        "MISSING_STATEFUL_HISTORY_EVIDENCE",
    )


@pytest.mark.parametrize(
    "missing_blocker",
    (
        "MISSING_ATOMIC_FAILURE_BDD",
        "MISSING_TERMINAL_BDD",
        "MISSING_BVA_EVIDENCE",
        "MISSING_STATEFUL_HISTORY_EVIDENCE",
    ),
)
def test_given_rerooted_o010b_deficit_omission_when_checked_then_route_semantics_reject(
    missing_blocker: str,
) -> None:
    # Arrange
    candidate = _artifact_object()
    candidate["route_resolution_rows"][0]["blockers"].remove(missing_blocker)

    # Act
    with pytest.raises(core.SemanticResolutionRejectV1) as rejected:
        core.parse_semantic_resolution_artifact_v1(_canonical_rerooted_artifact(candidate))

    # Assert
    assert rejected.value.code == "ROUTE_SEMANTICS"


def test_given_fixed_classification_target_sets_when_read_then_projected_totals_are_derived() -> (
    None
):
    # Arrange
    artifact = _artifact_object()
    target_sets = artifact["projected_future_target_sets"]
    base = target_sets["base_structural_counts"]
    totals = artifact["projected_future_structural_totals"]

    # Act
    derived = {
        "capability_count": base["capability_count"]
        + len(target_sets["future_capability_target_ids"]),
        "route_count": base["route_count"],
        "exclusion_count": base["exclusion_count"]
        + len(target_sets["future_exclusion_target_ids"]),
        "invariant_count": base["invariant_count"],
        "global_obligation_count": base["global_obligation_count"]
        + len(target_sets["future_global_obligation_ids"]),
    }
    derived["total"] = sum(derived.values())

    # Assert
    assert totals["label"] == "PROJECTED_AFTER_FUTURE_CAPABILITY_MANIFEST_AMENDMENT_NON_PROMOTIONAL"
    assert totals["current_o005_counts_unchanged"] is True
    assert target_sets["future_capability_target_ids"] == [
        "lane_capability:PERPS_MARKET:request_terminal_disposition",
        "lane_capability:ASSET_TRANSFER:profiled_non_managed_issue",
        "lane_capability:ASSET_TRANSFER:profiled_non_managed_burn",
        "lane_capability:PERPS_MARKET:realized_pnl_settlement",
        "lane_capability:SEALED_AUCTION:sealed_auction_fee_allocation",
        "lane_capability:SEALED_AUCTION:sealed_auction_residue_terminal_disposition",
        "lane_capability:SEALED_AUCTION:sealed_auction_batch_terminal_state",
        "lane_capability:SEALED_AUCTION:sealed_auction_fee_terminal_disposition",
        "lane_capability:SEALED_AUCTION:sealed_auction_reservation_terminal_disposition",
        "lane_capability:EXTERNAL_CUSTODY:external_effect_delivery",
    ]
    assert target_sets["future_exclusion_target_ids"] == ["exclusion:zusd_faucet_issuance"]
    assert target_sets["future_global_obligation_ids"] == [
        "global_obligation:pending_asset_intent_terminal_coverage"
    ]
    assert target_sets["non_counted_production_rejection_policy_resolution_ids"] == []
    assert derived == {
        "capability_count": 113,
        "route_count": 4,
        "exclusion_count": 5,
        "invariant_count": 14,
        "global_obligation_count": 6,
        "total": 142,
    }
    assert {field: totals[field] for field in derived} == derived
    assert (
        totals["evidence_denominator"]
        == (derived["capability_count"] + derived["route_count"]) * 9 + derived["exclusion_count"]
    )
    assert totals["evidence_denominator"] == 1058


@pytest.mark.parametrize(
    ("raw", "code"),
    [
        (b'{"x":1,"x":2}', "JSON_DECODE"),
        (b"{}", "JSON_FIELDS"),
    ],
)
def test_given_malformed_or_duplicate_bytes_when_parsed_then_typed_rejects_are_reported(
    raw: bytes,
    code: str,
) -> None:
    # Arrange / Act
    with pytest.raises(core.SemanticResolutionRejectV1) as rejected:
        core.parse_semantic_resolution_artifact_v1(raw)

    # Assert
    assert rejected.value.code == code


def test_given_mutable_or_subclassed_bytes_when_parsed_then_exact_immutable_ingress_rejects() -> (
    None
):
    # Arrange
    class BytesSubclass(bytes):
        pass

    inputs = (bytearray(_artifact_bytes()), BytesSubclass(_artifact_bytes()))

    # Act / Assert
    for raw in inputs:
        with pytest.raises(core.SemanticResolutionRejectV1) as rejected:
            core.parse_semantic_resolution_artifact_v1(cast(bytes, raw))
        assert rejected.value.code == "JSON_BYTES_TYPE"


def test_given_external_object_alias_when_original_immutable_bytes_are_checked_then_result_is_unchanged() -> (
    None
):
    # Arrange
    original = _artifact_bytes()
    alias = bytearray(original)
    alias[0] = ord("[")
    source_raw = _source_bytes()

    # Act
    report = _report(core.check_semantic_resolution_artifact_v1(original, source_raw))

    # Assert
    assert bytes(alias) != original
    assert report["ok"] is True


def test_given_unknown_field_when_parsed_then_closed_schema_rejects_before_promotion() -> None:
    # Arrange
    mutated = _artifact_object()
    mutated["unreviewed_authority"] = "ACTIVE_NEW"

    # Act / Assert
    with pytest.raises(core.SemanticResolutionRejectV1) as rejected:
        core.parse_semantic_resolution_artifact_v1(_canonical_artifact(mutated))
    assert rejected.value.code == "JSON_FIELDS"


@pytest.mark.parametrize(
    ("mutation", "expected_code"),
    (
        ("transfer-burn-substitution", "ROUTE_SEMANTICS"),
        ("claim-buy-burn-bdd-complete", "ROUTE_SEMANTICS"),
        ("managed-issue-alias", "RESOLUTION_SEMANTICS"),
        ("lane-substitution", "RESOLUTION_SEMANTICS"),
        ("resolution-kind-substitution", "RESOLUTION_SEMANTICS"),
        ("route-order-substitution", "ROUTE_SOURCE_ORDER"),
        ("authority-promotion", "CLAIM_CEILING"),
        ("requirements-closure-promotion", "CLAIM_CEILING"),
        ("erase-external-lane-nonclaim", "NONCLAIM_SEMANTICS"),
    ),
)
def test_given_rerooted_semantic_substitution_when_standalone_parser_runs_then_it_rejects(
    mutation: str,
    expected_code: str,
) -> None:
    # Arrange.
    candidate = _artifact_object()
    if mutation == "transfer-burn-substitution":
        candidate["route_resolution_rows"][0]["route_steps"][-1] = "transfer_burn_substitution"
    elif mutation == "claim-buy-burn-bdd-complete":
        route = candidate["route_resolution_rows"][0]
        route["missing_workflow_bdd"] = False
        route["blockers"].remove("MISSING_WORKFLOW_BDD")
    elif mutation == "managed-issue-alias":
        candidate["resolution_rows"][2]["target_id"] = (
            "lane_capability:ASSET_TRANSFER:managed_issue"
        )
    elif mutation == "lane-substitution":
        candidate["resolution_rows"][1]["lane_id"] = "ZUSD_MONETARY"
    elif mutation == "resolution-kind-substitution":
        candidate["resolution_rows"][1]["resolution_kind"] = "EXCLUSION"
    elif mutation == "route-order-substitution":
        candidate["route_resolution_rows"].reverse()
    elif mutation == "authority-promotion":
        candidate["production_authority"] = "ACTIVE"
    elif mutation == "requirements-closure-promotion":
        candidate["requirements_closed"] = True
    else:
        candidate["nonclaims"][-1] = ""

    # Act.
    with pytest.raises(core.SemanticResolutionRejectV1) as rejected:
        core.parse_semantic_resolution_artifact_v1(_canonical_rerooted_artifact(candidate))

    # Assert.
    assert rejected.value.code == expected_code


def test_given_source_drift_when_checked_then_exact_source_pin_rejects(tmp_path: Path) -> None:
    # Arrange
    source_path = tmp_path / core.SOURCE_ARTIFACT_PATH_V1
    source_path.parent.mkdir(parents=True)
    source = json.loads((REPO_ROOT / core.SOURCE_ARTIFACT_PATH_V1).read_text("utf-8"))
    source["nonclaims"] = ["source bytes drift while semantic target rows stay fixed"]
    source_path.write_bytes(_canonical_artifact(source))

    # Act
    report = _report(check_shell.check_m6_o005_semantic_resolutions_v1(tmp_path, ARTIFACT_PATH))

    # Assert
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "SOURCE_ARTIFACT_SHA256"
    assert report["production_authority"] == "NONE"
    assert report["closed_value_movement_gates"] == 0


def test_given_resolution_order_drift_when_checked_then_bijection_rejects() -> None:
    # Arrange
    mutated = _artifact_object()
    rows = mutated["resolution_rows"]
    rows[0], rows[1] = rows[1], rows[0]

    # Act
    report = _report(
        core.check_semantic_resolution_artifact_v1(
            _canonical_artifact(mutated),
            _source_bytes(),
        )
    )

    # Assert
    assert report["ok"] is False
    assert report["findings"][0]["code"] == "RESOLUTION_SOURCE_ORDER"


def test_given_depth_two_structure_preserving_mutants_when_checked_then_none_survive() -> None:
    # Arrange
    valid = _artifact_object()

    def promote_gate(candidate: dict[str, Any]) -> None:
        candidate["closed_value_movement_gates"] = 1

    def reverse_routes(candidate: dict[str, Any]) -> None:
        candidate["route_resolution_rows"].reverse()

    def alter_source_hash(candidate: dict[str, Any]) -> None:
        candidate["source_pins"]["o005_requirements_artifact_sha256"] = "0" * 64

    def add_unknown_field(candidate: dict[str, Any]) -> None:
        candidate["unexpected"] = False

    mutations = (promote_gate, reverse_routes, alter_source_hash, add_unknown_field)

    # Act
    reports: list[dict[str, Any]] = []
    for first in mutations:
        one_hop = deepcopy(valid)
        first(one_hop)
        reports.append(
            _report(
                core.check_semantic_resolution_artifact_v1(
                    _canonical_artifact(one_hop),
                    _source_bytes(),
                )
            )
        )
        for second in mutations:
            if second is first:
                continue
            two_hop = deepcopy(one_hop)
            second(two_hop)
            reports.append(
                _report(
                    core.check_semantic_resolution_artifact_v1(
                        _canonical_artifact(two_hop),
                        _source_bytes(),
                    )
                )
            )

    # Assert
    assert len(reports) == 16
    assert all(report["ok"] is False for report in reports)
    assert all(report["closed_value_movement_gates"] == 0 for report in reports)
    assert all(report["production_authority"] == "NONE" for report in reports)
