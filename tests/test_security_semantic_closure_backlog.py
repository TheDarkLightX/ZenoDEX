from __future__ import annotations

import json
import re
from collections.abc import Iterator
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
LEDGER_PATH = ROOT / "docs" / "audit" / "zenodex_closure_backlog_v1.json"
EXPECTED_PROFILE_IDS = {"production-strict", "public-testnet", "local-dev"}
EXPECTED_WORKBOOK_SHA256 = (
    "b536bc5c1ca4c24866a62c1a0919e5272b608f5f7b3fc7621cbfbf5caa7c3918"
)
LOCAL_CANDIDATE_IDS = {
    "STATE-ALIAS-001",
    "STATE-ALIAS-002",
    "STATE-ALIAS-003",
    "STATE-ALIAS-004",
    "STATE-ALIAS-005",
    "STATE-ALIAS-006",
    "SPOT-REJECT-ATOMICITY-001",
    "CPMM-EXACT-OUT-DOMAIN-001",
    "CPMM-PROTOCOL-FEE-BOUNDARY-001",
    "SPOT-TAU-FEE-RESERVE-BINDING-001",
    "PERP-PARTIAL-LIQUIDATION-REACHABILITY-001",
}
EXACT_GITHUB_ISSUE_FINDINGS = {
    "VAULT-CLAIMANT-ENTITLEMENT-001": 458,
    "PERP-ORACLE-AUTHORITY-PARITY-001": 455,
    "PROOF-VERIFIER-AUTHORITY-001": 411,
    "PROOF-LEDGER-BINDING-CHAIN-001": 412,
    "PROOF-SETTLEMENT-ADMISSION-001": 415,
}


def _load_ledger() -> dict[str, Any]:
    value = json.loads(LEDGER_PATH.read_text(encoding="utf-8"))
    assert type(value) is dict
    return value


def _iter_dicts(value: Any) -> Iterator[dict[str, Any]]:
    if type(value) is dict:
        yield value
        for child in value.values():
            yield from _iter_dicts(child)
    elif type(value) is list:
        for child in value:
            yield from _iter_dicts(child)


def _assert_complete_profile_resolution(entry: dict[str, Any]) -> None:
    applicability = entry["deployment_applicability"]
    assert type(applicability) is dict
    profiles = applicability["profiles"]
    unresolved = applicability["unresolved_profiles"]
    exclusions = applicability["exclusions"]
    assert type(profiles) is list
    assert type(unresolved) is list
    assert type(exclusions) is list
    assert all(type(profile) is str for profile in [*profiles, *unresolved])

    excluded_profiles: list[str] = []
    for exclusion in exclusions:
        assert type(exclusion) is dict
        assert exclusion["enforced"] is True
        assert type(exclusion["profile"]) is str
        assert exclusion["enforcement_evidence_refs"]
        excluded_profiles.append(exclusion["profile"])

    decisions = [*profiles, *unresolved, *excluded_profiles]
    assert len(decisions) == len(set(decisions))
    assert set(decisions) == EXPECTED_PROFILE_IDS


def test_security_semantic_closure_backlog_reconciles_to_39() -> None:
    ledger = _load_ledger()
    assert ledger["schema"] == "zenodex/security-semantic-closure-backlog/v1"

    findings = ledger["findings"]
    obligations = ledger["promotion_evidence_obligations"]
    groups = ledger["count_only_groups"]
    assert type(findings) is list
    assert type(obligations) is list
    assert type(groups) is list

    all_ids = [entry["id"] for entry in [*findings, *obligations, *groups]]
    assert len(all_ids) == len(set(all_ids))

    required_finding_fields = {
        "id",
        "kind",
        "area",
        "title",
        "status",
        "detail_status",
        "deployment_applicability",
        "evidence_refs",
        "closure_criteria",
        "release_credit",
        "release_credit_rule",
    }
    for finding in findings:
        assert type(finding) is dict
        assert required_finding_fields <= finding.keys()
        assert finding["kind"] == "defect_family"
        assert finding["detail_status"] == "enumerated"
        assert finding["status"] in {"open", "candidate_uncredited"}
        assert finding["release_credit"] is False
        assert finding["release_credit_rule"] == "RCR-1"
        assert finding["evidence_refs"]
        assert finding["closure_criteria"]
        _assert_complete_profile_resolution(finding)
        if finding["status"] == "candidate_uncredited":
            assert (
                finding["candidate_state"]
                == "local_committed_unreviewed_unmerged_no_release_credit"
            )
            candidate_refs = finding["candidate_evidence_refs"]
            assert candidate_refs
            for ref in candidate_refs:
                path_text, anchor = ref.split("#", 1)
                source = (ROOT / path_text).read_text(encoding="utf-8")
                assert f"def {anchor}" in source
        else:
            assert "candidate_state" not in finding
            assert "candidate_evidence_refs" not in finding

    for obligation in obligations:
        assert type(obligation) is dict
        assert required_finding_fields <= obligation.keys()
        assert obligation["kind"] == "promotion_evidence_obligation"
        assert obligation["detail_status"] == "enumerated"
        assert obligation["status"] in {"open", "candidate_uncredited", "blocked"}
        assert obligation["release_credit"] is False
        assert obligation["release_credit_rule"] == "RCR-1"
        assert obligation["evidence_refs"]
        assert obligation["closure_criteria"]
        _assert_complete_profile_resolution(obligation)
        if obligation["status"] == "candidate_uncredited":
            assert (
                obligation["candidate_state"]
                == "local_committed_unreviewed_unmerged_no_release_credit"
            )
        else:
            assert "candidate_state" not in obligation

    required_group_fields = {
        "id",
        "kind",
        "area",
        "count",
        "status",
        "detail_status",
        "deployment_applicability",
        "evidence_refs",
        "release_credit",
        "release_credit_rule",
    }
    for group in groups:
        assert type(group) is dict
        assert required_group_fields <= group.keys()
        assert group["kind"] in {
            "defect_family_group",
            "promotion_evidence_obligation_group",
        }
        assert type(group["count"]) is int and group["count"] > 0
        expected_status = (
            "open" if group["kind"] == "defect_family_group" else "blocked"
        )
        assert group["status"] == expected_status
        assert group["detail_status"] == "unenumerated"
        assert group["release_credit"] is False
        assert group["release_credit_rule"] == "RCR-2"
        assert group["evidence_refs"]
        assert group["deployment_applicability"]["required_action"]
        _assert_complete_profile_resolution(group)

    exact_defects = [entry for entry in findings if entry["kind"] == "defect_family"]
    grouped_defects = [entry for entry in groups if entry["kind"] == "defect_family_group"]
    exact_obligations = obligations
    grouped_obligations = [
        entry
        for entry in groups
        if entry["kind"] == "promotion_evidence_obligation_group"
    ]

    defect_count = len(exact_defects) + sum(entry["count"] for entry in grouped_defects)
    obligation_count = len(exact_obligations) + sum(
        entry["count"] for entry in grouped_obligations
    )
    expected = ledger["expected_counts"]
    assert defect_count == expected["defect_families"] == 32
    assert obligation_count == expected["promotion_evidence_obligations"] == 7
    assert defect_count + obligation_count == expected["total_closure_items"] == 39
    assert {entry["id"] for entry in findings if entry["status"] == "candidate_uncredited"} == LOCAL_CANDIDATE_IDS
    assert not any(item.get("release_credit") is True for item in _iter_dicts(ledger))


def test_security_semantic_closure_backlog_pins_sources_and_live_candidate_state() -> None:
    ledger = _load_ledger()
    basis = ledger["basis"]

    workbook = basis["spreadsheet_oracle"]
    assert workbook == {
        "filename": "zenodex_spreadsheet_oracle_audit_workbook_v4.xlsx",
        "version": "v4",
        "source_kind": "user_supplied_attachment",
        "sha256": EXPECTED_WORKBOOK_SHA256,
    }
    assert re.fullmatch(r"[0-9a-f]{64}", workbook["sha256"])
    assert "spreadsheet_oracle_revision" not in basis

    candidate = basis["candidate_worktree"]
    assert candidate == {
        "branch": "agent/differential-oracle-remaining-fixes-20260719",
        "base_revision": basis["repository_revision"],
        "candidate_revision": "4f6440827b110fc89693b3ec90d44851310f48db",
        "state": "local_committed_unreviewed",
        "release_credit": False,
    }

    pr454 = basis["pull_request_454_snapshot"]
    assert pr454["head_revision"] == basis["repository_revision"]
    assert pr454["head_branch"] == "agent/critical-core-assurance-pass-20260718"
    assert pr454["state"] == "open"
    assert pr454["draft"] is True
    assert pr454["merged"] is False
    assert pr454["required_ci"]["ci"] == "failure"
    assert pr454["release_credit"] is False


def test_security_semantic_closure_backlog_reconciles_area_counts() -> None:
    ledger = _load_ledger()
    observed: dict[str, int] = {}

    for finding in ledger["findings"]:
        if finding["kind"] != "defect_family":
            continue
        area = finding["area"]
        observed[area] = observed.get(area, 0) + 1

    for group in ledger["count_only_groups"]:
        if group["kind"] != "defect_family_group":
            continue
        area = group["area"]
        observed[area] = observed.get(area, 0) + group["count"]

    assert observed == ledger["expected_counts"]["defect_families_by_area"]


def test_known_open_github_issues_are_enumerated_not_hidden_in_groups() -> None:
    ledger = _load_ledger()
    findings = {entry["id"]: entry for entry in ledger["findings"]}
    group_refs = {
        ref
        for group in ledger["count_only_groups"]
        for ref in group["evidence_refs"]
    }

    for finding_id, issue_number in EXACT_GITHUB_ISSUE_FINDINGS.items():
        issue_url = f"https://github.com/TheDarkLightX/ZenoDEX/issues/{issue_number}"
        finding = findings[finding_id]
        assert finding["status"] == "open"
        assert issue_url in finding["evidence_refs"]
        assert issue_url not in group_refs

    group_counts = {
        entry["id"]: entry["count"] for entry in ledger["count_only_groups"]
    }
    assert group_counts == {
        "GROUP-ZUSD-UNENUMERATED-001": 10,
        "GROUP-PERPS-ORACLE-UNENUMERATED-001": 4,
        "GROUP-KEYS-PROOF-COVER-FIRE-UNENUMERATED-001": 2,
        "GROUP-PROMOTION-EVIDENCE-UNENUMERATED-001": 6,
    }


def test_deployment_profile_decisions_are_total_and_do_not_invent_exclusions() -> None:
    ledger = _load_ledger()
    declared_profiles = {entry["id"] for entry in ledger["deployment_profiles"]}
    assert declared_profiles == EXPECTED_PROFILE_IDS

    for profile in ledger["deployment_profiles"]:
        locator = ROOT / profile["locator"]
        assert locator.is_file()
        assert f"profile_id: {profile['id']}" in locator.read_text(encoding="utf-8")

    governed_entries = [
        *ledger["findings"],
        *ledger["promotion_evidence_obligations"],
        *ledger["count_only_groups"],
        *ledger["non_backlog_dispositions"],
    ]
    for entry in governed_entries:
        _assert_complete_profile_resolution(entry)

    assert all(
        not entry["deployment_applicability"]["exclusions"]
        for entry in governed_entries
    )


def test_cpmm_expected_reject_control_does_not_credit_integration_atomicity() -> None:
    ledger = _load_ledger()
    controls = {entry["id"]: entry for entry in ledger["verified_non_defect_controls"]}
    control = controls["CPMM-IN-003"]

    assert "src/kernels/python/cpmm_swap_v8.py#swap_exact_in_v8" in control[
        "evidence_refs"
    ]
    assert not any("commits_nonce_only" in ref for ref in control["evidence_refs"])
    assert "SPOT-REJECT-ATOMICITY-001" in control["scope_boundary"]

    reject_finding = next(
        entry
        for entry in ledger["findings"]
        if entry["id"] == "SPOT-REJECT-ATOMICITY-001"
    )
    assert reject_finding["status"] == "candidate_uncredited"
    assert reject_finding["release_credit"] is False


def test_security_semantic_closure_backlog_preserves_non_backlog_boundaries() -> None:
    ledger = _load_ledger()
    dispositions = {entry["id"]: entry for entry in ledger["non_backlog_dispositions"]}

    builders = dispositions["DISPOSITION-F14-F18"]
    assert builders["source_finding_ids"] == ["F14", "F15", "F16", "F17", "F18"]
    assert builders["disposition"] == "accepted_internal_builders"
    assert builders["counted_in_closure_backlog"] is False
    assert "non-escaping" in builders["constraint"]
    assert builders["release_credit"] is False
    assert builders["evidence_refs"]
    assert (
        builders["deployment_applicability"]["state"]
        == "conditional_disposition_not_an_enforced_profile_exclusion"
    )
    _assert_complete_profile_resolution(builders)

    demo_globals = dispositions["DISPOSITION-F19-F20"]
    assert demo_globals["source_finding_ids"] == ["F19", "F20"]
    assert demo_globals["disposition"] == "removed_demo_globals_candidate_uncredited"
    assert demo_globals["counted_in_closure_backlog"] is False
    assert "removed" in demo_globals["constraint"]
    assert demo_globals["release_credit"] is False
    assert demo_globals["evidence_refs"]
    assert (
        demo_globals["deployment_applicability"]["state"]
        == "candidate_uncredited_removal"
    )
    _assert_complete_profile_resolution(demo_globals)

    controls = {
        entry["id"]: entry["disposition"]
        for entry in ledger["verified_non_defect_controls"]
    }
    assert controls == {
        "CPMM-IN-003": "expected_reject_pass_not_a_defect",
        "CPMM-IN-004": "expected_reject_pass_not_a_defect",
    }


def test_unenumerated_groups_cannot_claim_release_credit() -> None:
    ledger = _load_ledger()
    groups = ledger["count_only_groups"]
    assert groups
    assert all(group["detail_status"] == "unenumerated" for group in groups)
    assert all(group["release_credit"] is False for group in groups)

    unreconciled = ledger["unreconciled_candidates"]
    assert unreconciled
    assert all(item["counted_in_39_item_floor"] is False for item in unreconciled)
    assert all(item["release_credit"] is False for item in unreconciled)
    assert ledger["closure_gate"]["release_blocked"] is True


def test_closure_gate_summary_and_canonical_blockers_are_derived() -> None:
    ledger = _load_ledger()
    findings = ledger["findings"]
    obligations = ledger["promotion_evidence_obligations"]
    groups = ledger["count_only_groups"]
    closure = ledger["closure_gate"]

    grouped_defects = sum(
        entry["count"] for entry in groups if entry["kind"] == "defect_family_group"
    )
    grouped_obligations = sum(
        entry["count"]
        for entry in groups
        if entry["kind"] == "promotion_evidence_obligation_group"
    )
    assert closure["summary"] == {
        "credited_items": 0,
        "candidate_uncredited_exact_defects": sum(
            entry["status"] == "candidate_uncredited" for entry in findings
        ),
        "open_exact_defects": sum(entry["status"] == "open" for entry in findings),
        "unenumerated_defect_items": grouped_defects,
        "blocked_exact_obligations": sum(
            entry["status"] == "blocked" for entry in obligations
        ),
        "unenumerated_obligation_items": grouped_obligations,
    }

    blockers = {entry["id"]: entry for entry in closure["canonical_blockers"]}
    assert set(blockers) == {
        "BLOCKER-ZERO-RELEASE-CREDIT",
        "BLOCKER-UNENUMERATED-ITEMS",
        "BLOCKER-DIRTY-LOCAL-CANDIDATES",
        "BLOCKER-PR454-DRAFT-RED-UNMERGED",
        "BLOCKER-PARTIAL-LIQUIDATION-FORMAL",
        "BLOCKER-UNRESOLVED-PROFILE-DECISIONS",
        "BLOCKER-UNRECONCILED-CANDIDATES",
    }
    assert all(entry["evidence_refs"] for entry in blockers.values())
    assert all(entry["release_credit"] is False for entry in blockers.values())
    assert not any("defect-family rows" in reason for reason in closure["reasons"])
