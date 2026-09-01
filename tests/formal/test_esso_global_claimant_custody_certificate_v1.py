"""Bounded ESSO and V1 information-loss evidence for claimant backing.

The ESSO model is a target certificate contract. The executable V1 witnesses
show why its exact lane-derived fields cannot be reconstructed from current
global-state bytes. No test in this module grants verifier or settlement
authority.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

from src.core.global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementCandidateV1,
    refine_global_economic_state_effects_v1,
)
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
)

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "global_claimant_custody_certificate_v1.yaml"

RECORDED_SOURCE_SHA256 = "1fe5238d3f7444a611ecdc2c802a145e7d9ef19558cab485452959010d1a05d4"
RECORDED_IR_HASH = "sha256:a86a2b43893e5c9ad22c44e986d6e4d69c422de9d12d88029c4197c665ab65c1"
RECORDED_FINGERPRINT = "e37705902eb04f48aee9ab1fac333396b80a317716aeb64f51ebdb72cb3fde82"
RECORDED_ESSO_CODE_HASH = "1145cf77668b6d86cda83d79820b13a65fbde12f"

EXPECTED_ACTIONS = {"open_claim", "drain_claim"}
EXPECTED_INVARIANTS = {
    "inv_exact_custody_partition_d0",
    "inv_exact_custody_partition_d1",
    "inv_exact_claimant_domain_liabilities",
    "inv_open_terminals_fit_exact_allocations",
    "inv_accept_requires_exact_bound_evidence",
    "inv_reserves_are_not_claimant_backing",
}


def _document() -> dict[str, object]:
    value = yaml.safe_load(MODEL.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _esso_python() -> str | None:
    configured = os.environ.get("ZENO_ESSO_PYTHON")
    if configured:
        return configured
    if importlib.util.find_spec("ESSO") is not None:
        return sys.executable
    return None


def _run_esso(python: str, *args: str) -> tuple[int, dict[str, object]]:
    process = subprocess.run(
        [python, "-m", "ESSO", *args],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    raw = process.stdout if process.stdout.strip() else process.stderr
    value = json.loads(raw)
    assert isinstance(value, dict)
    return process.returncode, value


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _lane_roots(perps_root: int = 40_000) -> tuple[LaneStateRootV1, ...]:
    return tuple(
        LaneStateRootV1(
            lane_id,
            _root(41_000 + index),
            True,
            _root(perps_root if lane_id is LaneIdV1.PERPS_MARKET else 42_000 + index),
        )
        for index, lane_id in enumerate(ALL_LANE_IDS_V1)
    )


def _amounts(*rows: tuple[str, str, str, int]) -> tuple[EconomicAmountV1, ...]:
    return tuple(
        sorted(
            (EconomicAmountV1(owner, asset, domain, amount) for owner, asset, domain, amount in rows),
            key=lambda row: row.key,
        )
    )


def _state(
    *,
    custody: tuple[tuple[str, str, str, int], ...],
    liabilities: tuple[tuple[str, str, str, int], ...],
    terminals: tuple[TerminalObligationV1, ...],
    lane_roots: tuple[LaneStateRootV1, ...] | None = None,
) -> GlobalEconomicStateV1:
    supplies = tuple(
        AssetSupplyV1(
            asset,
            sum(amount for _, row_asset, _, amount in custody if row_asset == asset),
        )
        for asset in sorted({row[1] for row in custody})
    )
    return GlobalEconomicStateV1(
        chain_id="zeno-claimant-certificate-no-go",
        deployment_root=_root(43_000),
        writer_epoch=1,
        height=1,
        profile_root=_root(43_001),
        lane_roots=lane_roots or _lane_roots(),
        supplies=supplies,
        custody=_amounts(*custody),
        liabilities=_amounts(*liabilities),
        terminal_obligations=tuple(sorted(terminals, key=lambda row: row.obligation_id)),
    )


def _accept_static_state(state: GlobalEconomicStateV1) -> None:
    candidate = GlobalEconomicStateEffectRefinementCandidateV1(
        state,
        state,
        GlobalEconomicEffectPlanV1.empty(),
    )
    refinement = refine_global_economic_state_effects_v1(candidate)
    assert refinement.pre_state_root == state.state_root
    assert refinement.post_state_root == state.state_root


def test_model_source_scope_and_claim_ceiling_are_exact() -> None:
    document = _document()
    source_hash = hashlib.sha256(MODEL.read_bytes()).hexdigest()
    actions = {row["id"] for row in document["actions"]}
    invariants = {row["id"] for row in document["invariants"]}
    notes = " ".join(document["meta"]["notes"].split())

    assert source_hash == RECORDED_SOURCE_SHA256
    assert document["meta"]["model_id"] == "global_claimant_custody_certificate_v1"
    assert actions == EXPECTED_ACTIONS
    assert invariants == EXPECTED_INVARIANTS
    for phrase in (
        "one asset, two custody domains, two claimants",
        "caller-provided true Boolean would not be authority",
        "does not prove current V1 runtime refinement",
        "settlement authority",
        "ABI extension remains required",
    ):
        assert phrase in notes


def test_exact_relation_excludes_reserves_and_classifies_every_custody_atom() -> None:
    document = _document()
    invariant_text = json.dumps(document["invariants"], sort_keys=True)

    assert "allocation_alice_d0" in invariant_text
    assert "unencumbered_d0" in invariant_text
    assert "liability_alice_d0" in invariant_text
    assert "open_alice_d0" in invariant_text
    assert "reserve_d0" not in json.dumps(document["invariants"][:4], sort_keys=True)

    custody = 2
    allocations = 1
    unencumbered = 0
    assert custody >= allocations + unencumbered
    assert custody != allocations + unencumbered, "weak inequality leaves one atom unclassified"


def test_aggregate_conservation_does_not_imply_domain_or_claimant_reconciliation() -> None:
    custody_by_domain = {"d0": 0, "d1": 2}
    liability_by_domain = {"d0": 2, "d1": 0}
    terminal_by_claimant = {"alice": 1, "bob": 1}
    liability_by_claimant = {"alice": 0, "bob": 2}

    assert sum(custody_by_domain.values()) == sum(liability_by_domain.values())
    assert liability_by_domain["d0"] > custody_by_domain["d0"]
    assert sum(terminal_by_claimant.values()) == sum(liability_by_claimant.values())
    assert terminal_by_claimant["alice"] > liability_by_claimant["alice"]


@pytest.mark.skipif(_esso_python() is None, reason="ESSO unavailable; formal replay is INCOMPLETE")
def test_esso_two_solver_replay_is_exact_and_deterministic() -> None:
    python = _esso_python()
    assert python is not None

    validate_rc, validate = _run_esso(python, "validate", str(MODEL))
    verify_rc, verify = _run_esso(
        python,
        "verify-multi",
        str(MODEL),
        "--solvers",
        "z3,cvc5",
        "--determinism-trials",
        "2",
        "--timeout-ms",
        "10000",
    )

    assert validate_rc == 0 and validate["ok"] is True
    assert validate["ir_hash"] == RECORDED_IR_HASH
    assert verify_rc == 0 and verify["ok"] is True
    assert verify["determinism"] is True
    assert verify["fingerprints"] == [RECORDED_FINGERPRINT, RECORDED_FINGERPRINT]
    report = verify["report"]
    assert report["verdict"] == "VERIFIED"
    assert report["failed_queries"] == 0
    assert report["inconclusive_queries"] == 0
    assert report["solvers_agreed"] is True
    assert report["tool_versions"]["esso_code_hash"] == RECORDED_ESSO_CODE_HASH
    assert set(verify["queries"]) == {
        "init_implies_inv",
        "inductive_open_claim",
        "inductive_drain_claim",
    }


@pytest.mark.parametrize(
    ("needle", "replacement", "named_disaster"),
    (
        pytest.param(
            'args:\n        - { param: "global_root_bound" }\n        - { param: "lane_projection_root_bound" }',
            'args:\n        - { bool: true }\n        - { param: "lane_projection_root_bound" }',
            "accept_without_global_root_binding",
            id="accept_without_global_root_binding",
        ),
        pytest.param(
            '- var: "custody_d0"\n        expr:\n          op: "ite"\n          cond: { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }\n          then: { op: "+", args: [{ var: "custody_d0" }, { param: "amount" }] }',
            '- var: "custody_d0"\n        expr:\n          op: "ite"\n          cond: { op: "=", args: [{ param: "domain" }, { enum: "D1" }] }\n          then: { op: "+", args: [{ var: "custody_d0" }, { param: "amount" }] }',
            "cross_domain_custody_substitution",
            id="cross_domain_custody_substitution",
        ),
        pytest.param(
            '- var: "custody_d0"\n        expr:\n          op: "ite"\n          cond: { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }\n          then: { op: "+", args: [{ var: "custody_d0" }, { param: "amount" }] }',
            '- var: "reserve_d0"\n        expr:\n          op: "ite"\n          cond: { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }\n          then: { op: "+", args: [{ var: "reserve_d0" }, { param: "amount" }] }',
            "reserve_used_as_claimant_backing",
            id="reserve_used_as_claimant_backing",
        ),
        pytest.param(
            '- var: "liability_alice_d0"\n        expr:\n          op: "ite"\n          cond: { op: "and", args: [{ op: "=", args: [{ param: "claimant" }, { enum: "ALICE" }] }, { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }] }\n          then: { op: "+", args: [{ var: "liability_alice_d0" }, { param: "amount" }] }',
            '- var: "liability_alice_d0"\n        expr:\n          op: "ite"\n          cond: { op: "and", args: [{ op: "=", args: [{ param: "claimant" }, { enum: "BOB" }] }, { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }] }\n          then: { op: "+", args: [{ var: "liability_alice_d0" }, { param: "amount" }] }',
            "claimant_column_substitution",
            id="claimant_column_substitution",
        ),
        pytest.param(
            '- var: "open_alice_d0"\n        expr:\n          op: "ite"\n          cond: { op: "and", args: [{ op: "=", args: [{ param: "claimant" }, { enum: "ALICE" }] }, { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }] }\n          then: { op: "+", args: [{ var: "open_alice_d0" }, { param: "amount" }] }',
            '- var: "open_alice_d0"\n        expr:\n          op: "ite"\n          cond: { op: "and", args: [{ op: "=", args: [{ param: "claimant" }, { enum: "ALICE" }] }, { op: "=", args: [{ param: "domain" }, { enum: "D1" }] }] }\n          then: { op: "+", args: [{ var: "open_alice_d0" }, { param: "amount" }] }',
            "terminal_domain_erasure",
            id="terminal_domain_erasure",
        ),
    ),
)
@pytest.mark.skipif(_esso_python() is None, reason="ESSO unavailable; mutation replay is INCOMPLETE")
def test_named_semantic_mutants_produce_two_solver_counterexamples(
    tmp_path: Path,
    needle: str,
    replacement: str,
    named_disaster: str,
) -> None:
    source = MODEL.read_text(encoding="utf-8")
    assert source.count(needle) >= 1, named_disaster
    mutant = tmp_path / f"{named_disaster}.yaml"
    mutant.write_text(source.replace(needle, replacement, 1), encoding="utf-8")
    python = _esso_python()
    assert python is not None

    rc, result = _run_esso(
        python,
        "verify-multi",
        str(mutant),
        "--solvers",
        "z3,cvc5",
        "--determinism-trials",
        "2",
        "--timeout-ms",
        "10000",
    )

    assert rc != 0
    assert result["ok"] is False
    assert result["report"]["verdict"] == "FAILED"
    assert result["report"]["failed_queries"] >= 1
    assert result["report"]["inconclusive_queries"] == 0
    assert result["report"]["solvers_agreed"] is True


def test_v1_domainless_terminal_has_distinct_hidden_domain_preimages() -> None:
    terminal = TerminalObligationV1(
        "terminal-1",
        LaneIdV1.PERPS_MARKET,
        "alice",
        "USD",
        2,
        TerminalObligationStatusV1.OPEN,
    )
    hidden_d0 = (terminal, "perps-domain-0", "custody-0")
    hidden_d1 = (terminal, "perps-domain-1", "custody-1")
    assert hidden_d0 != hidden_d1
    assert hidden_d0[0].to_canonical() == hidden_d1[0].to_canonical()
    assert "custody_domain" not in terminal.to_canonical()
    assert "custody_principal" not in terminal.to_canonical()

    ambiguous = _state(
        custody=(
            ("custody-0", "USD", "perps-domain-0", 1),
            ("custody-1", "USD", "perps-domain-1", 1),
        ),
        liabilities=(
            ("alice", "USD", "perps-domain-0", 1),
            ("alice", "USD", "perps-domain-1", 1),
        ),
        terminals=(terminal,),
    )
    _accept_static_state(ambiguous)


def test_v1_same_lane_root_accepts_claimant_substitution_without_projection_evidence() -> None:
    lane_roots = _lane_roots(perps_root=44_000)
    custody = (("account-bob", "USD", "perps-margin", 1),)
    honest = _state(
        custody=custody,
        liabilities=(("alice", "USD", "perps-margin", 1),),
        terminals=(
            TerminalObligationV1(
                "terminal-1",
                LaneIdV1.PERPS_MARKET,
                "alice",
                "USD",
                1,
                TerminalObligationStatusV1.OPEN,
            ),
        ),
        lane_roots=lane_roots,
    )
    substituted = _state(
        custody=custody,
        liabilities=(("mallory", "USD", "perps-margin", 1),),
        terminals=(
            TerminalObligationV1(
                "terminal-1",
                LaneIdV1.PERPS_MARKET,
                "mallory",
                "USD",
                1,
                TerminalObligationStatusV1.OPEN,
            ),
        ),
        lane_roots=lane_roots,
    )

    assert honest.lane_roots == substituted.lane_roots
    assert honest.state_root != substituted.state_root
    _accept_static_state(honest)
    _accept_static_state(substituted)
