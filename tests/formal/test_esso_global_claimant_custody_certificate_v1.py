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
from src.core.perps_margin_lane_coordinator_v1 import PerpsMarginLaneProjectionV1
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_CUSTODY_DOMAIN_V1,
    PerpsMarginAccountStatusV1,
    PerpsMarginAccountV1,
    PerpsMarginMarketStatusV1,
    PerpsMarginStateV1,
)

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "global_claimant_custody_certificate_v1.yaml"

RECORDED_SOURCE_SHA256 = "d7b547e32790828c149fb0e3bdd6b32e11a235bbb67b6cf02eaaff4db2681252"
RECORDED_IR_HASH = "sha256:918526261e71b37c7bf6af05a73a836c72fba86e008258e525b4970fcb75f04c"
RECORDED_FINGERPRINT = "256b0dcbb7c25c9581d6b16db8f2a5b44512d18c9cadf420477d6c63e38dfc86"
RECORDED_ESSO_CODE_HASH = "7f80c6216be85c827e8d1cc2fa08ee3107a74588"

EXPECTED_ACTIONS = {"open_claim", "drain_claim", "deposit_reserve"}
RESERVE_STATE_VARS = {"reserve_d0", "reserve_d1"}
EXPECTED_INVARIANTS = {
    "inv_exact_custody_partition_d0",
    "inv_exact_custody_partition_d1",
    "inv_exact_claimant_domain_liabilities",
    "inv_open_terminals_fit_exact_allocations",
    "inv_accept_requires_exact_bound_evidence",
}


def _document() -> dict[str, object]:
    value = yaml.safe_load(MODEL.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _esso_python() -> str:
    configured = os.environ.get("ZENO_ESSO_PYTHON")
    if configured:
        configured_path = Path(configured)
        if not configured_path.is_file():
            raise RuntimeError(
                f"configured ESSO interpreter is unavailable: {configured_path}"
            )
        return configured
    if importlib.util.find_spec("ESSO") is not None:
        return sys.executable
    raise RuntimeError(
        "ESSO is unavailable; set ZENO_ESSO_PYTHON to the verified interpreter"
    )


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


def _lane_roots(perps_root: int | str = 40_000) -> tuple[LaneStateRootV1, ...]:
    committed_perps_root = _root(perps_root) if type(perps_root) is int else perps_root
    return tuple(
        LaneStateRootV1(
            lane_id,
            _root(41_000 + index),
            True,
            (
                committed_perps_root
                if lane_id is LaneIdV1.PERPS_MARKET
                else _root(42_000 + index)
            ),
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
    reserves: tuple[tuple[str, str, str, int], ...] = (),
    lane_roots: tuple[LaneStateRootV1, ...] | None = None,
) -> GlobalEconomicStateV1:
    holdings = (*custody, *reserves)
    supplies = tuple(
        AssetSupplyV1(
            asset,
            sum(amount for _, row_asset, _, amount in holdings if row_asset == asset),
        )
        for asset in sorted({row[1] for row in holdings})
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
        reserves=_amounts(*reserves),
        terminal_obligations=tuple(sorted(terminals, key=lambda row: row.obligation_id)),
    )


def _accept_static_state(state: GlobalEconomicStateV1) -> str:
    candidate = GlobalEconomicStateEffectRefinementCandidateV1(
        state,
        state,
        GlobalEconomicEffectPlanV1.empty(),
    )
    refinement = refine_global_economic_state_effects_v1(candidate)
    assert refinement.pre_state_root == state.state_root
    assert refinement.post_state_root == state.state_root
    return refinement.refinement_root


def _sat_query_ids(result: dict[str, object]) -> set[str]:
    queries = result["queries"]
    assert isinstance(queries, dict)
    return {
        query_id
        for query_id, query in queries.items()
        if isinstance(query, dict) and query["final_result"] == "sat"
    }


def _assert_exact_two_solver_counterexample(
    result: dict[str, object],
    *,
    expected_query_id: str,
) -> None:
    assert result["ok"] is False
    assert _sat_query_ids(result) == {expected_query_id}
    queries = result["queries"]
    assert isinstance(queries, dict)
    query = queries[expected_query_id]
    assert isinstance(query, dict)
    assert query["final_result"] == "sat"
    assert query["agreed"] is True
    for solver in ("z3", "cvc5"):
        solver_result = query[solver]
        assert isinstance(solver_result, dict)
        assert solver_result["result"] == "sat"
        assert solver_result["model"] is not None


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
        "current no-unclassified profile",
        "Reserves are modelled as inert named atoms",
        "reserve can never stand in for missing custody",
        "Exact reserve reconciliation remains open",
        "caller-provided true Boolean would not be authority",
        "deposit_reserve accepts without bindings",
        "does not prove current V1 runtime refinement",
        "settlement authority",
        "ABI extension remains required",
    ):
        assert phrase in notes


def test_exact_partition_model_has_no_unclassified_or_reserve_escape_hatch() -> None:
    document = _document()
    invariants = {row["id"]: row for row in document["invariants"]}
    for domain in ("d0", "d1"):
        partition = invariants[f"inv_exact_custody_partition_{domain}"]["expr"]
        assert partition["op"] == "="
        assert partition["args"][0] == {"var": f"custody_{domain}"}
        assert partition["args"][1] == {
            "op": "+",
            "args": [
                {"var": f"allocation_alice_{domain}"},
                {"var": f"allocation_bob_{domain}"},
            ],
        }

    # Reserves exist only as inert state: no invariant, no guard or update of the claimant
    # actions, and no observable-free hiding place may mention them.
    claimed_invariants = json.dumps(document["invariants"], sort_keys=True)
    assert "reserve_" not in claimed_invariants
    state_ids = {row["id"] for row in document["state_vars"]}
    assert RESERVE_STATE_VARS <= state_ids
    assert RESERVE_STATE_VARS <= set(document["observables"]["state_vars"])
    assert {f"allocation_{claimant}_{domain}" for claimant in ("alice", "bob") for domain in ("d0", "d1")} <= set(
        document["observables"]["state_vars"]
    )
    for action in document["actions"]:
        text = json.dumps({"guard": action["guard"], "updates": action["updates"]}, sort_keys=True)
        if action["id"] == "deposit_reserve":
            assert {row["var"] for row in action["updates"]} == RESERVE_STATE_VARS
            assert "custody_" not in text and "allocation_" not in text and "liability_" not in text and "open_" not in text
        else:
            assert "reserve_" not in text, action["id"]
    surface = json.dumps({"state_vars": document["state_vars"], "invariants": document["invariants"]}, sort_keys=True)
    assert "unclassified_" not in surface
    assert "g_pre_" not in surface


def test_ir_hash_binds_the_observable_surface(tmp_path: Path) -> None:
    """Dropping one observable changes the model ir_hash the packet pins (observables are ABI)."""

    document = _document()
    observables = list(document["observables"]["state_vars"])
    document["observables"]["state_vars"] = [name for name in observables if name != "allocation_alice_d0"]
    variant = tmp_path / "hidden_allocation.yaml"
    variant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    rc, result = _run_esso(_esso_python(), "validate", str(variant))
    assert rc == 0 and result["ok"] is True
    assert result["ir_hash"] != RECORDED_IR_HASH


def test_runtime_rejects_aggregate_only_cross_domain_backing() -> None:
    aggregate_only = _state(
        custody=(("account-bob", "USD", "domain-1", 2),),
        liabilities=(("alice", "USD", "domain-0", 2),),
        terminals=(),
    )
    assert sum(row.amount_atoms for row in aggregate_only.custody) == sum(
        row.amount_atoms for row in aggregate_only.liabilities
    )

    with pytest.raises(
        ValueError,
        match="liabilities exceed same-domain custody backing",
    ):
        _accept_static_state(aggregate_only)


def test_runtime_rejects_reserve_masking_as_claimant_backing() -> None:
    reserve_masked = _state(
        custody=(),
        liabilities=(("alice", "USD", "perps-margin", 1),),
        terminals=(),
        reserves=(("protocol-reserve", "USD", "perps-margin", 1),),
    )
    assert sum(row.amount_atoms for row in reserve_masked.reserves) == sum(
        row.amount_atoms for row in reserve_masked.liabilities
    )

    with pytest.raises(
        ValueError,
        match="liabilities exceed same-domain custody backing",
    ):
        _accept_static_state(reserve_masked)


def test_configured_esso_interpreter_missing_fails_closed(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    missing = tmp_path / "missing-esso-python"
    monkeypatch.setenv("ZENO_ESSO_PYTHON", str(missing))

    with pytest.raises(RuntimeError, match="configured ESSO interpreter is unavailable"):
        _esso_python()


def test_esso_two_solver_replay_is_exact_and_deterministic() -> None:
    python = _esso_python()

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
        "inductive_deposit_reserve",
    }
    assert report["total_queries"] == 4 and report["passed_queries"] == 4


SUFFICIENT_INVARIANT_SUPPORT = {
    "inv_exact_custody_partition_d0": set(),
    "inv_exact_custody_partition_d1": set(),
    "inv_exact_claimant_domain_liabilities": set(),
    "inv_open_terminals_fit_exact_allocations": set(),
    "inv_accept_requires_exact_bound_evidence": set(),
}


@pytest.mark.parametrize("invariant_id", sorted(EXPECTED_INVARIANTS))
def test_each_invariant_has_a_sufficient_inductive_solver_projection(
    tmp_path: Path,
    invariant_id: str,
) -> None:
    document = _document()
    selected_ids = {invariant_id, *SUFFICIENT_INVARIANT_SUPPORT[invariant_id]}
    selected = [row for row in document["invariants"] if row["id"] in selected_ids]
    assert {row["id"] for row in selected} == selected_ids
    document["invariants"] = selected
    projection = tmp_path / f"{invariant_id}.yaml"
    projection.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    python = _esso_python()

    rc, result = _run_esso(
        python,
        "verify-multi",
        str(projection),
        "--solvers",
        "z3,cvc5",
        "--determinism-trials",
        "2",
        "--timeout-ms",
        "10000",
    )

    assert rc == 0 and result["ok"] is True, json.dumps(result, indent=2, sort_keys=True)
    assert result["report"]["verdict"] == "VERIFIED"
    assert result["report"]["failed_queries"] == 0
    assert result["report"]["inconclusive_queries"] == 0
    assert result["report"]["solvers_agreed"] is True


@pytest.mark.parametrize(
    (
        "needle",
        "replacement",
        "named_disaster",
        "expected_query_id",
        "attributed_invariant",
    ),
    (
        pytest.param(
            'args:\n        - { param: "global_root_bound" }\n        - { param: "lane_projection_root_bound" }',
            'args:\n        - { bool: true }\n        - { param: "lane_projection_root_bound" }',
            "accept_without_global_root_binding",
            "inductive_open_claim",
            "inv_accept_requires_exact_bound_evidence",
            id="accept_without_global_root_binding",
        ),
        pytest.param(
            '- var: "custody_d0"\n        expr:\n          op: "ite"\n          cond: { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }\n          then: { op: "+", args: [{ var: "custody_d0" }, { param: "amount" }] }',
            '- var: "custody_d0"\n        expr:\n          op: "ite"\n          cond: { op: "=", args: [{ param: "domain" }, { enum: "D1" }] }\n          then: { op: "+", args: [{ var: "custody_d0" }, { param: "amount" }] }',
            "cross_domain_custody_substitution",
            "inductive_open_claim",
            "inv_exact_custody_partition_d0",
            id="cross_domain_custody_substitution",
        ),
        pytest.param(
            '- var: "liability_alice_d0"\n        expr:\n          op: "ite"\n          cond: { op: "and", args: [{ op: "=", args: [{ param: "claimant" }, { enum: "ALICE" }] }, { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }] }\n          then: { op: "+", args: [{ var: "liability_alice_d0" }, { param: "amount" }] }',
            '- var: "liability_alice_d0"\n        expr:\n          op: "ite"\n          cond: { op: "and", args: [{ op: "=", args: [{ param: "claimant" }, { enum: "BOB" }] }, { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }] }\n          then: { op: "+", args: [{ var: "liability_alice_d0" }, { param: "amount" }] }',
            "claimant_column_substitution",
            "inductive_open_claim",
            "inv_exact_claimant_domain_liabilities",
            id="claimant_column_substitution",
        ),
        pytest.param(
            '- var: "open_alice_d0"\n        expr:\n          op: "ite"\n          cond: { op: "and", args: [{ op: "=", args: [{ param: "claimant" }, { enum: "ALICE" }] }, { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }] }\n          then: { op: "+", args: [{ var: "open_alice_d0" }, { param: "amount" }] }',
            '- var: "open_alice_d0"\n        expr:\n          op: "ite"\n          cond: { op: "and", args: [{ op: "=", args: [{ param: "claimant" }, { enum: "ALICE" }] }, { op: "=", args: [{ param: "domain" }, { enum: "D1" }] }] }\n          then: { op: "+", args: [{ var: "open_alice_d0" }, { param: "amount" }] }',
            "terminal_domain_erasure",
            "inductive_open_claim",
            "inv_open_terminals_fit_exact_allocations",
            id="terminal_domain_erasure",
        ),
        pytest.param(
            '- var: "custody_d0"\n        expr:\n          op: "ite"\n          cond: { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }\n          then: { op: "-", args: [{ var: "custody_d0" }, { param: "amount" }] }',
            '- var: "custody_d0"\n        expr:\n          op: "ite"\n          cond: { op: "=", args: [{ param: "domain" }, { enum: "D1" }] }\n          then: { op: "-", args: [{ var: "custody_d0" }, { param: "amount" }] }',
            "drain_cross_domain_custody_substitution",
            "inductive_drain_claim",
            "inv_exact_custody_partition_d0",
            id="drain_cross_domain_custody_substitution",
        ),
        pytest.param(
            '      - var: "custody_d0"\n        expr:\n          op: "ite"\n          cond: { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }\n          then: { op: "+", args: [{ var: "custody_d0" }, { param: "amount" }] }\n          else: { var: "custody_d0" }\n',
            '      - var: "reserve_d0"\n        expr:\n          op: "ite"\n          cond: { op: "=", args: [{ param: "domain" }, { enum: "D0" }] }\n          then: { op: "+", args: [{ var: "reserve_d0" }, { param: "amount" }] }\n          else: { var: "reserve_d0" }\n',
            "reserve_masking_open_claim",
            "inductive_open_claim",
            "inv_exact_custody_partition_d0",
            id="reserve_masking_open_claim",
        ),
    ),
)
def test_named_semantic_mutants_produce_two_solver_counterexamples(
    tmp_path: Path,
    needle: str,
    replacement: str,
    named_disaster: str,
    expected_query_id: str,
    attributed_invariant: str,
) -> None:
    source = MODEL.read_text(encoding="utf-8")
    assert source.count(needle) >= 1, named_disaster
    mutant = tmp_path / f"{named_disaster}.yaml"
    mutant.write_text(source.replace(needle, replacement, 1), encoding="utf-8")
    python = _esso_python()

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
    assert result["report"]["verdict"] == "FAILED"
    assert result["report"]["failed_queries"] == 1
    assert result["report"]["inconclusive_queries"] == 0
    assert result["report"]["solvers_agreed"] is True
    _assert_exact_two_solver_counterexample(
        result,
        expected_query_id=expected_query_id,
    )

    mutant_document = yaml.safe_load(mutant.read_text(encoding="utf-8"))
    attributed_rows = [
        row
        for row in mutant_document["invariants"]
        if row["id"] == attributed_invariant
    ]
    assert [row["id"] for row in attributed_rows] == [attributed_invariant]
    mutant_document["invariants"] = attributed_rows
    attribution_model = tmp_path / (
        f"{named_disaster}-{attributed_invariant}-attribution.yaml"
    )
    attribution_model.write_text(
        yaml.safe_dump(mutant_document, sort_keys=False),
        encoding="utf-8",
    )
    attribution_rc, attribution = _run_esso(
        python,
        "verify-multi",
        str(attribution_model),
        "--solvers",
        "z3,cvc5",
        "--determinism-trials",
        "2",
        "--timeout-ms",
        "10000",
    )

    assert attribution_rc != 0
    assert attribution["report"]["failed_queries"] == 1
    assert attribution["report"]["inconclusive_queries"] == 0
    assert attribution["report"]["solvers_agreed"] is True
    _assert_exact_two_solver_counterexample(
        attribution,
        expected_query_id=expected_query_id,
    )


def test_v1_terminal_domain_erasure_has_distinct_exact_relation_preimages() -> None:
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
    liabilities_by_domain = {
        row.custody_domain: row.amount_atoms for row in ambiguous.liabilities
    }
    assert terminal.amount_atoms > liabilities_by_domain[hidden_d0[1]]
    assert _accept_static_state(ambiguous) == (
        "0x99c49ccabda238b41785d2587dd509d15e37cb2896ed89941ccbc9f324b0be3b"
    )


def test_v1_accepts_claimant_substitution_against_canonical_perps_projection() -> None:
    account = PerpsMarginAccountV1(
        account_id="acct-bob",
        owner="alice",
        position_base=0,
        entry_price_e8=0,
        collateral_atoms=1,
        nonce=0,
        status=PerpsMarginAccountStatusV1.OPEN,
    )
    lane_state = PerpsMarginStateV1(
        module_release_id=_root(17),
        market_id="market",
        collateral_asset="USD",
        index_price_e8=1,
        maintenance_margin_bps=1,
        depeg_buffer_bps=0,
        max_position_abs=1,
        market_status=PerpsMarginMarketStatusV1.ACTIVE,
        accounts=(account,),
    )
    honest_projection = PerpsMarginLaneProjectionV1(
        lane_state=lane_state,
        balances=(),
        accounting_locations=(
            EconomicAmountV1(
                "acct-bob",
                "USD",
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
                1,
            ),
        ),
        liabilities=(
            EconomicAmountV1(
                "alice",
                "USD",
                PERPS_MARGIN_CUSTODY_DOMAIN_V1,
                1,
            ),
        ),
        supplies=(AssetSupplyV1("USD", 1),),
        terminal_obligations=lane_state.terminal_obligations,
    )
    honest_terminal = honest_projection.terminal_obligations[0]
    substituted_terminal = TerminalObligationV1(
        honest_terminal.obligation_id,
        honest_terminal.lane_id,
        "mallory",
        honest_terminal.asset,
        honest_terminal.amount_atoms,
        honest_terminal.status,
    )
    substituted = _state(
        custody=(("acct-bob", "USD", PERPS_MARGIN_CUSTODY_DOMAIN_V1, 1),),
        liabilities=(("mallory", "USD", PERPS_MARGIN_CUSTODY_DOMAIN_V1, 1),),
        terminals=(substituted_terminal,),
        lane_roots=_lane_roots(perps_root=honest_projection.state_root),
    )

    perps_lane_root = next(
        row for row in substituted.lane_roots if row.lane_id is LaneIdV1.PERPS_MARKET
    )
    assert honest_terminal.claimant == "alice"
    assert substituted_terminal.claimant == "mallory"
    assert perps_lane_root.state_root == honest_projection.state_root
    assert honest_terminal.obligation_id == (
        "0xcbb415722632be964cd5113050c842cdf8d643df256655ff551439c0fd81dc55"
    )
    assert honest_projection.state_root == (
        "0x470e8a0f06841fc48fb1cd93a3417824fcd1eece840458455ee9f8a7f3b16a28"
    )
    assert substituted.state_root == (
        "0x32fe632a765eb2d143be6257bc2bc27c253be6307a160093781a5fd541593bf0"
    )
    assert _accept_static_state(substituted) == (
        "0xc553f2cfb6f028b5679a1cb3a2ccd693d59d6deb0b16c8374cd179fd378f2daa"
    )
