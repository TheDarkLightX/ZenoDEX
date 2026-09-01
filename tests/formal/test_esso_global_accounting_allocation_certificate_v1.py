"""Two-solver ESSO evidence for the bounded GlobalAccountingAllocationCertificateV1 model.

The model (two lanes, one control domain, two claimants, eight atoms per cell)
is the sidecar checker's relation as an inductive contract: every accepted
transition preserves the exact lane partition, the row/table equalities, the
custody aggregate, the terminal bound, the producer gate, and the lane binding
premise, and the normative partition and same-domain backing follow as
inductive invariants. Named semantic mutants must each produce one exact
two-solver counterexample attributed to a single invariant. The runtime link
replays the model's disasters against the Python checker. No verifier,
settlement, release, or production authority is granted.
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

from src.core import global_accounting_allocation_certificate_v1 as cert
from tools import render_global_accounting_allocation_certificate_v1_golden as renderer

ROOT = Path(__file__).resolve().parents[2]
MODEL = ROOT / "src" / "kernels" / "dex" / "global_accounting_allocation_certificate_v1.yaml"

RECORDED_SOURCE_SHA256 = "07caf71835c5e8a6c671f4bcd967cc6c42c0ef77ba5875c56abe41265050a5a8"
RECORDED_IR_HASH = "sha256:d4b31feeb6c9a618fa50e45391e9b1b8ffd88e2c5163a59a5317912b0bfb232b"
RECORDED_FINGERPRINT = "7387e9f8974b2d1ce58406cf9cb3bd2a00af19b80fd26005579e3b454817f519"
RECORDED_ESSO_CODE_HASH = "7f80c6216be85c827e8d1cc2fa08ee3107a74588"

EXPECTED_ACTIONS = {
    "enable_lane",
    "open_entitlement",
    "deposit_reserve",
    "register_external",
    "open_terminal",
    "drain_terminal",
    "disable_lane",
}
EXPECTED_INVARIANTS = {
    "inv_lane_partition_exact",
    "inv_lane_rows_equal_tables",
    "inv_lane_aggregate_equals_custody",
    "inv_terminal_bound_by_entitlement",
    "inv_producer_gate",
    "inv_accept_requires_lane_binding",
    "inv_normative_partition",
    "inv_same_domain_backed",
}
EXPECTED_QUERIES = {"init_implies_inv", *(f"inductive_{action}" for action in EXPECTED_ACTIONS)}


def _document() -> dict[str, object]:
    value = yaml.safe_load(MODEL.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _esso_python() -> str:
    configured = os.environ.get("ZENO_ESSO_PYTHON")
    if configured:
        configured_path = Path(configured)
        if not configured_path.is_file():
            raise RuntimeError(f"configured ESSO interpreter is unavailable: {configured_path}")
        return configured
    if importlib.util.find_spec("ESSO") is not None:
        return sys.executable
    raise RuntimeError("ESSO is unavailable; set ZENO_ESSO_PYTHON to the verified interpreter")


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


def _verify(python: str, model: Path) -> tuple[int, dict[str, object]]:
    return _run_esso(python, "verify-multi", str(model), "--solvers", "z3,cvc5", "--determinism-trials", "2", "--timeout-ms", "10000")


def _sat_query_ids(result: dict[str, object]) -> set[str]:
    queries = result["queries"]
    assert isinstance(queries, dict)
    return {query_id for query_id, query in queries.items() if isinstance(query, dict) and query["final_result"] == "sat"}


def _assert_exact_two_solver_counterexample(result: dict[str, object], *, expected_query_id: str) -> None:
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
    assert hashlib.sha256(MODEL.read_bytes()).hexdigest() == RECORDED_SOURCE_SHA256
    assert document["meta"]["model_id"] == "global_accounting_allocation_certificate_v1"
    assert {row["id"] for row in document["actions"]} == EXPECTED_ACTIONS
    assert {row["id"] for row in document["invariants"]} == EXPECTED_INVARIANTS
    notes = " ".join(document["meta"]["notes"].split())
    for phrase in (
        "one asset, one control domain, two lanes (L0, L1), two claimants",
        "classifies the atoms it controls exactly once",
        "unencumbered reserve with no claimant",
        "A reserve never stands in for a missing claimant entitlement",
        "caller-provided true Boolean would not be authority",
        "does not prove finite-width arithmetic, canonical bytes, roots, current V1 runtime refinement",
        "settlement authority",
        "No lane producer is receipt-backed in the running code",
        "enable_lane models the future receipt-backed producers, not a present capability",
    ):
        assert phrase in notes, phrase


def test_observable_surface_covers_every_state_variable() -> None:
    document = _document()
    state_vars = [row["id"] for row in document["state_vars"]]
    assert document["observables"]["state_vars"] == state_vars
    assert document["observables"]["effects"] == ["accepted", "decision"]
    assert len(state_vars) == 28


def test_ir_hash_binds_the_observable_surface(tmp_path: Path) -> None:
    python = _esso_python()
    rc, validate = _run_esso(python, "validate", str(MODEL))
    assert rc == 0 and validate["ok"] is True and validate["ir_hash"] == RECORDED_IR_HASH
    document = _document()
    document["observables"]["state_vars"] = document["observables"]["state_vars"][:-1]
    narrowed = tmp_path / "narrowed.yaml"
    narrowed.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    rc, narrowed_validate = _run_esso(python, "validate", str(narrowed))
    assert rc == 0 and narrowed_validate["ir_hash"] != RECORDED_IR_HASH
    round_trip = tmp_path / "round_trip.yaml"
    round_trip.write_text(yaml.safe_dump(_document(), sort_keys=False), encoding="utf-8")
    rc, same = _run_esso(python, "validate", str(round_trip))
    assert rc == 0 and same["ir_hash"] == RECORDED_IR_HASH


def test_esso_two_solver_replay_is_exact_and_deterministic() -> None:
    python = _esso_python()
    validate_rc, validate = _run_esso(python, "validate", str(MODEL))
    verify_rc, verify = _verify(python, MODEL)
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
    assert set(verify["queries"]) == EXPECTED_QUERIES
    assert report["total_queries"] == 8 and report["passed_queries"] == 8


@pytest.mark.parametrize("invariant_id", sorted(EXPECTED_INVARIANTS))
def test_each_invariant_is_inductive_on_its_own(tmp_path: Path, invariant_id: str) -> None:
    document = _document()
    document["invariants"] = [row for row in document["invariants"] if row["id"] == invariant_id]
    assert [row["id"] for row in document["invariants"]] == [invariant_id]
    projection = tmp_path / f"{invariant_id}.yaml"
    projection.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    rc, result = _verify(_esso_python(), projection)
    assert rc == 0 and result["ok"] is True, json.dumps(result, indent=2, sort_keys=True)
    assert result["report"]["verdict"] == "VERIFIED"
    assert result["report"]["failed_queries"] == 0
    assert result["report"]["inconclusive_queries"] == 0
    assert result["report"]["solvers_agreed"] is True


def _action(document: dict[str, object], action_id: str) -> dict[str, object]:
    rows = [row for row in document["actions"] if row["id"] == action_id]
    assert len(rows) == 1, action_id
    return rows[0]


def _update(action: dict[str, object], var: str) -> dict[str, object]:
    rows = [row for row in action["updates"] if row["var"] == var]
    assert len(rows) == 1, var
    return rows[0]


def _replace_guard_leaf(action: dict[str, object], leaf: dict[str, object]) -> None:
    args = action["guard"]["args"]
    matches = [index for index, arg in enumerate(args) if arg == leaf]
    assert len(matches) == 1, leaf
    args[matches[0]] = {"bool": True}


def _mutate_reserve_masks_entitlement(document: dict[str, object]) -> None:
    """open_entitlement grows the liability table but routes the atoms into the reserve row."""
    action = _action(document, "open_entitlement")
    update = _update(action, "ent_alice_l0")
    condition = update["expr"]["cond"]
    update["expr"]["then"] = {"var": "ent_alice_l0"}
    action["updates"].append({"var": "reserve_l0", "expr": {"op": "ite", "cond": condition, "then": {"op": "+", "args": [{"var": "reserve_l0"}, {"param": "amount"}]}, "else": {"var": "reserve_l0"}}})


def _mutate_unassigned_atom(document: dict[str, object]) -> None:
    """deposit_reserve grows the controlled atoms without classifying them."""
    _update(_action(document, "deposit_reserve"), "reserve_l0")["expr"] = {"var": "reserve_l0"}


def _mutate_enable_without_receipt(document: dict[str, object]) -> None:
    _replace_guard_leaf(_action(document, "enable_lane"), {"param": "receipt_backed"})


def _mutate_terminal_over_entitlement(document: dict[str, object]) -> None:
    action = _action(document, "open_terminal")
    args = action["guard"]["args"]
    bounds = [index for index, arg in enumerate(args) if arg.get("op") == "<=" and arg["args"][1].get("op") == "ite"]
    assert len(bounds) == 1
    args[bounds[0]] = {"bool": True}


def _mutate_custody_double_count(document: dict[str, object]) -> None:
    update = _update(_action(document, "open_entitlement"), "custody")
    update["expr"] = {"op": "+", "args": [{"var": "custody"}, {"param": "amount"}, {"param": "amount"}]}


def _mutate_disable_with_rows(document: dict[str, object]) -> None:
    action = _action(document, "disable_lane")
    args = action["guard"]["args"]
    emptiness = [index for index, arg in enumerate(args) if arg.get("op") == "ite"]
    assert len(emptiness) == 1
    args[emptiness[0]] = {"bool": True}


def _mutate_external_table_not_summed(document: dict[str, object]) -> None:
    action = _action(document, "register_external")
    before = len(action["updates"])
    action["updates"] = [row for row in action["updates"] if row["var"] != "external"]
    assert len(action["updates"]) == before - 1


def _mutate_accept_without_lane_binding(document: dict[str, object]) -> None:
    _replace_guard_leaf(_action(document, "open_entitlement"), {"param": "lane_root_bound"})


@pytest.mark.parametrize(
    ("mutate", "named_disaster", "expected_query_id", "attributed_invariant"),
    (
        pytest.param(_mutate_reserve_masks_entitlement, "reserve_masks_entitlement", "inductive_open_entitlement", "inv_lane_rows_equal_tables", id="reserve_masks_entitlement"),
        pytest.param(_mutate_unassigned_atom, "unassigned_atom", "inductive_deposit_reserve", "inv_lane_partition_exact", id="unassigned_atom"),
        pytest.param(_mutate_enable_without_receipt, "enable_without_receipt", "inductive_enable_lane", "inv_producer_gate", id="enable_without_receipt"),
        pytest.param(_mutate_terminal_over_entitlement, "terminal_over_entitlement", "inductive_open_terminal", "inv_terminal_bound_by_entitlement", id="terminal_over_entitlement"),
        pytest.param(_mutate_custody_double_count, "custody_double_count", "inductive_open_entitlement", "inv_lane_aggregate_equals_custody", id="custody_double_count"),
        pytest.param(_mutate_disable_with_rows, "disable_with_rows", "inductive_disable_lane", "inv_producer_gate", id="disable_with_rows"),
        pytest.param(_mutate_external_table_not_summed, "external_table_not_summed", "inductive_register_external", "inv_lane_rows_equal_tables", id="external_table_not_summed"),
        pytest.param(_mutate_accept_without_lane_binding, "accept_without_lane_binding", "inductive_open_entitlement", "inv_accept_requires_lane_binding", id="accept_without_lane_binding"),
    ),
)
def test_named_semantic_mutants_produce_two_solver_counterexamples(
    tmp_path: Path,
    mutate: object,
    named_disaster: str,
    expected_query_id: str,
    attributed_invariant: str,
) -> None:
    document = _document()
    mutate(document)
    assert document != _document(), named_disaster
    mutant = tmp_path / f"{named_disaster}.yaml"
    mutant.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    python = _esso_python()
    rc, result = _verify(python, mutant)
    assert rc != 0
    assert result["report"]["verdict"] == "FAILED"
    assert result["report"]["failed_queries"] == 1
    assert result["report"]["inconclusive_queries"] == 0
    assert result["report"]["solvers_agreed"] is True
    _assert_exact_two_solver_counterexample(result, expected_query_id=expected_query_id)
    attributed = [row for row in document["invariants"] if row["id"] == attributed_invariant]
    assert [row["id"] for row in attributed] == [attributed_invariant]
    document["invariants"] = attributed
    attribution_model = tmp_path / f"{named_disaster}-{attributed_invariant}-attribution.yaml"
    attribution_model.write_text(yaml.safe_dump(document, sort_keys=False), encoding="utf-8")
    attribution_rc, attribution = _verify(python, attribution_model)
    assert attribution_rc != 0
    assert attribution["report"]["failed_queries"] == 1
    assert attribution["report"]["inconclusive_queries"] == 0
    assert attribution["report"]["solvers_agreed"] is True
    _assert_exact_two_solver_counterexample(attribution, expected_query_id=expected_query_id)


def test_runtime_rejects_reserve_masking_as_entitlement() -> None:
    """The Python checker's row equality is the runtime form of inv_lane_rows_equal_tables."""

    state = renderer.build_state_v1(
        renderer._spec(custody=[("spot-pool", "USD", "spot-pool", 3)], liabilities=[("alice", "USD", "spot-pool", 3)])
    )
    base = cert.build_registered_empty_certificate_v1(state)
    lane = base.ordered_lane_fragments[0]
    masking = renderer._fragment_with_rows(
        lane,
        controlled_locations=(cert.ControlledLocationRowV1("USD", "spot-pool", "spot-pool", 3),),
        claimant_entitlements=(cert.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", 2),),
        unencumbered_reserves=(cert.UnencumberedReserveRowV1("USD", "protocol", "spot-pool", 1),),
    )
    certificate = renderer._certificate_with_fragments(base, (masking, *base.ordered_lane_fragments[1:]))
    cert._check_exactly_once(certificate)
    with pytest.raises(cert._Reject) as captured:
        cert._check_entitlement_rows(certificate, state)
    assert captured.value.code is cert.AllocationCertificateRejectCodeV1.ENTITLEMENT_ROWS_DRIFT


def test_runtime_rejects_enabled_lane_without_receipt_backed_producer() -> None:
    """The producer gate of the model is the running BLOCKED_LANE_PRODUCER_MISSING check."""

    state = renderer.build_state_v1(renderer._spec(lanes_enabled=renderer.ALL_ENABLED))
    outcome = cert.check_global_accounting_allocation_certificate_v1(cert.build_registered_empty_certificate_v1(state), state)
    assert isinstance(outcome, cert.AllocationCertificateRejectedV1)
    assert outcome.code is cert.AllocationCertificateRejectCodeV1.BLOCKED_LANE_PRODUCER_MISSING
    assert outcome.pre_state_root == outcome.post_state_root == state.state_root
    empty = renderer.build_state_v1(renderer._spec())
    accepted = cert.check_global_accounting_allocation_certificate_v1(cert.build_registered_empty_certificate_v1(empty), empty)
    assert isinstance(accepted, cert.AllocationCertificateAcceptedV1)
