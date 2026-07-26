from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools.check_fcis_authority_snapshot_contract import (
    AUTHORITY_GRAPH_AUTHORITY_PATHS,
    DEFAULT_AUTHORITY_PATHS,
    EXACT_CONSUMERS_AUTHORITY_PATHS,
    EXACT_REPLAY_AUTHORITY_PATHS,
    FINAL_MOUNT_AUTHORITY_PATHS,
    STATE_SUBSTRATE_AUTHORITY_PATHS,
    check_contract,
)

_COMPLIANT = """
from dataclasses import dataclass

FCIS_REQUIRED_REGISTRY_IDS = ("synthetic/enum/v1", "synthetic/record/v1")
FCIS_REGISTERED_REGISTRY_IDS = ("synthetic/enum/v1", "synthetic/record/v1")

@dataclass(frozen=True, slots=True)
class OwnedRecordV1:
    value: int

def exact(value: object) -> int:
    if type(value) is not int:
        raise TypeError("exact int required")
    return value
"""


@pytest.mark.parametrize(
    "path",
    [
        "src/core/dex.py",
        "src/core/fcis_step_evaluation_values.py",
        "src/state/fcis_committed_state_values.py",
        "src/core/fcis_step_evaluator.py",
        "src/core/settlement_strong_validator.py",
        "src/state/legacy_state_snapshots.py",
        "src/state/state_snapshots.py",
        "src/state/perps_aggregate_transitions.py",
        "src/state/fcis_execution_context_admission.py",
    ],
)
def test_default_authority_paths_cover_mounted_and_exact_authority(
    path: str,
) -> None:
    assert Path(path) in DEFAULT_AUTHORITY_PATHS


def test_m5_authority_graph_paths_are_mandatory() -> None:
    required = {
        Path("src/core/fcis_authority_admission.py"),
        Path("src/core/fcis_authority_dispatch.py"),
        Path("src/core/fcis_authority_schema.py"),
        Path("src/core/fcis_commit_bundle_values.py"),
        Path("src/core/fcis_decision_values.py"),
        Path("src/core/fcis_outbox_values.py"),
        Path("src/core/fcis_transition_budget.py"),
        Path("src/core/fcis_transition_values.py"),
        Path("src/state/state_admission_profile.py"),
        Path("src/state/state_snapshot_schema.py"),
    }
    assert required <= set(AUTHORITY_GRAPH_AUTHORITY_PATHS)
    assert required <= set(FINAL_MOUNT_AUTHORITY_PATHS)


def test_e11_profiles_keep_review_units_and_final_mount_distinct() -> None:
    dex = Path("src/core/dex.py")
    mixed_settlement_consumer = Path("src/core/settlement_strong_validator.py")
    legacy = Path("src/state/legacy_state_snapshots.py")
    owned_intent = Path("src/state/intent_snapshots.py")
    intent_registry = Path("src/state/intent_field_registry.py")

    assert dex not in STATE_SUBSTRATE_AUTHORITY_PATHS
    assert mixed_settlement_consumer not in STATE_SUBSTRATE_AUTHORITY_PATHS
    assert legacy not in STATE_SUBSTRATE_AUTHORITY_PATHS
    assert owned_intent not in STATE_SUBSTRATE_AUTHORITY_PATHS
    assert owned_intent in AUTHORITY_GRAPH_AUTHORITY_PATHS
    assert intent_registry in AUTHORITY_GRAPH_AUTHORITY_PATHS
    assert dex not in AUTHORITY_GRAPH_AUTHORITY_PATHS
    assert legacy not in AUTHORITY_GRAPH_AUTHORITY_PATHS
    assert dex in FINAL_MOUNT_AUTHORITY_PATHS
    assert mixed_settlement_consumer in FINAL_MOUNT_AUTHORITY_PATHS
    assert legacy in FINAL_MOUNT_AUTHORITY_PATHS
    assert set(STATE_SUBSTRATE_AUTHORITY_PATHS) < set(FINAL_MOUNT_AUTHORITY_PATHS)
    assert set(AUTHORITY_GRAPH_AUTHORITY_PATHS) < set(FINAL_MOUNT_AUTHORITY_PATHS)


def test_exact_replay_profile_covers_the_m3_relation_and_route_consumer() -> None:
    assert EXACT_REPLAY_AUTHORITY_PATHS == (
        Path("src/core/route_settlement.py"),
        Path("src/core/settlement_strong_validator.py"),
    )
    assert set(EXACT_REPLAY_AUTHORITY_PATHS) < set(FINAL_MOUNT_AUTHORITY_PATHS)


def test_exact_consumers_profile_covers_the_complete_m4_relation() -> None:
    assert EXACT_CONSUMERS_AUTHORITY_PATHS == (
        Path("src/core/fcis_step_evaluator.py"),
        Path("src/core/fcis_state_read_trace_v5.py"),
        Path("src/core/fcis_support_profile_constants_v5.py"),
        Path("src/core/fcis_support_profile_v5.py"),
        Path("src/core/fcis_traced_reads_v5.py"),
        Path("src/core/nonce_batch_transition.py"),
        Path("src/core/route_settlement.py"),
        Path("src/core/settlement_strong_validator.py"),
        Path("src/state/support_root.py"),
        Path("src/integration/fcis_spot_shadow.py"),
    )
    assert set(EXACT_REPLAY_AUTHORITY_PATHS) < set(EXACT_CONSUMERS_AUTHORITY_PATHS)
    assert set(EXACT_CONSUMERS_AUTHORITY_PATHS) < set(FINAL_MOUNT_AUTHORITY_PATHS)


def _exact_consumer_dataflow_source() -> str:
    evaluator = Path(__file__).resolve().parents[2] / "src/core/fcis_step_evaluator.py"
    return evaluator.read_text(encoding="utf-8")


def _run_exact_consumer_source(tmp_path: Path, source: str) -> dict[str, object]:
    relative = Path("src/core/fcis_step_evaluator.py")
    authority = tmp_path / relative
    authority.parent.mkdir(parents=True)
    authority.write_text(source, encoding="utf-8")
    return check_contract(
        repo_root=tmp_path,
        authority_paths=(relative,),
        requirements_path=None,
        test_matrix_paths=(),
        profile="exact-consumers",
    )


def test_exact_consumers_profile_accepts_one_retained_lineage(tmp_path: Path) -> None:
    report = _run_exact_consumer_source(
        tmp_path,
        _exact_consumer_dataflow_source(),
    )

    assert report["ok"] is True


_NONCE_ENTRY_CALL = """    nonce, nonce_read_trace = _nonce_candidate_observed_v5(
        state=state,
        intents=exact_intents,
        context=exact_context,
    )"""
_FEE_ENTRY_CALL = """    fee, complete_read_trace = _fee_candidate_observed_v5(
        state=state,
        settlement=exact_settlement,
        context=exact_context,
        state_read_trace=combined_read_trace,
    )"""


@pytest.mark.parametrize(
    ("anchor", "replacement"),
    [
        (
            "    return exact_settlement, exact_intents",
            "    return settlement, intents",
        ),
        (
            "    exact_settlement, exact_intents = command",
            "    exact_settlement, exact_intents = command; exact_intents = intents",
        ),
        (
            _NONCE_ENTRY_CALL,
            """    _nonce_candidate_observed_v5(
        state=state,
        intents=intents,
        context=exact_context,
    )
"""
            + _NONCE_ENTRY_CALL,
        ),
        (
            _FEE_ENTRY_CALL,
            _FEE_ENTRY_CALL.replace("settlement=exact_settlement", "settlement=settlement"),
        ),
        (
            "        intents=exact_intents,\n        pre_binding=pre_binding,",
            "        intents=intents,\n        pre_binding=pre_binding,",
        ),
        (
            _FEE_ENTRY_CALL,
            """    evaluate_settlement_strong_legacy_committed_for_differential_v1(
        settlement=exact_settlement,
        intents=exact_intents,
    )
"""
            + _FEE_ENTRY_CALL,
        ),
        (
            _FEE_ENTRY_CALL,
            '    reader = exact_intents[0].get_field\n    reader("nonce")\n' + _FEE_ENTRY_CALL,
        ),
        (
            "    material = FCISEvaluatedMaterialV1(\n"
            "        pre_state=state,\n"
            "        settlement=exact_settlement,\n"
            "        intents=exact_intents,\n"
            "        context=exact_context,\n"
            "    )",
            "    material = FCISEvaluatedMaterialV1(\n"
            "        pre_state=state,\n"
            "        settlement=other_settlement,\n"
            "        intents=exact_intents,\n"
            "        context=exact_context,\n"
            "    )",
        ),
        (
            "    return _evaluation_ok_from_evaluator_v1(material, candidate, evidence)",
            "    return FCISStepEvaluationOkV1(\n"
            "        material, replacement_candidate, evidence\n"
            "    )",
        ),
    ],
)
def test_exact_consumers_profile_kills_m4_dataflow_mutations(
    tmp_path: Path,
    anchor: str,
    replacement: str,
) -> None:
    source = _exact_consumer_dataflow_source()
    assert source.count(anchor) == 1
    report = _run_exact_consumer_source(
        tmp_path,
        source.replace(anchor, replacement, 1),
    )

    assert "EXACT_CONSUMER_DATAFLOW" in _codes(report)


@pytest.mark.parametrize(
    ("anchor", "replacement"),
    [
        (
            "    state_source: object,\n    settlement: object,",
            "    balances: object,\n    settlement: object,",
        ),
        (
            "    state = _admit_exact_state_v1(state_source)",
            "    state = state_source",
        ),
        (
            "        oracle=state.oracle,\n        perps=state.perps,\n    )\n    root_preimage =",
            "        oracle=state.oracle,\n    )\n    root_preimage =",
        ),
        (
            "canonical_snapshot_bytes_from_committed_state_v1(",
            "state_root_preimage_with_committed_spot_state_v1(",
        ),
        (
            "        snapshot_commitment=post_root,",
            "        snapshot_commitment=support_root,",
        ),
    ],
)
def test_exact_consumers_profile_kills_aggregate_and_root_mutations(
    tmp_path: Path,
    anchor: str,
    replacement: str,
) -> None:
    source = _exact_consumer_dataflow_source()
    assert source.count(anchor) == 1
    report = _run_exact_consumer_source(
        tmp_path,
        source.replace(anchor, replacement, 1),
    )

    assert "EXACT_CONSUMER_DATAFLOW" in _codes(report)


def test_exact_consumers_profile_kills_post_admission_object_mutation(
    tmp_path: Path,
) -> None:
    source = _exact_consumer_dataflow_source()
    anchor = "    exact_settlement, exact_intents = command"
    assert source.count(anchor) == 1
    report = _run_exact_consumer_source(
        tmp_path,
        source.replace(
            anchor,
            anchor + "\n    object.__setattr__(exact_settlement, 'fills', ())",
            1,
        ),
    )

    assert "OWNED_VALUE_MUTATION_BYPASS" in _codes(report)


def test_exact_consumers_profile_kills_raw_companion_sink_parameter(
    tmp_path: Path,
) -> None:
    source = _exact_consumer_dataflow_source()
    replacement = _FEE_ENTRY_CALL.replace(
        "        context=exact_context,",
        "        context=exact_context,\n        raw_settlement=settlement,",
    )
    assert source.count(_FEE_ENTRY_CALL) == 1
    report = _run_exact_consumer_source(
        tmp_path,
        source.replace(_FEE_ENTRY_CALL, replacement, 1),
    )

    assert "EXACT_CONSUMER_DATAFLOW" in _codes(report)


def test_exact_consumers_profile_kills_pre_admission_raw_alias_override(
    tmp_path: Path,
) -> None:
    source = _exact_consumer_dataflow_source()
    source = source.replace(
        "    command = _admit_exact_command_v1(settlement, intents)",
        "    raw_settlement = settlement\n"
        "    command = _admit_exact_command_v1(settlement, intents)",
        1,
    )
    source = source.replace(
        "    candidate = FCISStepCandidateV1()",
        "    fee = _total_settlement_fees_v1(raw_settlement)\n"
        "    candidate = FCISStepCandidateV1()",
        1,
    )

    report = _run_exact_consumer_source(tmp_path, source)

    assert "EXACT_CONSUMER_DATAFLOW" in _codes(report)


def test_exact_consumers_profile_requires_exact_sink_result_assignment(
    tmp_path: Path,
) -> None:
    source = _exact_consumer_dataflow_source()
    replacement = (
        _FEE_ENTRY_CALL.replace("    fee, complete_read_trace = ", "    ")
        + "\n    fee = _total_settlement_fees_v1(exact_settlement)"
    )
    assert source.count(_FEE_ENTRY_CALL) == 1
    report = _run_exact_consumer_source(
        tmp_path,
        source.replace(_FEE_ENTRY_CALL, replacement, 1),
    )

    assert "EXACT_CONSUMER_DATAFLOW" in _codes(report)


def _run_exact_consumer_leaf_source(
    tmp_path: Path,
    relative: Path,
    source: str,
) -> dict[str, object]:
    authority = tmp_path / relative
    authority.parent.mkdir(parents=True, exist_ok=True)
    authority.write_text(source, encoding="utf-8")
    return check_contract(
        repo_root=tmp_path,
        authority_paths=(relative,),
        requirements_path=None,
        test_matrix_paths=(),
        profile="exact-consumers",
    )


@pytest.mark.parametrize(
    ("relative", "anchor", "replacement"),
    [
        (
            Path("src/core/nonce_batch_transition.py"),
            "        exact_intents = admit_intent_batch(intents)",
            "        admit_intent_batch(intents)\n        exact_intents = intents",
        ),
        (
            Path("src/core/nonce_batch_transition.py"),
            "    if not intents:\n        return observed(IntentNonceBatchOkV1(nonces, None))",
            "    admit_intent_batch(intents)\n"
            "    if not intents:\n        return observed(IntentNonceBatchOkV1(nonces, None))",
        ),
        (
            Path("src/state/support_root.py"),
            "    return _derive_batch_state_support_owned_v1(exact_intents, pools=exact_pools)",
            "    return _derive_batch_state_support_owned_v1(intents, pools=exact_pools)",
        ),
        (
            Path("src/state/support_root.py"),
            "    support = _derive_batch_state_support_owned_v1(intents, pools=pools)",
            "    support = derive_batch_state_support_owned_committed_v1(\n"
            "        intents, pools=pools\n"
            "    )",
        ),
    ],
)
def test_exact_consumers_profile_kills_leaf_consumer_bypasses(
    tmp_path: Path,
    relative: Path,
    anchor: str,
    replacement: str,
) -> None:
    repository_root = Path(__file__).resolve().parents[2]
    source = (repository_root / relative).read_text(encoding="utf-8")
    assert source.count(anchor) == 1

    report = _run_exact_consumer_leaf_source(
        tmp_path,
        relative,
        source.replace(anchor, replacement, 1),
    )

    assert "EXACT_CONSUMER_DATAFLOW" in _codes(report)


def _repo_source(relative: Path) -> str:
    return (Path(__file__).resolve().parents[2] / relative).read_text(encoding="utf-8")


def test_m5_gate_rejects_public_rejection_trace_field(tmp_path: Path) -> None:
    relative = Path("src/core/fcis_step_evaluation_values.py")
    source = _repo_source(relative)
    anchor = "    public_reason: str\n\n    def __post_init__"
    assert source.count(anchor) == 1
    mutated = source.replace(
        anchor,
        "    public_reason: str\n    state_read_trace: object\n\n    def __post_init__",
        1,
    )

    report = _run_exact_consumer_leaf_source(tmp_path, relative, mutated)

    assert "FCIS_SUPPORT_TRACE_V5" in _codes(report)


def test_m5_gate_rejects_bypassed_observed_nonce_sink(tmp_path: Path) -> None:
    source = _exact_consumer_dataflow_source()
    assert source.count(_NONCE_ENTRY_CALL) == 1
    mutated = source.replace(
        _NONCE_ENTRY_CALL,
        _NONCE_ENTRY_CALL.replace(
            "_nonce_candidate_observed_v5",
            "_nonce_candidate_v1",
        ),
        1,
    )

    report = _run_exact_consumer_source(tmp_path, mutated)

    assert "EXACT_CONSUMER_DATAFLOW" in _codes(report)


def test_m5_gate_rejects_bypassed_observed_settlement_sink(tmp_path: Path) -> None:
    source = _exact_consumer_dataflow_source()
    anchor = "    observed = _evaluate_settlement_strong_admitted_observed_v5("
    assert source.count(anchor) == 1
    mutated = source.replace(
        anchor,
        "    observed = _evaluate_settlement_strong_admitted_v1(",
        1,
    )

    report = _run_exact_consumer_source(tmp_path, mutated)

    assert "FCIS_SUPPORT_TRACE_V5" in _codes(report)


def test_m5_gate_rejects_post_state_support_binding(tmp_path: Path) -> None:
    source = _exact_consumer_dataflow_source()
    anchor = "            balances=pre_state.balances,"
    assert source.count(anchor) == 2
    mutated = source.replace(
        anchor,
        "            balances=candidate.state.balances,",
        1,
    )

    report = _run_exact_consumer_source(tmp_path, mutated)

    assert "FCIS_SUPPORT_TRACE_V5" in _codes(report)


def test_m5_gate_rejects_untraced_replay_lookup(tmp_path: Path) -> None:
    relative = Path("src/core/settlement_strong_validator.py")
    source = _repo_source(relative)
    anchor = "    replay_state = pre_replay_state"
    assert source.count(anchor) == 1
    mutated = source.replace(
        anchor,
        anchor + '\n    _ = replay_state.pools["untraced"]',
        1,
    )

    report = _run_exact_consumer_leaf_source(tmp_path, relative, mutated)

    assert "FCIS_SUPPORT_TRACE_V5" in _codes(report)


def test_m5_gate_rejects_observed_reader_importing_declared_support(
    tmp_path: Path,
) -> None:
    relative = Path("src/core/fcis_traced_reads_v5.py")
    source = _repo_source(relative)
    mutated = source + (
        "\nfrom .fcis_support_profile_v5 import _derive_fcis_support_set_v5_admitted\n"
    )

    report = _run_exact_consumer_leaf_source(tmp_path, relative, mutated)

    assert "FCIS_SUPPORT_TRACE_V5" in _codes(report)


def test_exact_replay_profile_rejects_entry_annotation_and_projection_drift(
    tmp_path: Path,
) -> None:
    relative = Path("src/core/settlement_strong_validator.py")
    authority = tmp_path / relative
    authority.parent.mkdir(parents=True)
    authority.write_text(
        """
def _admit_exact_commands_v1(settlement, intents):
    snapshot_settlement(settlement)
    admit_intent_batch(intents)

def evaluate_settlement_strong_committed_v1(*, settlement: object, intents: object,
        pre_balances: object, pre_pools: object, pre_lp_balances: object):
    command = _admit_exact_commands_v1(settlement, intents)
    return _evaluate_settlement_strong_admitted_v1(command)

def _evaluate_settlement_strong_admitted_v1(command):
    return _evaluate_settlement_strong_replay_committed_v1(command)

def _evaluate_settlement_strong_replay_committed_v1(command):
    return _validate_settlement_strong_impl(command)

def _validate_settlement_strong_impl(command):
    return BalanceTable()
""",
        encoding="utf-8",
    )
    report = check_contract(
        repo_root=tmp_path,
        authority_paths=(relative,),
        requirements_path=None,
        test_matrix_paths=(),
        profile="exact-replay",
    )
    codes = _codes(report)
    assert "EXACT_REPLAY_ENTRY_SHAPE" in codes
    assert "EXACT_REPLAY_MUTABLE_PROJECTION" in codes


def _copy_repo_authority_source(tmp_path: Path, relative: Path) -> Path:
    source = Path(__file__).resolve().parents[2] / relative
    authority = tmp_path / relative
    authority.parent.mkdir(parents=True)
    authority.write_bytes(source.read_bytes())
    return authority


def test_exact_replay_profile_rejects_unlisted_compatibility_growth(tmp_path: Path) -> None:
    relative = Path("src/core/route_settlement.py")
    authority = _copy_repo_authority_source(tmp_path, relative)
    authority.write_text(
        authority.read_text(encoding="utf-8")
        + "\ndef unlisted_compatibility(value):\n    return isinstance(value, Mapping)\n",
        encoding="utf-8",
    )
    report = check_contract(
        repo_root=tmp_path,
        authority_paths=(relative,),
        requirements_path=None,
        test_matrix_paths=(),
        profile="exact-replay",
    )
    assert "BROAD_ADMISSION" in _codes(report)
    compatibility = report["compatibility_findings"]
    assert type(compatibility) is list
    assert len(compatibility) == 9


def test_exact_replay_profile_rejects_same_count_compatibility_relocation(
    tmp_path: Path,
) -> None:
    relative = Path("src/core/route_settlement.py")
    authority = _copy_repo_authority_source(tmp_path, relative)
    source = authority.read_text(encoding="utf-8")
    old = "if not isinstance(value, str) or not value:"
    assert source.count(old) == 1
    source = source.replace(old, "if type(value) is not str or not value:", 1)
    source += "\ndef relocated_compatibility(value):\n    return isinstance(value, str)\n"
    authority.write_text(source, encoding="utf-8")

    report = check_contract(
        repo_root=tmp_path,
        authority_paths=(relative,),
        requirements_path=None,
        test_matrix_paths=(),
        profile="exact-replay",
    )

    assert "BROAD_ADMISSION" in _codes(report)
    compatibility = report["compatibility_findings"]
    assert type(compatibility) is list
    assert len(compatibility) == 8


def _exact_replay_dataflow_source(
    *,
    admission_body: str,
    replay_settlement: str,
    replay_intents: str,
) -> str:
    return f"""
def _admit_exact_commands_v1(settlement, intents):
{admission_body}

def evaluate_settlement_strong_committed_v1(*,
        settlement: OwnedSettlementV1,
        intents: tuple[OwnedIntentV1, ...],
        pre_balances: CommittedBalanceTableV1,
        pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
        pre_lp_balances: CommittedLPTableV1,
        now: int,
        min_lp_position_age_seconds: int,
        lp_duration_policy: object,
        mode: str,
        allow_cow_netting: bool,
        allow_snapshot_bound_quote_bindings: bool,
        protocol_fee_share_bps: int,
        protocol_fee_recipient_pubkey: object):
    command = _admit_exact_commands_v1(settlement, intents)
    if type(command) is StrongSettlementRejectV1:
        return command
    exact_settlement, exact_intents = command
    return _evaluate_settlement_strong_admitted_v1(
        settlement={replay_settlement},
        intents={replay_intents},
        pre_balances=pre_balances,
        pre_pools=pre_pools,
        pre_lp_balances=pre_lp_balances,
        now=now,
        min_lp_position_age_seconds=min_lp_position_age_seconds,
        lp_duration_policy=lp_duration_policy,
        mode=mode,
        allow_cow_netting=allow_cow_netting,
        allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )

def _evaluate_settlement_strong_admitted_v1(*,
        settlement: OwnedSettlementV1,
        intents: tuple[OwnedIntentV1, ...],
        pre_balances: CommittedBalanceTableV1,
        pre_pools: OwnedMapV1[str, CommittedPoolStateV1],
        pre_lp_balances: CommittedLPTableV1,
        now: int,
        min_lp_position_age_seconds: int,
        lp_duration_policy: object,
        mode: str,
        allow_cow_netting: bool,
        allow_snapshot_bound_quote_bindings: bool,
        protocol_fee_share_bps: int,
        protocol_fee_recipient_pubkey: object):
    return _evaluate_settlement_strong_replay_committed_v1(
        settlement=settlement,
        intents=intents,
        pre_balances=pre_balances,
        pre_pools=pre_pools,
        pre_lp_balances=pre_lp_balances,
        now=now,
        min_lp_position_age_seconds=min_lp_position_age_seconds,
        lp_duration_policy=lp_duration_policy,
        mode=mode,
        allow_cow_netting=allow_cow_netting,
        allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
        protocol_fee_share_bps=protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
    )

def _evaluate_settlement_strong_replay_committed_v1(**command):
    return _validate_settlement_strong_impl(command)

def _validate_settlement_strong_impl(command):
    return command
"""


@pytest.mark.parametrize(
    ("admission_body", "replay_settlement", "replay_intents"),
    [
        (
            "    snapshot_settlement(settlement)\n"
            "    admit_intent_batch(intents)\n"
            "    return settlement, intents",
            "exact_settlement",
            "exact_intents",
        ),
        (
            "    exact_settlement = snapshot_settlement(settlement)\n"
            "    exact_intents = admit_intent_batch(intents)\n"
            "    return exact_settlement, exact_intents",
            "settlement",
            "intents",
        ),
    ],
)
def test_exact_replay_profile_rejects_ignored_or_raw_admission_dataflow(
    tmp_path: Path,
    admission_body: str,
    replay_settlement: str,
    replay_intents: str,
) -> None:
    relative = Path("src/core/settlement_strong_validator.py")
    authority = tmp_path / relative
    authority.parent.mkdir(parents=True)
    authority.write_text(
        _exact_replay_dataflow_source(
            admission_body=admission_body,
            replay_settlement=replay_settlement,
            replay_intents=replay_intents,
        ),
        encoding="utf-8",
    )

    report = check_contract(
        repo_root=tmp_path,
        authority_paths=(relative,),
        requirements_path=None,
        test_matrix_paths=(),
        profile="exact-replay",
    )

    assert "EXACT_REPLAY_DATAFLOW" in _codes(report)


@pytest.mark.parametrize("mutation", ["raw-admission-return", "raw-replay-call"])
def test_exact_replay_profile_rejects_exact_and_raw_paths_coexisting(
    tmp_path: Path,
    mutation: str,
) -> None:
    source = _exact_replay_dataflow_source(
        admission_body=(
            "    exact_settlement = snapshot_settlement(settlement)\n"
            "    exact_intents = admit_intent_batch(intents)\n"
            "    return exact_settlement, exact_intents"
        ),
        replay_settlement="exact_settlement",
        replay_intents="exact_intents",
    )
    if mutation == "raw-admission-return":
        source = source.replace(
            "    return exact_settlement, exact_intents",
            "    if use_raw:\n"
            "        return settlement, intents\n"
            "    return exact_settlement, exact_intents",
            1,
        )
    else:
        replay_anchor = (
            "    return _evaluate_settlement_strong_admitted_v1(\n"
            "        settlement=exact_settlement,"
        )
        assert source.count(replay_anchor) == 1
        source = source.replace(
            replay_anchor,
            "    if use_raw:\n"
            "        _evaluate_settlement_strong_admitted_v1(\n"
            "            settlement=settlement, intents=intents\n"
            "        )\n" + replay_anchor,
            1,
        )

    relative = Path("src/core/settlement_strong_validator.py")
    authority = tmp_path / relative
    authority.parent.mkdir(parents=True)
    authority.write_text(source, encoding="utf-8")
    report = check_contract(
        repo_root=tmp_path,
        authority_paths=(relative,),
        requirements_path=None,
        test_matrix_paths=(),
        profile="exact-replay",
    )

    assert "EXACT_REPLAY_DATAFLOW" in _codes(report)


@pytest.mark.parametrize("mutation", ["admission-rebind", "entry-rebind"])
def test_exact_replay_profile_rejects_protected_exact_value_rebinding(
    tmp_path: Path,
    mutation: str,
) -> None:
    source = _exact_replay_dataflow_source(
        admission_body=(
            "    exact_settlement = snapshot_settlement(settlement)\n"
            "    exact_intents = admit_intent_batch(intents)\n"
            "    return exact_settlement, exact_intents"
        ),
        replay_settlement="exact_settlement",
        replay_intents="exact_intents",
    )
    if mutation == "admission-rebind":
        anchor = "    return exact_settlement, exact_intents"
        replacement = (
            "    exact_settlement = settlement\n    return exact_settlement, exact_intents"
        )
    else:
        anchor = "    exact_settlement, exact_intents = command"
        replacement = "    exact_settlement, exact_intents = command\n    exact_intents = intents"
    assert source.count(anchor) == 1
    source = source.replace(anchor, replacement, 1)

    relative = Path("src/core/settlement_strong_validator.py")
    authority = tmp_path / relative
    authority.parent.mkdir(parents=True)
    authority.write_text(source, encoding="utf-8")
    report = check_contract(
        repo_root=tmp_path,
        authority_paths=(relative,),
        requirements_path=None,
        test_matrix_paths=(),
        profile="exact-replay",
    )

    assert "EXACT_REPLAY_DATAFLOW" in _codes(report)


@pytest.mark.parametrize(
    "mutation_call",
    [
        "object.__setattr__(exact_settlement, 'included_intents', ())",
        "object.__delattr__(exact_settlement, 'included_intents')",
        "type.__setattr__(OwnedSettlementV1, 'field', 1)",
        "type.__delattr__(OwnedSettlementV1, 'field')",
    ],
)
def test_exact_replay_profile_rejects_post_admission_mutation_bypass(
    tmp_path: Path,
    mutation_call: str,
) -> None:
    source = _exact_replay_dataflow_source(
        admission_body=(
            "    exact_settlement = snapshot_settlement(settlement)\n"
            "    exact_intents = admit_intent_batch(intents)\n"
            "    return exact_settlement, exact_intents"
        ),
        replay_settlement="exact_settlement",
        replay_intents="exact_intents",
    )
    anchor = "    exact_settlement, exact_intents = command"
    assert source.count(anchor) == 1
    source = source.replace(
        anchor,
        f"{anchor}; {mutation_call}",
        1,
    )

    relative = Path("src/core/settlement_strong_validator.py")
    authority = tmp_path / relative
    authority.parent.mkdir(parents=True)
    authority.write_text(source, encoding="utf-8")
    report = check_contract(
        repo_root=tmp_path,
        authority_paths=(relative,),
        requirements_path=None,
        test_matrix_paths=(),
        profile="exact-replay",
    )

    assert "OWNED_VALUE_MUTATION_BYPASS" in _codes(report)


@pytest.mark.parametrize(
    "source",
    [
        """
def snapshot_intent(source: object) -> object:
    projected = tuple(vars(source).items())
    return _admit_graph_value('intent', projected)
""",
        """
def admit_intent_batch(source: object) -> object:
    if type(source) is not list:
        raise TypeError
    admitted = _admit_graph_value('intent-batch', source)
    return admitted
""",
        """
def snapshot_intent(source: object) -> object:
    admitted = _admit_graph_value('intent', source)
    if type(admitted) is not object:
        raise RuntimeError
    return source
""",
        """
def snapshot_intent(source: object) -> object:
    admitted = _admit_graph_value('intent', source)
    if type(admitted) is not object:
        raise RuntimeError
    return project(source)
""",
        """
def snapshot_intent(source: object) -> object:
    admitted = _admit_graph_value('intent', source)
    if type(admitted) is not object:
        raise RuntimeError
    return replacement(admitted)
""",
        """
def _replace_result(function):
    def replacement(source):
        return source
    return replacement

@_replace_result
def snapshot_intent(source: object) -> object:
    admitted = _admit_graph_value('intent', source)
    if type(admitted) is not object:
        raise RuntimeError
    return admitted
""",
        """
from dataclasses import dataclass
@dataclass(frozen=True, slots=True)
class _IntentAdmissionSourceV1:
    value: object
""",
    ],
)
def test_checker_rejects_manual_intent_source_projection(
    tmp_path: Path,
    source: str,
) -> None:
    relative = Path("src/state/intent_snapshots.py")
    authority = tmp_path / relative
    authority.parent.mkdir(parents=True)
    authority.write_text(source, encoding="utf-8")
    report = check_contract(
        repo_root=tmp_path,
        authority_paths=(relative,),
        requirements_path=None,
        test_matrix_paths=(),
    )
    assert "MANUAL_SOURCE_PROJECTION" in _codes(report)


def _run(tmp_path: Path, source: str, *, unrelated: str | None = None):
    authority = tmp_path / "authority.py"
    authority.write_text(source, encoding="utf-8")
    if unrelated is not None:
        (tmp_path / "unrelated.py").write_text(unrelated, encoding="utf-8")
    return check_contract(
        repo_root=tmp_path,
        authority_paths=(Path("authority.py"),),
        requirements_path=None,
        test_matrix_paths=(),
    )


def _codes(report: dict[str, object]) -> set[str]:
    violations = report["violations"]
    assert type(violations) is list
    return {item["code"] for item in violations}


@pytest.mark.parametrize(
    "source",
    [
        "from copy import copy\nvalue = copy({})\n",
        "import copy\nvalue = copy.deepcopy({})\n",
    ],
)
def test_checker_rejects_copy_and_deepcopy(tmp_path: Path, source: str) -> None:
    assert "FORBIDDEN_COPY" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    [
        "from src.state.immutable_collections import deep_freeze\nvalue = deep_freeze(object())\n",
        "import src.state.immutable_collections as immutable_collections\n"
        "value = immutable_collections.deep_freeze(object())\n",
    ],
)
def test_checker_rejects_generic_deep_freeze(
    tmp_path: Path,
    source: str,
) -> None:
    assert "GENERIC_DEEP_FREEZE" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    [
        "class Snapshot:\n    def __init__(self):\n        self._snapshot_sealed = True\n",
        "def seal(value: object) -> None:\n"
        "    object.__setattr__(value, '_snapshot_sealed', True)\n",
    ],
)
def test_checker_rejects_snapshot_seal_flags(
    tmp_path: Path,
    source: str,
) -> None:
    assert "SNAPSHOT_SEAL_FLAG" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    [
        "import pickle\n",
        "import copyreg\n",
        "class Bad:\n    def __reduce__(self):\n        return tuple, ()\n",
        "class Bad:\n    def __deepcopy__(self, memo):\n        return self\n",
    ],
)
def test_checker_rejects_reconstruction_protocols(tmp_path: Path, source: str) -> None:
    assert "FORBIDDEN_RECONSTRUCTION" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    [
        "from typing import Any\ndef admit(value: Any) -> Any:\n    return value\n",
        "import typing\ndef admit(value: typing.Any) -> object:\n    return value\n",
    ],
)
def test_checker_rejects_typing_any(tmp_path: Path, source: str) -> None:
    assert "OPEN_AUTHORITY_TYPE" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "base",
    ["dict", "list", "set", "MutableMapping"],
)
def test_checker_rejects_mutable_committed_bases(tmp_path: Path, base: str) -> None:
    prefix = "from collections.abc import MutableMapping\n" if base == "MutableMapping" else ""
    report = _run(tmp_path, f"{prefix}class CommittedValue({base}):\n    pass\n")
    assert "MUTABLE_BASE" in _codes(report)


@pytest.mark.parametrize(
    "target",
    ["Mapping", "Sequence", "Iterable", "int", "str", "bytes", "Enum"],
)
def test_checker_rejects_broad_isinstance_admission(tmp_path: Path, target: str) -> None:
    if target in {"Mapping", "Sequence", "Iterable"}:
        prefix = f"from collections.abc import {target}\n"
    elif target == "Enum":
        prefix = "from enum import Enum\n"
    else:
        prefix = ""
    source = f"{prefix}def admit(value: object):\n    return isinstance(value, {target})\n"
    assert "BROAD_ADMISSION" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    [
        "from dataclasses import is_dataclass\ndef admit(value):\n    return is_dataclass(value)\n",
        "from enum import Enum\ndef admit(value):\n    return issubclass(type(value), Enum)\n",
    ],
)
def test_checker_rejects_reflective_admission(tmp_path: Path, source: str) -> None:
    assert "REFLECTIVE_ADMISSION" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    (
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def commit(bundle: CommitBundleClaimV1) -> None:\n"
        "    publish(bundle)\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1) -> None:\n"
        "    publish(payload=bundle)\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1) -> None:\n"
        "    candidate = bundle\n"
        "    publish(candidate)\n",
        "from shell import publish as emit\n"
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1) -> None:\n"
        "    emit(bundle)\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "async def verify(bundle: CommitBundleClaimV1) -> None:\n"
        "    await publish(bundle)\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1) -> None:\n"
        "    emit = publish\n"
        "    emit(bundle)\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1 as Bundle\n"
        "def verify(bundle: Bundle) -> None:\n"
        "    publish(bundle)\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1) -> None:\n"
        "    def emit(value):\n"
        "        publish(value)\n"
        "    emit(bundle)\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1) -> None:\n"
        "    emit = lambda value: publish(value)\n"
        "    emit(bundle)\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1) -> None:\n"
        '    getattr(shell, "publish")(bundle)\n',
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1):\n"
        "    return bundle\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1):\n"
        "    return bundle.decision\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1):\n"
        "    return bundle.outbox.records[0]\n",
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify(bundle: CommitBundleClaimV1) -> None:\n"
        "    shell.pending = bundle\n",
    ),
)
def test_checker_rejects_decoded_claim_flow_to_commit_or_publish(
    tmp_path: Path,
    source: str,
) -> None:
    assert "CLAIM_AUTHORITY_ESCAPE" in _codes(_run(tmp_path, source))


def test_checker_allows_claim_only_verification(tmp_path: Path) -> None:
    source = (
        "from src.core.fcis_commit_bundle_values import CommitBundleClaimV1\n"
        "def verify_claim(bundle: CommitBundleClaimV1) -> bool:\n"
        '    return bundle.expected_pre_root.startswith("0x")\n'
    )
    assert "CLAIM_AUTHORITY_ESCAPE" not in _codes(_run(tmp_path, source))


def test_checker_rejects_direct_canonical_claim_byte_construction(tmp_path: Path) -> None:
    source = _COMPLIANT + '\nCanonicalAuthorityClaimBytesV1("x", b"x", object())\n'
    assert "CONSTRUCTION_CALLSITE" in _codes(_run(tmp_path, source))


def test_checker_rejects_object_new_constructor_bypass(tmp_path: Path) -> None:
    report = _run(tmp_path, "value = object.__new__(dict)\n")
    assert "CONSTRUCTOR_BYPASS" in _codes(report)


@pytest.mark.parametrize(
    "source",
    [
        "def freeze(source):\n    return dict(source)\n",
        "def freeze(source):\n    return list(source)\n",
        "def freeze(source):\n    return tuple(source)\n",
    ],
)
def test_checker_rejects_container_coercion_at_authority_boundary(
    tmp_path: Path,
    source: str,
) -> None:
    assert "COERCIVE_CONTAINER_COPY" in _codes(_run(tmp_path, source))


def test_checker_rejects_container_coercion_under_renamed_parameter(
    tmp_path: Path,
) -> None:
    assert "COERCIVE_CONTAINER_COPY" in _codes(
        _run(tmp_path, "def freeze(x):\n    return tuple(x)\n")
    )


def test_checker_rejects_aliased_broad_isinstance(tmp_path: Path) -> None:
    source = (
        "from builtins import isinstance as exact\n"
        "def admit(value: object):\n"
        "    return exact(value, int)\n"
    )
    assert "BROAD_ADMISSION" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    [
        (
            "from src.state.owned_collections import _owned_map_from_admitted\n"
            'value = _owned_map_from_admitted((("k", []),), "v1", "map/v1")\n'
        ),
        (
            "from src.state.owned_collections import _owned_enum_from_admitted\n"
            'value = _owned_enum_from_admitted("v1", 0, 0)\n'
        ),
        (
            "from src.state.owned_collections import "
            "_owned_map_from_canonical_transition_v1\n"
            "value = _owned_map_from_canonical_transition_v1("
            '(("k", 1),), "v1", "map/v1")\n'
        ),
        (
            "from src.state.owned_collections import "
            "_owned_enum_from_canonical_transition_v1\n"
            'value = _owned_enum_from_canonical_transition_v1("v1", 0, 0)\n'
        ),
    ],
)
def test_checker_rejects_owned_factories_outside_interpreter(
    tmp_path: Path,
    source: str,
) -> None:
    assert "OWNED_CONSTRUCTION_ESCAPE" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    [
        ("import src.state.snapshot_combinators as sc\nengine = sc._admit_with_registry_v1\n"),
        ("import src.state.owned_collections as oc\nmake = oc._owned_map_from_admitted\n"),
        ("import src.state.owned_collections as oc\nmake = oc._owned_enum_from_admitted\n"),
        (
            "import src.state.owned_collections as oc\n"
            "make = oc._owned_map_from_canonical_transition_v1\n"
        ),
        (
            "import src.state.owned_collections as oc\n"
            "make = oc._owned_enum_from_canonical_transition_v1\n"
        ),
        ("import src.state.owned_collections as oc\ntoken = oc._OWNED_MAP_CONSTRUCTION_TOKEN\n"),
        ("import src.state.owned_collections as oc\ntoken = oc._OWNED_ENUM_CONSTRUCTION_TOKEN\n"),
        ("import src.state.snapshot_combinators as sc\ntoken = sc._ADMISSION_REGISTRY_TOKEN\n"),
        ("import src.state.snapshot_combinators as sc\ntoken = sc._VALIDATED_LIMITS_TOKEN\n"),
    ],
)
def test_checker_rejects_private_capability_attribute_capture(
    tmp_path: Path,
    source: str,
) -> None:
    assert "PRIVATE_AUTHORITY_IMPORT" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    [
        "from src.core.nonce_batch_transition import "
        "_validate_and_apply_intent_nonce_batch_admitted_v1\n",
        "from src.core.settlement_strong_validator import "
        "_evaluate_settlement_strong_admitted_v1\n",
        "from src.state.support_root import "
        "_compute_support_state_root_for_batch_owned_admitted_v1\n",
    ],
)
def test_checker_rejects_private_admitted_sink_imports_outside_evaluator(
    tmp_path: Path,
    source: str,
) -> None:
    assert "PRIVATE_AUTHORITY_IMPORT" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    [
        (
            "import src.core.nonce_batch_transition as nonce_module\n"
            "name = '_validate_and_apply_intent_nonce_batch_' + 'admitted_v1'\n"
            "sink = getattr(nonce_module, name)\n"
        ),
        (
            "import src.core.nonce_batch_transition as nonce_module\n"
            "def capture_private_sink():\n"
            "    name = '_validate_and_apply_intent_nonce_batch_' + 'admitted_v1'\n"
            "    return getattr(nonce_module, name)\n"
        ),
    ],
)
def test_checker_rejects_computed_private_admitted_sink_getattr(
    tmp_path: Path,
    source: str,
) -> None:
    assert "PRIVATE_AUTHORITY_IMPORT" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "capture",
    [
        "nonce_module.__dict__[name]",
        "vars(nonce_module)[name]",
    ],
)
def test_checker_rejects_private_sink_module_mapping_capture(
    tmp_path: Path,
    capture: str,
) -> None:
    source = (
        "import src.core.nonce_batch_transition as nonce_module\n"
        "prefix = '_validate_and_apply_intent_nonce_batch_'\n"
        "suffix = 'admitted_v1'\n"
        "name = prefix + suffix\n"
        f"sink = {capture}\n"
    )

    assert "PRIVATE_AUTHORITY_IMPORT" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "source",
    [
        (
            "import importlib\n"
            "module_name = 'src.core.nonce_batch_' + 'transition'\n"
            "nonce_module = importlib.import_module(module_name)\n"
        ),
        (
            "import sys\n"
            "module_name = 'src.core.nonce_batch_' + 'transition'\n"
            "nonce_module = sys.modules[module_name]\n"
        ),
        "from src.core import nonce_batch_transition as nonce_module\n",
    ],
)
def test_checker_rejects_private_authority_module_object_capture(
    tmp_path: Path,
    source: str,
) -> None:
    assert "PRIVATE_AUTHORITY_IMPORT" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    ("module", "symbol"),
    [
        ("src.state.snapshot_combinators", "_admit_with_registry_v1"),
        ("src.state.owned_collections", "_owned_map_from_admitted"),
        ("src.state.owned_collections", "_owned_enum_from_admitted"),
        ("src.state.owned_collections", "_owned_map_from_canonical_transition_v1"),
        ("src.state.owned_collections", "_owned_enum_from_canonical_transition_v1"),
        ("src.state.owned_collections", "_OWNED_MAP_CONSTRUCTION_TOKEN"),
        ("src.state.owned_collections", "_OWNED_ENUM_CONSTRUCTION_TOKEN"),
        ("src.state.snapshot_combinators", "_ADMISSION_REGISTRY_TOKEN"),
        ("src.state.snapshot_combinators", "_VALIDATED_LIMITS_TOKEN"),
    ],
)
def test_checker_rejects_private_capability_reflective_capture(
    tmp_path: Path,
    module: str,
    symbol: str,
) -> None:
    source = f"import {module} as target\ncapability = getattr(target, {symbol!r})\n"
    assert "PRIVATE_AUTHORITY_IMPORT" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "expression",
    [
        "vars(target)['_admit_with_registry_v1']",
        "target.__dict__['_admit_with_registry_v1']",
    ],
)
def test_checker_rejects_private_capability_dictionary_capture(
    tmp_path: Path,
    expression: str,
) -> None:
    source = f"import src.state.snapshot_combinators as target\ncapability = {expression}\n"
    # Authority invariant: reflective lookup cannot bypass the import allowlist.
    assert "PRIVATE_AUTHORITY_IMPORT" in _codes(_run(tmp_path, source))


def test_checker_rejects_internal_admission_engine_outside_profile_facade(
    tmp_path: Path,
) -> None:
    source = (
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "result = _admit_with_registry_v1(registry, revision, schema, limits, source, post, encode)\n"
    )
    assert "PROFILE_BINDING_ESCAPE" in _codes(_run(tmp_path, source))


def test_checker_scans_sensitive_calls_outside_explicit_authority_paths(
    tmp_path: Path,
) -> None:
    source_dir = tmp_path / "src" / "integration"
    source_dir.mkdir(parents=True)
    (source_dir / "escape.py").write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "result = _admit_with_registry_v1(registry, revision, schema, limits, source, construct, encode)\n",
        encoding="utf-8",
    )

    report = _run(tmp_path, _COMPLIANT)
    assert "PRIVATE_AUTHORITY_IMPORT" in _codes(report)
    assert "PROFILE_BINDING_ESCAPE" in _codes(report)


@pytest.mark.parametrize(
    "source",
    (
        "from src.integration.fcis_spot_shadow import evaluate_fcis_spot_candidate_shadow_v1\n",
        "from .fcis_spot_shadow import evaluate_fcis_spot_candidate_shadow_v1\n",
        "import src.integration.fcis_spot_shadow\n",
        "import importlib\nshadow = importlib.import_module('src.integration.fcis_spot_shadow')\n",
        "import importlib\n"
        "module_name = 'src.integration.' + 'fcis_spot_shadow'\n"
        "shadow = importlib.import_module(module_name)\n",
        "import importlib\n"
        "shadow = importlib.import_module('src.integration.' + 'fcis_spot_shadow')\n",
        "shadow = __import__('src.integration.fcis_spot_shadow')\n",
    ),
)
def test_checker_rejects_shadow_authority_import_anywhere_in_production(
    tmp_path: Path,
    source: str,
) -> None:
    consumer = tmp_path / "src" / "integration" / "consumer.py"
    consumer.parent.mkdir(parents=True)
    consumer.write_text(source, encoding="utf-8")

    assert "SHADOW_AUTHORITY_IMPORT" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_resolves_parent_relative_shadow_import(
    tmp_path: Path,
) -> None:
    consumer = tmp_path / "src" / "core" / "consumer.py"
    consumer.parent.mkdir(parents=True)
    consumer.write_text(
        "from ..integration.fcis_spot_shadow import evaluate_fcis_spot_candidate_shadow_v1\n",
        encoding="utf-8",
    )

    assert "SHADOW_AUTHORITY_IMPORT" in _codes(_run(tmp_path, _COMPLIANT))


@pytest.mark.parametrize(
    "source",
    (
        "import importlib\n"
        "def load():\n"
        "    module_name = 'src.integration.' + 'fcis_spot_shadow'\n"
        "    return importlib.import_module(module_name)\n",
        "import importlib\n"
        "def load():\n"
        "    return importlib.import_module(MODULE_NAME)\n"
        "MODULE_NAME = 'src.integration.fcis_spot_shadow'\n",
        "import importlib\n"
        "loader = importlib.import_module\n"
        "def load():\n"
        "    return loader('src.integration.fcis_spot_shadow')\n",
    ),
)
def test_checker_rejects_shadow_dynamic_binding_spellings(
    tmp_path: Path,
    source: str,
) -> None:
    consumer = tmp_path / "src" / "core" / "consumer.py"
    consumer.parent.mkdir(parents=True)
    consumer.write_text(source, encoding="utf-8")

    assert "SHADOW_AUTHORITY_IMPORT" in _codes(_run(tmp_path, _COMPLIANT))


@pytest.mark.parametrize(
    "shadow_function",
    (
        "evaluate_fcis_spot_candidate_shadow_v1",
        "evaluate_fcis_step_shadow_v1",
    ),
)
def test_checker_rejects_shadow_authority_through_an_intermediary(
    tmp_path: Path,
    shadow_function: str,
) -> None:
    integration = tmp_path / "src" / "integration"
    integration.mkdir(parents=True)
    (integration / "shadow_adapter.py").write_text(
        f"from src.integration.fcis_spot_shadow import {shadow_function}\n",
        encoding="utf-8",
    )
    (integration / "dex_engine.py").write_text(
        f"from src.integration.shadow_adapter import {shadow_function}\n",
        encoding="utf-8",
    )

    report = _run(tmp_path, _COMPLIANT)
    assert "SHADOW_AUTHORITY_IMPORT" in _codes(report)
    violations = report["violations"]
    assert type(violations) is list
    assert any(
        item["code"] == "SHADOW_AUTHORITY_IMPORT"
        and item["path"] == "src/integration/shadow_adapter.py"
        for item in violations
    )


@pytest.mark.parametrize(
    "source",
    (
        "from src.core.fcis_step_evaluator import evaluate_fcis_step_candidate_v1\n",
        "from .fcis_step_evaluator import evaluate_fcis_step_candidate_v1\n",
        "import src.core.fcis_step_evaluator\n",
        "import importlib\nevaluator = importlib.import_module('src.core.fcis_step_evaluator')\n",
        "import importlib\n"
        "module_name = 'src.core.' + 'fcis_step_evaluator'\n"
        "evaluator = importlib.import_module(module_name)\n",
        "evaluator = __import__('src.core.fcis_step_evaluator')\n",
    ),
)
def test_checker_rejects_unmounted_evaluator_import_in_production(
    tmp_path: Path,
    source: str,
) -> None:
    consumer = tmp_path / "src" / "core" / "consumer.py"
    consumer.parent.mkdir(parents=True)
    consumer.write_text(source, encoding="utf-8")

    assert "UNMOUNTED_EVALUATOR_IMPORT" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_resolves_parent_relative_unmounted_evaluator_import(
    tmp_path: Path,
) -> None:
    consumer = tmp_path / "src" / "integration" / "consumer.py"
    consumer.parent.mkdir(parents=True)
    consumer.write_text(
        "from ..core.fcis_step_evaluator import evaluate_fcis_step_candidate_v1\n",
        encoding="utf-8",
    )

    assert "UNMOUNTED_EVALUATOR_IMPORT" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_unmounted_evaluator_through_an_intermediary(
    tmp_path: Path,
) -> None:
    integration = tmp_path / "src" / "integration"
    integration.mkdir(parents=True)
    (integration / "candidate_adapter.py").write_text(
        "from src.core.fcis_step_evaluator import evaluate_fcis_step_candidate_v1\n",
        encoding="utf-8",
    )
    (integration / "dex_engine.py").write_text(
        "from src.integration.candidate_adapter import evaluate_fcis_step_candidate_v1\n",
        encoding="utf-8",
    )

    report = _run(tmp_path, _COMPLIANT)
    assert "UNMOUNTED_EVALUATOR_IMPORT" in _codes(report)
    violations = report["violations"]
    assert type(violations) is list
    assert any(
        item["code"] == "UNMOUNTED_EVALUATOR_IMPORT"
        and item["path"] == "src/integration/candidate_adapter.py"
        for item in violations
    )


def test_checker_allows_unmounted_evaluator_only_in_shadow_adapter(
    tmp_path: Path,
) -> None:
    shadow = tmp_path / "src" / "integration" / "fcis_spot_shadow.py"
    shadow.parent.mkdir(parents=True)
    shadow.write_text(
        "from ..core.fcis_step_evaluator import evaluate_fcis_step_candidate_v1\n",
        encoding="utf-8",
    )

    assert "UNMOUNTED_EVALUATOR_IMPORT" not in _codes(_run(tmp_path, _COMPLIANT))


@pytest.mark.parametrize(
    "profile_relative_path",
    [
        "src/state/state_admission_profile.py",
        "src/state/lp_duration_policy_admission.py",
        "src/state/fcis_execution_context_admission.py",
    ],
)
def test_checker_allows_internal_engine_only_in_explicit_profile_facades(
    tmp_path: Path,
    profile_relative_path: str,
) -> None:
    profile = tmp_path / profile_relative_path
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "_REGISTRY = object()\n"
        "if _REGISTRY.schema_ids != FCIS_REGISTERED_REGISTRY_IDS:\n"
        "    raise RuntimeError('registry manifest drift')\n"
        "def _construct(tag, fields):\n"
        "    return fields\n"
        "def _encode(schema_id, value):\n"
        "    return b''\n"
        "def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    return _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _construct, _encode)\n",
        encoding="utf-8",
    )

    assert _codes(_run(tmp_path, _COMPLIANT)) == set()


@pytest.mark.parametrize(
    "profile_name",
    (
        "state_admission_profile.py",
        "lp_duration_policy_admission.py",
        "fcis_execution_context_admission.py",
    ),
)
def test_checker_rejects_nested_suffix_profile_spoof(
    tmp_path: Path,
    profile_name: str,
) -> None:
    profile = tmp_path / "src" / "rogue" / "src" / "state" / profile_name
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "result = _admit_with_registry_v1("
        "registry, revision, schema, limits, source, construct, encode)\n",
        encoding="utf-8",
    )

    report = _run(tmp_path, _COMPLIANT)
    assert "PRIVATE_AUTHORITY_IMPORT" in _codes(report)
    assert "PROFILE_BINDING_ESCAPE" in _codes(report)


def test_checker_rejects_internal_engine_in_lookalike_profile(tmp_path: Path) -> None:
    profile = tmp_path / "src" / "state" / "other_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "_REGISTRY = object()\n"
        "def _construct(tag, fields):\n"
        "    return fields\n"
        "def _encode(schema_id, value):\n"
        "    return b''\n"
        "def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    return _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _construct, _encode)\n",
        encoding="utf-8",
    )

    report = _run(tmp_path, _COMPLIANT)
    assert "PRIVATE_AUTHORITY_IMPORT" in _codes(report)
    assert "PROFILE_BINDING_ESCAPE" in _codes(report)


def test_checker_rejects_missing_or_empty_profile_registry(tmp_path: Path) -> None:
    profile = tmp_path / "src" / "state" / "state_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "FCIS_REQUIRED_REGISTRY_IDS = ()\nFCIS_REGISTERED_REGISTRY_IDS = ()\n",
        encoding="utf-8",
    )

    assert "PROFILE_REGISTRY_DRIFT" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_requires_registry_manifest_binding_on_the_engine_registry(
    tmp_path: Path,
) -> None:
    profile = tmp_path / "src" / "state" / "state_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "_REGISTRY = object()\n"
        "def _construct(tag, fields):\n"
        "    return fields\n"
        "def _encode(schema_id, value):\n"
        "    return b''\n"
        "def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    return _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _construct, _encode)\n",
        encoding="utf-8",
    )

    assert "PROFILE_REGISTRY_BINDING" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_manifest_check_bound_to_a_different_registry(
    tmp_path: Path,
) -> None:
    profile = tmp_path / "src" / "state" / "state_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "_REGISTRY = object()\n"
        "_OTHER_REGISTRY = object()\n"
        "if _OTHER_REGISTRY.schema_ids != FCIS_REGISTERED_REGISTRY_IDS:\n"
        "    raise RuntimeError('registry manifest drift')\n"
        "def _construct(tag, fields):\n"
        "    return fields\n"
        "def _encode(schema_id, value):\n"
        "    return b''\n"
        "def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    return _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _construct, _encode)\n",
        encoding="utf-8",
    )

    assert "PROFILE_REGISTRY_BINDING" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_caller_selected_profile_binding(tmp_path: Path) -> None:
    profile = tmp_path / "src" / "state" / "state_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "def admit(schema_revision, schema_id, validated_limits, source, registry, construct, encode):\n"
        "    return _admit_with_registry_v1(registry, schema_revision, schema_id, validated_limits, source, construct, encode)\n",
        encoding="utf-8",
    )

    assert "PROFILE_FACADE_SHAPE" in _codes(_run(tmp_path, _COMPLIANT))


@pytest.mark.parametrize(
    "profile_relative_path",
    [
        "src/state/state_admission_profile.py",
        "src/state/lp_duration_policy_admission.py",
        "src/state/fcis_execution_context_admission.py",
    ],
)
def test_checker_rejects_second_public_entrypoint_in_each_profile(
    tmp_path: Path,
    profile_relative_path: str,
) -> None:
    profile = tmp_path / profile_relative_path
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    return _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _CONSTRUCT, _ENCODE)\n"
        "def admit_custom(source):\n"
        "    return source\n",
        encoding="utf-8",
    )

    assert "PROFILE_FACADE_SHAPE" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_public_profile_binding_class(tmp_path: Path) -> None:
    profile = tmp_path / "src" / "state" / "state_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "class BoundAdmissionV1:\n"
        "    pass\n"
        "def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    return _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _CONSTRUCT, _ENCODE)\n",
        encoding="utf-8",
    )

    # Authority invariant: callers get one function, never a constructible binding object.
    assert "PROFILE_FACADE_SHAPE" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_async_profile_entrypoint(tmp_path: Path) -> None:
    profile = tmp_path / "src" / "state" / "state_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "async def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    return _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _CONSTRUCT, _ENCODE)\n",
        encoding="utf-8",
    )

    assert "PROFILE_FACADE_SHAPE" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_profile_that_discards_engine_result(tmp_path: Path) -> None:
    profile = tmp_path / "src" / "state" / "state_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "_REGISTRY = object()\n"
        "def _construct(tag, fields):\n"
        "    return fields\n"
        "def _encode(schema_id, value):\n"
        "    return b''\n"
        "def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _construct, _encode)\n"
        "    return source\n",
        encoding="utf-8",
    )

    assert "PROFILE_FACADE_SHAPE" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_locally_shadowed_profile_resolver(tmp_path: Path) -> None:
    profile = tmp_path / "src" / "state" / "state_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "_REGISTRY = object()\n"
        "def _encode(schema_id, value):\n"
        "    return b''\n"
        "def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    _construct = source\n"
        "    return _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _construct, _encode)\n",
        encoding="utf-8",
    )

    # A private-looking local name is still caller-selected behavior.
    assert "PROFILE_FACADE_SHAPE" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_undefined_profile_bindings(tmp_path: Path) -> None:
    profile = tmp_path / "src" / "state" / "state_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    return _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _construct, _encode)\n",
        encoding="utf-8",
    )

    assert "PROFILE_FACADE_SHAPE" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_spoofed_constructor_builder_name_in_wrong_module(
    tmp_path: Path,
) -> None:
    source_dir = tmp_path / "src" / "integration"
    source_dir.mkdir(parents=True)
    (source_dir / "escape.py").write_text(
        "def build_admission_registry_v1():\n    return AdmissionRegistryV1()\n",
        encoding="utf-8",
    )

    assert "CONSTRUCTION_CALLSITE" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_behavior_in_declarative_registry_records(
    tmp_path: Path,
) -> None:
    source = (
        "from dataclasses import dataclass\n"
        "from typing import Callable\n"
        "@dataclass(frozen=True, slots=True)\n"
        "class RecordRegistrationV1:\n"
        "    constructor: Callable[[object], object]\n"
    )
    assert "REGISTRY_BEHAVIOR_FIELD" in _codes(_run(tmp_path, source))


def test_checker_rejects_executing_declarative_type_binding(tmp_path: Path) -> None:
    source = "def construct(registration):\n    return registration.owned_type()\n"
    assert "DECLARATIVE_REGISTRY_EXECUTION" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    ("constructor", "allowed_function"),
    [
        ("ValidatedAdmissionLimitsV1", "build_admission_limits_v1"),
        ("AdmissionRegistryV1", "build_admission_registry_v1"),
        ("OwnedMapV1", "_owned_map_from_admitted"),
        ("OwnedEnumV1", "_owned_enum_from_admitted"),
    ],
)
def test_checker_rejects_authority_constructor_outside_allowlisted_function(
    tmp_path: Path,
    constructor: str,
    allowed_function: str,
) -> None:
    source = f"def wrong():\n    return {constructor}()\n"
    report = _run(tmp_path, source)
    assert "CONSTRUCTION_CALLSITE" in _codes(report)
    assert allowed_function in str(report["violations"])


def test_checker_rejects_set_valued_frozen_authority_schema(tmp_path: Path) -> None:
    source = (
        "from dataclasses import dataclass\n"
        "@dataclass(frozen=True, slots=True)\n"
        "class BadSchema:\n"
        "    choices: set[str]\n"
    )
    assert "OPEN_AUTHORITY_SCHEMA" in _codes(_run(tmp_path, source))


def test_checker_rejects_mutable_dataclass_evaluation_state(tmp_path: Path) -> None:
    source = (
        "from dataclasses import dataclass\n"
        "@dataclass(slots=True)\n"
        "class AdmissionContext:\n"
        "    nodes_used: int = 0\n"
    )
    assert "MUTABLE_CORE_STATE" in _codes(_run(tmp_path, source))


@pytest.mark.parametrize(
    "expression",
    [
        "[]",
        "{}",
        "set()",
        "[item for item in source]",
        "{item: item for item in source}",
        "{item for item in source}",
        "list(source)",
        "dict(source)",
    ],
)
def test_checker_rejects_mutable_buffers_under_buffer_free_profile(
    tmp_path: Path,
    expression: str,
) -> None:
    source = (
        "FCIS_MUTABLE_LOCAL_BUFFERS_FORBIDDEN = True\n"
        "def build(source: tuple[object, ...]) -> object:\n"
        f"    candidate = {expression}\n"
        "    return tuple(candidate)\n"
    )

    assert "MUTABLE_LOCAL_BUFFER" in _codes(_run(tmp_path, source))


def test_checker_accepts_tuple_only_buffer_free_profile(tmp_path: Path) -> None:
    source = (
        "FCIS_MUTABLE_LOCAL_BUFFERS_FORBIDDEN = True\n"
        "def build(source: tuple[object, ...]) -> tuple[object, ...]:\n"
        "    return tuple(item for item in source)\n"
    )

    assert _codes(_run(tmp_path, source)) == set()


def test_checker_rejects_public_scratch_conversion_in_core_tree(tmp_path: Path) -> None:
    state_dir = tmp_path / "src" / "state"
    state_dir.mkdir(parents=True)
    (state_dir / "state_transitions.py").write_text(
        "def to_scratch_balances(value: object) -> dict:\n    return {}\n",
        encoding="utf-8",
    )
    assert "MUTABLE_CORE_BOUNDARY" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_structural_view_at_core_boundary(tmp_path: Path) -> None:
    source = (
        "class BalanceView:\n"
        "    pass\n"
        "def apply_delta(state: BalanceView) -> BalanceView:\n"
        "    return state\n"
    )
    assert "STRUCTURAL_CORE_BOUNDARY" in _codes(_run(tmp_path, source))


def test_checker_rejects_legacy_mutable_constructor_in_profile(tmp_path: Path) -> None:
    profile = tmp_path / "src" / "state" / "state_admission_profile.py"
    profile.parent.mkdir(parents=True)
    profile.write_text(
        "from src.state.snapshot_combinators import _admit_with_registry_v1\n"
        "FCIS_REQUIRED_REGISTRY_IDS = ('test/root/v1',)\n"
        "FCIS_REGISTERED_REGISTRY_IDS = ('test/root/v1',)\n"
        "_REGISTRY = object()\n"
        "def _construct(tag, fields):\n"
        "    return BalanceTable()\n"
        "def _encode(schema_id, value):\n"
        "    return b''\n"
        "def admit(schema_revision, schema_id, validated_limits, source):\n"
        "    return _admit_with_registry_v1(_REGISTRY, schema_revision, schema_id, validated_limits, source, _construct, _encode)\n",
        encoding="utf-8",
    )
    assert "LEGACY_MUTABLE_CONSTRUCTION" in _codes(_run(tmp_path, _COMPLIANT))


def test_checker_rejects_registry_drift(tmp_path: Path) -> None:
    source = """
FCIS_REQUIRED_REGISTRY_IDS = ("enum/a", "record/b")
FCIS_REGISTERED_REGISTRY_IDS = ("enum/a",)
"""
    assert "REGISTRY_DRIFT" in _codes(_run(tmp_path, source))


def test_checker_rejects_uncovered_pr477_requirement(tmp_path: Path) -> None:
    authority = tmp_path / "authority.py"
    authority.write_text(_COMPLIANT, encoding="utf-8")
    requirements = tmp_path / "requirements.json"
    requirements.write_text(
        json.dumps(
            {
                "requirements": [
                    {
                        "id": "FCIS-477-999",
                        "pr": 477,
                        "tests": [],
                        "evidence": [],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    report = check_contract(
        repo_root=tmp_path,
        authority_paths=(Path("authority.py"),),
        requirements_path=Path("requirements.json"),
        test_matrix_paths=(),
    )
    assert "UNCOVERED_REQUIREMENT" in _codes(report)


def test_checker_accepts_evidence_only_pr477_process_requirement(
    tmp_path: Path,
) -> None:
    authority = tmp_path / "authority.py"
    authority.write_text(_COMPLIANT, encoding="utf-8")
    requirements = tmp_path / "requirements.json"
    requirements.write_text(
        json.dumps(
            {
                "requirements": [
                    {
                        "id": "FCIS-PROC-999",
                        "pr": 477,
                        "tests": [],
                        "evidence": ["merge-base receipt"],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    report = check_contract(
        repo_root=tmp_path,
        authority_paths=(Path("authority.py"),),
        requirements_path=Path("requirements.json"),
        test_matrix_paths=(),
    )
    assert report["ok"] is True


def test_checker_is_path_scoped_and_deterministic(tmp_path: Path) -> None:
    unrelated = "from copy import deepcopy\nvalue = deepcopy({})\n"
    first = _run(tmp_path, _COMPLIANT, unrelated=unrelated)
    second = _run(tmp_path, _COMPLIANT, unrelated=unrelated)
    assert first == second
    assert first["ok"] is True
    assert first["violations"] == []
    assert list(first) == sorted(first)


def test_checker_reports_syntax_errors_without_escaping(tmp_path: Path) -> None:
    report = _run(tmp_path, "def broken(:\n")
    assert "SYNTAX_ERROR" in _codes(report)
