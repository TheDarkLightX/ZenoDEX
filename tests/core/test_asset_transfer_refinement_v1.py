"""Bounded Python refinement scenarios for the `ASSET_TRANSFER` corpus.

The corpus and its oracle are specified independently of both runtimes: the
oracle in `tools/check_asset_transfer_refinement_v1.py` never calls a production
transition. These scenarios only adapt the validated fixture into typed values
at the comparison boundary and confront the Python transition with it.

Authority: bounded executable research evidence. No production, settlement,
release, migration, proof, or value-moving authority is created here, and
`custody_domain` remains an accounting-location/control-domain label.
"""

from __future__ import annotations

import json
from collections.abc import Callable, Iterable
from pathlib import Path
from typing import Any

import pytest

from src.core.asset_transfer_module_v1 import (
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectedV1,
    AssetTransferResultV1,
    AssetTransferStateV1,
    transition_asset_transfer_v1,
)
from src.core.global_settlement_types_v1 import (
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
)
from tools.check_asset_transfer_refinement_v1 import (
    CORPUS_PATH,
    RefinementCaseV1,
    RefinementCorpusErrorV1,
    check_asset_transfer_refinement_v1,
    load_asset_transfer_refinement_corpus_v1,
    parse_asset_transfer_refinement_corpus_v1,
)

# Importing this module is itself the unmutated control for the hostile mutations
# below: the committed corpus must load and validate before any test runs.
CORPUS = load_asset_transfer_refinement_corpus_v1()
CASES_BY_ID = {case.case_id: case for case in CORPUS.cases}
ACCEPTED_IDS = sorted(case.case_id for case in CORPUS.cases if case.outcome == "accepted")
REJECTED_IDS = sorted(case.case_id for case in CORPUS.cases if case.outcome == "rejected")

BASE_ID = "accept-third-party-fee-baseline"
ZERO_ID = "reject-zero-amount"
SELF_ID = "reject-self-transfer"
PAIR_ID = "precedence-self-transfer-over-zero-amount"
LURE_ID = "precedence-unknown-asset-over-disabled-asset"
ORDER_FIRST_ID = "precedence-insufficient-balance-over-recipient-overflow-sender-sorts-first"
ORDER_LAST_ID = "precedence-insufficient-balance-over-recipient-overflow-sender-sorts-last"
# Repaired region, its first invalid neighbour one fee atom away, accepted sender delta.
WIDTH_BOUNDARY_PAIRS = (
    ("accept-distinct-fee-owner-exact-i128-min-sender-delta",
     "reject-distinct-debit-one-atom-below-i128-min", -(1 << 127)),
    ("accept-sender-owned-fee-at-i128-max",
     "reject-sender-owned-fee-one-atom-above-i128-max", -((1 << 127) - 1)),
)


_BALANCE_FIELDS = ("owner", "asset", "custody_domain", "amount_atoms")
_EFFECT_FIELDS = ("kind", "principal", "asset", "custody_domain", "delta_atoms")
_FEE_FIELDS = ("asset", "fee_charged_atoms", "current_allocations_atoms", "carried_residue_atoms")
_CONSERVATION_FIELDS = (
    "asset", "owned_and_custodied_pre_atoms", "owned_and_custodied_post_atoms", "supply_pre_atoms",
    "supply_post_atoms", "authorized_issue_atoms", "authorized_burn_atoms",
)


def _typed_state(raw: dict[str, Any]) -> AssetTransferStateV1:
    return AssetTransferStateV1(
        module_release_id=raw["module_release_id"],
        policies=tuple(AssetTransferPolicyV1(r["asset"], r["fee_owner"], int(r["transfer_fee_atoms"]), r["enabled"]) for r in raw["policies"]),
        balances=tuple(EconomicAmountV1(r["owner"], r["asset"], r["custody_domain"], int(r["amount_atoms"])) for r in raw["balances"]),
        supplies=tuple(AssetSupplyV1(r["asset"], int(r["amount_atoms"])) for r in raw["supplies"]),
    )


def _apply(case: RefinementCaseV1) -> tuple[AssetTransferStateV1, AssetTransferResultV1]:
    # The parsed context and command field sets match the typed constructors exactly.
    pre_state = _typed_state(dict(case.pre_state))
    context = AssetTransferContextV1(**dict(case.context))
    command = AssetTransferCommandV1(**dict(case.command))
    return pre_state, transition_asset_transfer_v1(context, pre_state, command)


def _rows(rows: Iterable[Any], fields: tuple[str, ...]) -> list[dict[str, str]]:
    # Project runtime rows onto the exact scalar shape the corpus records.
    return [
        {name: str(getattr(getattr(row, name), "value", getattr(row, name))) for name in fields}
        for row in rows
    ]


def _observed(pre_state: AssetTransferStateV1, result: AssetTransferResultV1) -> dict[str, Any]:
    if isinstance(result, AssetTransferRejectedV1):
        roots = (result.pre_state_root, result.post_state_root)
        return {
            "outcome": "rejected", "reject_code": result.code.value,
            "effects_empty": result.effects.is_empty,
            "state_root_unchanged": all(root == pre_state.state_root for root in roots),
        }
    assert isinstance(result, AssetTransferAcceptedV1)
    effects = result.effects
    return {
        "outcome": "accepted",
        "post_balances": _rows(result.post_state.balances, _BALANCE_FIELDS),
        "effect_rows": _rows(effects.rows, _EFFECT_FIELDS),
        "fee_conservation": _rows(effects.fee_conservation, _FEE_FIELDS),
        "asset_conservation": _rows(effects.asset_conservation, _CONSERVATION_FIELDS)[0],
        "occurrence_consumptions": list(effects.occurrence_consumptions),
        "external_outbox_enqueue": list(effects.external_outbox_enqueue),
    }


def test_committed_corpus_passes_the_independent_oracle() -> None:
    # Arrange / Act
    report = check_asset_transfer_refinement_v1(CORPUS_PATH)

    # Assert
    assert report["ok"] is True, report["findings"]
    assert report["accepted_cases"] + report["rejected_cases"] == report["case_count"] == len(CORPUS.cases)
    assert report["unreachable_codes"] == ["BALANCE_OVERFLOW", "POST_STATE_RESOURCE_BOUND_EXCEEDED"]
    assert report["production_authority"] is False
    assert CORPUS.validation_command.startswith("python3 tools/check_asset_transfer_refinement_v1")


@pytest.mark.parametrize("case_id", sorted(CASES_BY_ID))
def test_python_transition_refines_every_corpus_case_on_every_replay(case_id: str) -> None:
    # Arrange
    case = CASES_BY_ID[case_id]
    repetitions = CORPUS.deterministic_replay_repetitions

    # Act
    observations = [_observed(*_apply(case)) for _ in range(repetitions)]

    # Assert
    assert observations and all(o == dict(case.expected) for o in observations)


@pytest.mark.parametrize("case_id", REJECTED_IDS)
def test_every_rejection_is_an_exact_no_op_with_empty_effects(case_id: str) -> None:
    # Arrange
    case = CASES_BY_ID[case_id]
    pre_root = _typed_state(dict(case.pre_state)).state_root

    # Act
    result = _apply(case)[1]

    # Assert
    assert isinstance(result, AssetTransferRejectedV1)
    assert result.code.value == case.reject_code
    assert result.pre_state_root == pre_root
    assert result.post_state_root == pre_root
    assert result.effects == GlobalEconomicEffectPlanV1.empty()


@pytest.mark.parametrize("case_id", ACCEPTED_IDS)
def test_accepted_cases_conserve_supply_totals_and_bind_the_lane_write(case_id: str) -> None:
    # Arrange
    case = CASES_BY_ID[case_id]
    asset = case.command["asset"]

    # Act
    pre_state, result = _apply(case)

    # Assert
    assert isinstance(result, AssetTransferAcceptedV1)
    pre_total = sum(row.amount_atoms for row in pre_state.balances if row.asset == asset)
    post_total = sum(row.amount_atoms for row in result.post_state.balances if row.asset == asset)
    assert pre_total == post_total
    assert result.post_state.supplies == pre_state.supplies
    assert result.post_state.policies == pre_state.policies
    assert all(row.amount_atoms > 0 for row in result.post_state.balances)
    assert result.effects.external_outbox_enqueue == ()
    assert result.effects.lane_writes == (
        LaneWriteV1(LaneIdV1.ASSET_TRANSFER, pre_state.state_root, result.post_state.state_root),
    )
    assert result.module_journal.lane_id is LaneIdV1.ASSET_TRANSFER
    movements = [row for row in result.effects.rows if row.kind.value == "ACCOUNT_MOVEMENT"]
    assert sum(row.delta_atoms for row in movements) == 0
    keys = [row.key for row in result.effects.rows]
    assert keys == sorted(set(keys))
    assert all(row.delta_atoms != 0 for row in result.effects.rows)


def test_reject_precedence_is_independent_of_principal_spelling() -> None:
    """Mutation killer: a lexicographic post-balance scan reverses one half of this pair."""

    # Arrange
    first, last = CASES_BY_ID[ORDER_FIRST_ID], CASES_BY_ID[ORDER_LAST_ID]

    # Act
    results = (_apply(first)[1], _apply(last)[1])

    # Assert
    assert first.command["sender"] < first.command["recipient"]
    assert last.command["sender"] > last.command["recipient"]
    for result in results:
        assert isinstance(result, AssetTransferRejectedV1)
        assert result.code.value == "INSUFFICIENT_BALANCE"


@pytest.mark.parametrize(
    ("accepted_id", "rejected_id", "sender_delta_atoms"),
    WIDTH_BOUNDARY_PAIRS,
    ids=[pair[0] for pair in WIDTH_BOUNDARY_PAIRS],
)
def test_repaired_width_regions_flip_at_exactly_one_fee_atom(
    accepted_id: str, rejected_id: str, sender_delta_atoms: int
) -> None:
    """Mutation killer: an off-by-one signed width bound flips one half of each pair."""

    # Arrange
    accepted, rejected = CASES_BY_ID[accepted_id], CASES_BY_ID[rejected_id]
    fees = [int(c.pre_state["policies"][0]["transfer_fee_atoms"]) for c in (accepted, rejected)]

    # Act
    accepted_result, rejected_result = _apply(accepted)[1], _apply(rejected)[1]

    # Assert
    assert fees[1] == fees[0] + 1
    assert accepted.command["amount_atoms"] == rejected.command["amount_atoms"]
    assert isinstance(accepted_result, AssetTransferAcceptedV1)
    assert accepted_result.effects.rows[0].delta_atoms == sender_delta_atoms
    assert isinstance(rejected_result, AssetTransferRejectedV1)
    assert rejected_result.code.value == "EFFECT_DELTA_OVERFLOW"


def test_corpus_states_only_the_bounded_claims_it_checks() -> None:
    # Arrange / Act / Assert
    assert "deterministic_repeated_replay" in CORPUS.checked_observations
    assert not any(o.endswith("_root") or "journal" in o for o in CORPUS.checked_observations)
    for fragment in ("no universal Python/Rust equivalence", "value-moving authority",
                     "accounting-location", "exact bytes", "prior_defects records only defects"):
        assert any(fragment in claim for claim in CORPUS.nonclaims), fragment
    assert CORPUS.unreachable_codes["BALANCE_OVERFLOW"]
    assert CORPUS.prior_defects
    for defect in CORPUS.prior_defects:
        assert defect["status"] == "killed_by_this_corpus"
        assert all(case_id in CASES_BY_ID for case_id in defect["regression_case_ids"])


Mutation = Callable[[dict[str, Any]], None]
DRIFT = "drifts from the independent oracle"


def _at(payload: dict[str, Any], case_id: str | None, path: str) -> tuple[Any, Any]:
    """Resolve a dotted path to its container and final key, rooted at a case or the corpus."""

    node: Any = payload
    if case_id is not None:
        node = next(case for case in node["cases"] if case["case_id"] == case_id)
    steps = [int(step) if step.isdigit() else step for step in path.split(".")]
    for step in steps[:-1]:
        node = node[step]
    return node, steps[-1]


def _set(case_id: str | None, path: str, value: Any) -> Mutation:
    def mutate(payload: dict[str, Any]) -> None:
        node, key = _at(payload, case_id, path)
        node[key] = value

    return mutate


def _append(case_id: str | None, path: str, value: Any) -> Mutation:
    def mutate(payload: dict[str, Any]) -> None:
        node, key = _at(payload, case_id, path)
        items = [*node[key], value]
        node[key] = sorted(items) if all(isinstance(item, str) for item in items) else items

    return mutate


def _swap(case_id: str | None, path: str, left: int, right: int) -> Mutation:
    def mutate(payload: dict[str, Any]) -> None:
        node, key = _at(payload, case_id, path)
        node[key][left], node[key][right] = node[key][right], node[key][left]

    return mutate


def _drop_case(case_id: str) -> Mutation:
    def mutate(payload: dict[str, Any]) -> None:
        payload["cases"] = [case for case in payload["cases"] if case["case_id"] != case_id]

    return mutate


HOSTILE_MUTATIONS: dict[str, tuple[Mutation, str]] = {
    "duplicate_case_id": (_set(None, "cases.1.case_id", BASE_ID), "duplicate case id"),
    "unknown_corpus_field": (_set(None, "opaque_authority", True), "carry exactly the fields"),
    "unknown_case_field": (_set(BASE_ID, "settlement_hint", "y"), "carry exactly the fields"),
    "atoms_as_json_int": (_set(BASE_ID, "command.amount_atoms", 30), "must be a JSON string"),
    "bool_as_writer_epoch": (_set(BASE_ID, "context.writer_epoch", True), "exact int type"),
    "float_writer_epoch": (_set(BASE_ID, "context.writer_epoch", 7.0), "exact int type"),
    "int_as_enabled_flag": (_set(BASE_ID, "pre_state.policies.0.enabled", 1), "a JSON boolean"),
    "leading_zero_atoms": (_set(BASE_ID, "command.amount_atoms", "030"), "canonical unsigned"),
    "signed_atoms": (_set(BASE_ID, "command.amount_atoms", "-30"), "canonical unsigned"),
    "uppercase_root": (_set(BASE_ID, "context.grant_root", "0x" + "AB" * 32), "lowercase 0x-pre"),
    "undeclared_reject_code": (_set(ZERO_ID, "expected.reject_code", "N"), "declared reject code"),
    "flipped_reject_code": (_set(ZERO_ID, "expected.reject_code", "SELF_TRANSFER"), DRIFT),
    "accepted_post_balance": (_set(BASE_ID, "expected.post_balances.0.amount_atoms", "69"), DRIFT),
    "accepted_effect_row_order": (_swap(BASE_ID, "expected.effect_rows", 0, 1), DRIFT),
    "class_outside_vocabulary": (_append(BASE_ID, "classes", "zz_alias"), "outside the closed voc"),
    "dead_vocabulary_alias": (_append(None, "class_vocabulary", "zz_unused"), "unused aliases"),
    "drop_required_boundary_case": (_drop_case("accept-one-atom-transfer"), "required boundary"),
    "fee_owner_role": (_set(BASE_ID, "fee_owner_role", "sender"), "match the fee owner alias"),
    "ambiguous_fee_owner": (_set(SELF_ID, "pre_state.policies.0.fee_owner", "alice"), "ambiguous"),
    "unsorted_pre_state_balances": (_swap(ZERO_ID, "pre_state.balances", 0, 1), "sorted and unique"),
    "zero_pre_state_balance": (_set(ZERO_ID, "pre_state.balances.0.amount_atoms", "0"), "zero bal"),
    "balances_above_supply": (_set(ZERO_ID, "pre_state.supplies.0.amount_atoms", "114"), "supply"),
    "reordered_precedence": (_swap(None, "reject_precedence", 9, 10), "the scoped precedence"),
    "unreachable_over_covered_code": (
        _append(None, "unreachable_codes", {"code": "INSUFFICIENT_BALANCE", "reason": "no"}),
        "declares unreachable",
    ),
    "drop_a_prior_defect_regression": (_drop_case(ORDER_LAST_ID), "lost its regression cases"),
    "reopen_a_prior_defect": (_set(None, "prior_defects.0.status", "open"), "prior defect status"),
    "nonadjacent_precedence_pair": (
        _set(PAIR_ID, "precedence_pair", ["SELF_TRANSFER", "FEE_LIMIT_EXCEEDED"]),
        "adjacent reject classes",
    ),
    "drop_a_pair_witness": (_drop_case(PAIR_ID), "has no witness case"),
    "remove_the_disabled_lure": (_set(LURE_ID, "pre_state.policies.0.enabled", True), "lure"),
    "nonempty_external_outbox": (
        _set(BASE_ID, "expected.external_outbox_enqueue", [{"id": "0x11"}]),
        "must stay empty for this lane",
    ),
    "claimed_production_authority": (_set(None, "authority.production_authority", True), "be false"),
}


@pytest.mark.parametrize(
    ("mutation", "expected_message"), HOSTILE_MUTATIONS.values(), ids=HOSTILE_MUTATIONS
)
def test_oracle_fails_closed_on_hostile_fixture_mutations(
    mutation: Mutation, expected_message: str
) -> None:
    # Arrange
    payload = json.loads(CORPUS_PATH.read_text(encoding="utf-8"))
    mutation(payload)

    # Act / Assert
    with pytest.raises(RefinementCorpusErrorV1, match=expected_message):
        parse_asset_transfer_refinement_corpus_v1(payload)


def test_oracle_rejects_duplicate_json_keys_and_unreadable_corpora(tmp_path: Path) -> None:
    # Arrange
    duplicated = tmp_path / "duplicated.json"
    duplicated.write_text('{"schema": "a", "schema": "b"}', encoding="utf-8")
    missing = tmp_path / "absent.json"

    # Act / Assert
    with pytest.raises(RefinementCorpusErrorV1, match="duplicate JSON key: schema"):
        load_asset_transfer_refinement_corpus_v1(duplicated)
    with pytest.raises(RefinementCorpusErrorV1, match="corpus cannot be loaded"):
        load_asset_transfer_refinement_corpus_v1(missing)
    report = check_asset_transfer_refinement_v1(missing)
    assert report["ok"] is False
    assert report["case_count"] == 0


@pytest.mark.parametrize("container_kind", ("list", "dict"))
def test_direct_parser_rejects_python_only_container_subclasses(
    container_kind: str,
) -> None:
    # Arrange
    class ListAlias(list[object]):
        pass

    class DictAlias(dict[str, object]):
        pass

    payload = json.loads(CORPUS_PATH.read_text(encoding="utf-8"))
    expected = payload["cases"][0]["expected"]
    if container_kind == "list":
        expected["post_balances"] = ListAlias(expected["post_balances"])
    else:
        expected["effect_rows"][0] = DictAlias(expected["effect_rows"][0])

    # Act / Assert
    with pytest.raises(RefinementCorpusErrorV1, match="exact JSON values"):
        parse_asset_transfer_refinement_corpus_v1(payload)
