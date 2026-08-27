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

import copy
import json
from collections.abc import Callable
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

CORPUS = load_asset_transfer_refinement_corpus_v1()
CASES_BY_ID = {case.case_id: case for case in CORPUS.cases}
COUNTEREXAMPLE_ID = "precedence-insufficient-balance-over-recipient-overflow-sender-sorts-last"
MIRROR_ID = "precedence-insufficient-balance-over-recipient-overflow-sender-sorts-first"


def _typed_context(raw: dict[str, Any]) -> AssetTransferContextV1:
    return AssetTransferContextV1(
        chain_id=raw["chain_id"],
        deployment_root=raw["deployment_root"],
        profile_root=raw["profile_root"],
        writer_epoch=raw["writer_epoch"],
        module_release_id=raw["module_release_id"],
        command_occurrence_id=raw["command_occurrence_id"],
        subject_id=raw["subject_id"],
        grant_root=raw["grant_root"],
    )


def _typed_state(raw: dict[str, Any]) -> AssetTransferStateV1:
    return AssetTransferStateV1(
        module_release_id=raw["module_release_id"],
        policies=tuple(
            AssetTransferPolicyV1(
                row["asset"], row["fee_owner"], int(row["transfer_fee_atoms"]), row["enabled"]
            )
            for row in raw["policies"]
        ),
        balances=tuple(
            EconomicAmountV1(
                row["owner"], row["asset"], row["custody_domain"], int(row["amount_atoms"])
            )
            for row in raw["balances"]
        ),
        supplies=tuple(
            AssetSupplyV1(row["asset"], int(row["amount_atoms"])) for row in raw["supplies"]
        ),
    )


def _typed_command(raw: dict[str, Any]) -> AssetTransferCommandV1:
    return AssetTransferCommandV1(
        command_kind=raw["command_kind"],
        asset=raw["asset"],
        sender=raw["sender"],
        recipient=raw["recipient"],
        amount_atoms=int(raw["amount_atoms"]),
        max_fee_atoms=int(raw["max_fee_atoms"]),
    )


def _apply(case: RefinementCaseV1) -> tuple[AssetTransferStateV1, AssetTransferResultV1]:
    pre_state = _typed_state(dict(case.pre_state))
    result = transition_asset_transfer_v1(
        _typed_context(dict(case.context)), pre_state, _typed_command(dict(case.command))
    )
    return pre_state, result


def _observed(pre_state: AssetTransferStateV1, result: AssetTransferResultV1) -> dict[str, Any]:
    """Encode the runtime outcome in the exact shape the corpus records."""

    if isinstance(result, AssetTransferRejectedV1):
        return {
            "outcome": "rejected",
            "reject_code": result.code.value,
            "effects_empty": result.effects.is_empty,
            "state_root_unchanged": (
                result.pre_state_root == pre_state.state_root
                and result.post_state_root == pre_state.state_root
            ),
        }
    assert isinstance(result, AssetTransferAcceptedV1)
    conservation = result.effects.asset_conservation[0]
    return {
        "outcome": "accepted",
        "post_balances": [
            {
                "owner": row.owner,
                "asset": row.asset,
                "custody_domain": row.custody_domain,
                "amount_atoms": str(row.amount_atoms),
            }
            for row in result.post_state.balances
        ],
        "effect_rows": [
            {
                "kind": row.kind.value,
                "principal": row.principal,
                "asset": row.asset,
                "custody_domain": row.custody_domain,
                "delta_atoms": str(row.delta_atoms),
            }
            for row in result.effects.rows
        ],
        "fee_conservation": [
            {
                "asset": row.asset,
                "fee_charged_atoms": str(row.fee_charged_atoms),
                "current_allocations_atoms": str(row.current_allocations_atoms),
                "carried_residue_atoms": str(row.carried_residue_atoms),
            }
            for row in result.effects.fee_conservation
        ],
        "asset_conservation": {
            "asset": conservation.asset,
            "owned_and_custodied_pre_atoms": str(conservation.owned_and_custodied_pre_atoms),
            "owned_and_custodied_post_atoms": str(conservation.owned_and_custodied_post_atoms),
            "supply_pre_atoms": str(conservation.supply_pre_atoms),
            "supply_post_atoms": str(conservation.supply_post_atoms),
            "authorized_issue_atoms": str(conservation.authorized_issue_atoms),
            "authorized_burn_atoms": str(conservation.authorized_burn_atoms),
        },
        "occurrence_consumptions": list(result.effects.occurrence_consumptions),
        "external_outbox_enqueue": list(result.effects.external_outbox_enqueue),
    }


def _payload() -> dict[str, Any]:
    return json.loads(CORPUS_PATH.read_text(encoding="utf-8"))


def _case_payload(payload: dict[str, Any], case_id: str) -> dict[str, Any]:
    return next(case for case in payload["cases"] if case["case_id"] == case_id)


def test_committed_corpus_passes_the_independent_oracle() -> None:
    # Arrange / Act
    report = check_asset_transfer_refinement_v1(CORPUS_PATH)

    # Assert
    assert report["ok"] is True, report["findings"]
    assert report["findings"] == []
    assert report["case_count"] == len(CORPUS.cases)
    assert report["accepted_cases"] + report["rejected_cases"] == len(CORPUS.cases)
    assert report["unreachable_codes"] == ["BALANCE_OVERFLOW"]
    assert report["cross_language_counterexamples"] == [COUNTEREXAMPLE_ID]
    assert report["production_authority"] is False
    assert CORPUS.validation_command.startswith("python3 tools/check_asset_transfer_refinement_v1.py")


@pytest.mark.parametrize("case_id", sorted(CASES_BY_ID))
def test_python_transition_refines_every_corpus_case(case_id: str) -> None:
    # Arrange
    case = CASES_BY_ID[case_id]

    # Act
    pre_state, result = _apply(case)

    # Assert
    assert _observed(pre_state, result) == dict(case.expected)


@pytest.mark.parametrize("case_id", sorted(CASES_BY_ID))
def test_repeated_replay_of_the_pure_transition_is_deterministic(case_id: str) -> None:
    # Arrange
    case = CASES_BY_ID[case_id]

    # Act
    observations = [_observed(*_apply(case)) for _ in range(CORPUS.deterministic_replay_repetitions)]

    # Assert
    assert CORPUS.deterministic_replay_repetitions >= 2
    assert all(observation == observations[0] for observation in observations)
    assert observations[0] == dict(case.expected)


@pytest.mark.parametrize(
    "case_id", sorted(case.case_id for case in CORPUS.cases if case.outcome == "rejected")
)
def test_every_rejection_is_an_exact_no_op_with_empty_effects(case_id: str) -> None:
    # Arrange
    case = CASES_BY_ID[case_id]
    pre_root = _typed_state(dict(case.pre_state)).state_root

    # Act
    pre_state, result = _apply(case)

    # Assert
    assert isinstance(result, AssetTransferRejectedV1)
    assert result.code.value == case.reject_code
    assert result.pre_state_root == pre_root
    assert result.post_state_root == pre_root
    assert result.effects.is_empty
    assert result.effects.rows == ()
    assert result.effects.lane_writes == ()
    assert result.effects.occurrence_consumptions == ()
    assert pre_state.state_root == pre_root


@pytest.mark.parametrize(
    "case_id", sorted(case.case_id for case in CORPUS.cases if case.outcome == "accepted")
)
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
    assert pre_state.supply_atoms(asset) == result.post_state.supply_atoms(asset)
    assert result.post_state.supplies == pre_state.supplies
    assert result.post_state.policies == pre_state.policies
    assert all(row.amount_atoms > 0 for row in result.post_state.balances)
    assert result.effects.external_outbox_enqueue == ()
    assert result.effects.lane_writes == (
        LaneWriteV1(LaneIdV1.ASSET_TRANSFER, pre_state.state_root, result.post_state.state_root),
    )
    assert result.module_journal.lane_id is LaneIdV1.ASSET_TRANSFER
    assert sum(row.delta_atoms for row in result.effects.rows if row.kind.value == "ACCOUNT_MOVEMENT") == 0


def test_reject_precedence_is_independent_of_principal_spelling() -> None:
    """Mutation killer: a lexicographic post-balance scan reverses this pair."""

    # Arrange
    mirror, counterexample = CASES_BY_ID[MIRROR_ID], CASES_BY_ID[COUNTEREXAMPLE_ID]

    # Act
    mirror_result = _apply(mirror)[1]
    counterexample_result = _apply(counterexample)[1]

    # Assert
    assert isinstance(mirror_result, AssetTransferRejectedV1)
    assert isinstance(counterexample_result, AssetTransferRejectedV1)
    assert mirror_result.code.value == "INSUFFICIENT_BALANCE"
    assert counterexample_result.code.value == "INSUFFICIENT_BALANCE"
    assert mirror.command["sender"] < mirror.command["recipient"]
    assert counterexample.command["sender"] > counterexample.command["recipient"]
    assert counterexample.rust_observed_code == "BALANCE_OVERFLOW"


def test_accepted_effect_rows_are_canonically_ordered_and_nonzero() -> None:
    """Mutation killer: unsorted or zero-delta effect rows must not survive."""

    # Arrange
    accepted = [case for case in CORPUS.cases if case.outcome == "accepted"]

    # Act / Assert
    assert accepted
    for case in accepted:
        rows = _apply(case)[1].effects.rows
        keys = [row.key for row in rows]
        assert keys == sorted(keys)
        assert len(keys) == len(set(keys))
        assert all(row.delta_atoms != 0 for row in rows)


def test_corpus_states_only_the_bounded_claims_it_checks() -> None:
    # Arrange / Act / Assert
    assert "deterministic_repeated_replay" in CORPUS.checked_observations
    assert not any(
        observation.endswith("_root") or "journal" in observation
        for observation in CORPUS.checked_observations
    )
    assert any("no universal Python/Rust equivalence" in claim for claim in CORPUS.nonclaims)
    assert any("value-moving authority" in claim for claim in CORPUS.nonclaims)
    assert any("accounting-location" in claim for claim in CORPUS.nonclaims)
    assert any("exact bytes" in claim for claim in CORPUS.nonclaims)
    assert CORPUS.unreachable_codes["BALANCE_OVERFLOW"]


def _mutate_duplicate_case_id(payload: dict[str, Any]) -> None:
    payload["cases"][1]["case_id"] = payload["cases"][0]["case_id"]


def _mutate_unknown_corpus_field(payload: dict[str, Any]) -> None:
    payload["opaque_authority"] = True


def _mutate_unknown_case_field(payload: dict[str, Any]) -> None:
    payload["cases"][0]["settlement_hint"] = "yes"


def _mutate_atoms_as_json_int(payload: dict[str, Any]) -> None:
    payload["cases"][0]["command"]["amount_atoms"] = 30


def _mutate_bool_as_writer_epoch(payload: dict[str, Any]) -> None:
    payload["cases"][0]["context"]["writer_epoch"] = True


def _mutate_integral_float_writer_epoch(payload: dict[str, Any]) -> None:
    payload["cases"][0]["context"]["writer_epoch"] = 7.0


def _mutate_int_as_enabled_flag(payload: dict[str, Any]) -> None:
    payload["cases"][0]["pre_state"]["policies"][0]["enabled"] = 1


def _mutate_leading_zero_atoms(payload: dict[str, Any]) -> None:
    payload["cases"][0]["command"]["amount_atoms"] = "030"


def _mutate_signed_atoms(payload: dict[str, Any]) -> None:
    payload["cases"][0]["command"]["amount_atoms"] = "-30"


def _mutate_uppercase_root(payload: dict[str, Any]) -> None:
    payload["cases"][0]["context"]["deployment_root"] = "0x" + "AB" * 32


def _mutate_undeclared_reject_code(payload: dict[str, Any]) -> None:
    _case_payload(payload, "reject-zero-amount")["expected"]["reject_code"] = "NOT_A_CODE"


def _mutate_flipped_reject_code(payload: dict[str, Any]) -> None:
    _case_payload(payload, "reject-zero-amount")["expected"]["reject_code"] = "SELF_TRANSFER"


def _mutate_accepted_post_balance(payload: dict[str, Any]) -> None:
    case = _case_payload(payload, "accept-third-party-fee-baseline")
    case["expected"]["post_balances"][0]["amount_atoms"] = "69"


def _mutate_class_outside_vocabulary(payload: dict[str, Any]) -> None:
    case = payload["cases"][0]
    case["classes"] = sorted([*case["classes"], "zz_undeclared_alias"])


def _mutate_drop_required_boundary_case(payload: dict[str, Any]) -> None:
    payload["cases"] = [
        case for case in payload["cases"] if case["case_id"] != "accept-one-atom-transfer"
    ]


def _mutate_dead_vocabulary_alias(payload: dict[str, Any]) -> None:
    payload["class_vocabulary"] = sorted([*payload["class_vocabulary"], "zz_never_used"])


def _mutate_fee_owner_role(payload: dict[str, Any]) -> None:
    _case_payload(payload, "accept-third-party-fee-baseline")["fee_owner_role"] = "sender"


def _mutate_ambiguous_fee_owner_alias(payload: dict[str, Any]) -> None:
    case = _case_payload(payload, "reject-self-transfer")
    case["pre_state"]["policies"][0]["fee_owner"] = "alice"


def _mutate_unsorted_pre_state_balances(payload: dict[str, Any]) -> None:
    balances = _case_payload(payload, "reject-zero-amount")["pre_state"]["balances"]
    balances[0], balances[1] = balances[1], balances[0]


def _mutate_zero_pre_state_balance(payload: dict[str, Any]) -> None:
    _case_payload(payload, "reject-zero-amount")["pre_state"]["balances"][0]["amount_atoms"] = "0"


def _mutate_balances_above_supply(payload: dict[str, Any]) -> None:
    _case_payload(payload, "reject-zero-amount")["pre_state"]["supplies"][0]["amount_atoms"] = "114"


def _mutate_reordered_precedence(payload: dict[str, Any]) -> None:
    precedence = payload["reject_precedence"]
    precedence[9], precedence[10] = precedence[10], precedence[9]


def _mutate_unreachable_claim_over_a_covered_code(payload: dict[str, Any]) -> None:
    payload["unreachable_codes"].append(
        {"code": "INSUFFICIENT_BALANCE", "reason": "unsupported claim"}
    )


def _mutate_drop_the_counterexample(payload: dict[str, Any]) -> None:
    case = _case_payload(payload, COUNTEREXAMPLE_ID)
    case["cross_language"] = "agree"
    case["rust_observed_code"] = None


def _mutate_nonadjacent_precedence_pair(payload: dict[str, Any]) -> None:
    case = _case_payload(payload, "precedence-self-transfer-over-zero-amount")
    case["precedence_pair"] = ["SELF_TRANSFER", "FEE_LIMIT_EXCEEDED"]


def _mutate_drop_a_pair_witness(payload: dict[str, Any]) -> None:
    payload["cases"] = [
        case
        for case in payload["cases"]
        if case["case_id"] != "precedence-self-transfer-over-zero-amount"
    ]


def _mutate_remove_the_disabled_policy_lure(payload: dict[str, Any]) -> None:
    case = _case_payload(payload, "precedence-unknown-asset-over-disabled-asset")
    case["pre_state"]["policies"][0]["enabled"] = True


def _mutate_nonempty_external_outbox(payload: dict[str, Any]) -> None:
    case = _case_payload(payload, "accept-third-party-fee-baseline")
    case["expected"]["external_outbox_enqueue"] = [{"effect_id": "0x" + "11" * 32}]


def _mutate_claimed_production_authority(payload: dict[str, Any]) -> None:
    payload["authority"]["production_authority"] = True


HOSTILE_MUTATIONS: tuple[tuple[str, Callable[[dict[str, Any]], None], str], ...] = (
    ("duplicate_case_id", _mutate_duplicate_case_id, "duplicate case id"),
    ("unknown_corpus_field", _mutate_unknown_corpus_field, "must carry exactly the fields"),
    ("unknown_case_field", _mutate_unknown_case_field, "must carry exactly the fields"),
    ("atoms_as_json_int", _mutate_atoms_as_json_int, "must be a JSON string"),
    ("bool_as_writer_epoch", _mutate_bool_as_writer_epoch, "exact int type"),
    ("integral_float_writer_epoch", _mutate_integral_float_writer_epoch, "exact int type"),
    ("int_as_enabled_flag", _mutate_int_as_enabled_flag, "must be a JSON boolean"),
    ("leading_zero_atoms", _mutate_leading_zero_atoms, "canonical unsigned base-10 atom string"),
    ("signed_atoms", _mutate_signed_atoms, "canonical unsigned base-10 atom string"),
    ("uppercase_root", _mutate_uppercase_root, "lowercase 0x-prefixed 32-byte hex root"),
    ("undeclared_reject_code", _mutate_undeclared_reject_code, "not a declared reject code"),
    ("flipped_reject_code", _mutate_flipped_reject_code, "drifts from the independent oracle"),
    ("accepted_post_balance", _mutate_accepted_post_balance, "drifts from the independent oracle"),
    ("class_outside_vocabulary", _mutate_class_outside_vocabulary, "outside the closed vocabulary"),
    (
        "drop_required_boundary_case",
        _mutate_drop_required_boundary_case,
        "missing required boundary classes",
    ),
    ("dead_vocabulary_alias", _mutate_dead_vocabulary_alias, "unused aliases"),
    ("fee_owner_role", _mutate_fee_owner_role, "does not match the fee owner alias"),
    ("ambiguous_fee_owner_alias", _mutate_ambiguous_fee_owner_alias, "alias is ambiguous"),
    ("unsorted_pre_state_balances", _mutate_unsorted_pre_state_balances, "must be sorted and unique"),
    ("zero_pre_state_balance", _mutate_zero_pre_state_balance, "rather than carry a zero balance"),
    ("balances_above_supply", _mutate_balances_above_supply, "exceeds supply"),
    ("reordered_precedence", _mutate_reordered_precedence, "must equal the scoped precedence"),
    (
        "unreachable_claim_over_a_covered_code",
        _mutate_unreachable_claim_over_a_covered_code,
        "which the corpus declares unreachable",
    ),
    (
        "drop_the_counterexample",
        _mutate_drop_the_counterexample,
        "must retain the recorded cross-language counterexample",
    ),
    (
        "nonadjacent_precedence_pair",
        _mutate_nonadjacent_precedence_pair,
        "must name adjacent reject classes",
    ),
    ("drop_a_pair_witness", _mutate_drop_a_pair_witness, "has no witness case"),
    (
        "remove_the_disabled_policy_lure",
        _mutate_remove_the_disabled_policy_lure,
        "must carry a disabled-policy lure",
    ),
    ("nonempty_external_outbox", _mutate_nonempty_external_outbox, "must stay empty for this lane"),
    (
        "claimed_production_authority",
        _mutate_claimed_production_authority,
        "must be false for research-only evidence",
    ),
)


@pytest.mark.parametrize(
    ("mutation", "expected_message"),
    [(mutate, message) for _, mutate, message in HOSTILE_MUTATIONS],
    ids=[name for name, _, _ in HOSTILE_MUTATIONS],
)
def test_oracle_fails_closed_on_hostile_fixture_mutations(
    mutation: Callable[[dict[str, Any]], None], expected_message: str
) -> None:
    # Arrange
    payload = copy.deepcopy(_payload())
    mutation(payload)

    # Act / Assert
    with pytest.raises(RefinementCorpusErrorV1, match=expected_message):
        parse_asset_transfer_refinement_corpus_v1(payload)


def test_unmutated_payload_still_parses_so_the_mutations_are_the_cause() -> None:
    # Arrange / Act
    corpus = parse_asset_transfer_refinement_corpus_v1(copy.deepcopy(_payload()))

    # Assert
    assert len(corpus.cases) == len(CORPUS.cases)


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
