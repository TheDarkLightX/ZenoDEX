"""P4B0-B tests for the pure legacy-to-exact refinement evaluator."""

from __future__ import annotations

import json
from collections.abc import Callable
from pathlib import Path
from typing import cast

import pytest

from src.core.fcis_legacy_refinement import evaluate_refinement_v1
from src.core.fcis_legacy_refinement_admission import (
    PACKET_COMMIT_V1,
    PACKET_TREE_HASH_V1,
    REQUIRED_ANCESTOR_V1,
    admit_observation_pair_bytes_v1,
)
from src.core.fcis_legacy_refinement_policy import SEMANTIC_STATE_FIELD_ORDER_V1
from src.core.fcis_legacy_refinement_values import (
    InvalidEvidenceV1,
    MismatchV1,
    ObservationPairV1,
    RefinesV1,
)
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

REPO_ROOT = Path(__file__).resolve().parents[2]
DIFFERENTIAL_PATH = REPO_ROOT / "docs/research/FCIS_M5_P4A_DIFFERENTIAL_REPLAY_V1.json"


def _mapping(value: object) -> dict[str, object]:
    assert type(value) is dict
    return cast(dict[str, object], value)


def _sequence(value: object) -> list[object]:
    assert type(value) is list
    return cast(list[object], value)


def _artifact() -> dict[str, object]:
    return _mapping(json.loads(DIFFERENTIAL_PATH.read_bytes()))


def _fixture_source(fixture_id: str) -> dict[str, object]:
    artifact = _artifact()
    selected = next(
        _mapping(fixture)
        for fixture in _sequence(artifact["fixtures"])
        if _mapping(fixture)["fixture_id"] == fixture_id
    )
    command_kind = cast(str, selected["command_kind"])
    input_binding = _mapping(selected["input_binding"])
    comparison = _mapping(selected["comparison"])

    def binding(side: str) -> dict[str, object]:
        raw = _mapping(input_binding[side])
        return {
            "baseline_artifact_hash": artifact["baseline_artifact_sha256"],
            "command_bytes": raw["command_bytes"],
            "command_hash": raw["command_hash"],
            "command_kind": command_kind,
            "context_bytes": raw["context_bytes"],
            "context_hash": raw["context_hash"],
            "differential_artifact_hash": artifact["artifact_sha256"],
            "fixture_id": fixture_id,
            "packet_commit": PACKET_COMMIT_V1,
            "packet_tree_hash": PACKET_TREE_HASH_V1,
            "pre_state_bytes": raw["state_snapshot_bytes"],
            "pre_state_root": raw["state_snapshot_root"],
            "reviewed_start_sha": REQUIRED_ANCESTOR_V1,
        }

    return {
        "exact": {"binding": binding("exact"), "observation": comparison["exact"]},
        "legacy": {"binding": binding("legacy"), "observation": comparison["legacy"]},
    }


def _admit_source(source: dict[str, object]) -> ObservationPairV1:
    result = admit_observation_pair_bytes_v1(canonical_json_bytes(source))
    assert type(result) is ObservationPairV1
    return result


def _evaluate_fixture(fixture_id: str) -> RefinesV1 | MismatchV1 | InvalidEvidenceV1:
    return evaluate_refinement_v1(_admit_source(_fixture_source(fixture_id)))


def _evaluate_source(
    source: dict[str, object],
) -> RefinesV1 | MismatchV1 | InvalidEvidenceV1:
    admitted = admit_observation_pair_bytes_v1(canonical_json_bytes(source))
    if type(admitted) is InvalidEvidenceV1:
        return admitted
    assert type(admitted) is ObservationPairV1
    return evaluate_refinement_v1(admitted)


def _rewrite_component(
    source: dict[str, object],
    field_name: str,
    mutate: Callable[[dict[str, object]], None],
) -> None:
    exact = _mapping(source["exact"])
    observation = _mapping(exact["observation"])
    raw = cast(str, observation[field_name])
    component = _mapping(json.loads(bytes.fromhex(raw)))
    mutate(component)
    observation[field_name] = canonical_json_bytes(component).hex()


def _pop_first_list_field(name: str) -> Callable[[dict[str, object]], None]:
    def mutate(component: dict[str, object]) -> None:
        values = _sequence(component[name])
        assert values
        values.pop(0)

    return mutate


def _change_bundle_support_root(component: dict[str, object]) -> None:
    receipt = _mapping(_mapping(component["decision"])["receipt"])
    binding = _mapping(receipt["binding"])
    binding["support_root"] = "0x" + "01" * 32


def _rewrite_legacy_state(source: dict[str, object], field_name: str) -> None:
    legacy = _mapping(source["legacy"])
    observation = _mapping(legacy["observation"])
    raw = cast(str, observation["next_state_snapshot_bytes"])
    state = _mapping(json.loads(bytes.fromhex(raw)))
    if field_name == "balances":
        first = _mapping(_sequence(state["balances"])[0])
        first["amount"] = cast(int, first["amount"]) + 1
    elif field_name == "fee_accumulator":
        fees = _mapping(state["fee_accumulator"])
        fees["dust"] = cast(int, fees["dust"]) + 1
    elif field_name == "lp_balances":
        first = _mapping(_sequence(state["lp_balances"])[0])
        first["amount"] = cast(int, first["amount"]) + 1
    elif field_name == "nonces":
        first = _mapping(_sequence(state["nonces"])[0])
        first["last_nonce"] = cast(int, first["last_nonce"]) + 1
    elif field_name == "pools":
        first = _mapping(_sequence(state["pools"])[0])
        first["reserve0"] = cast(int, first["reserve0"]) + 1
    elif field_name in {"oracle", "perps", "vault"}:
        state[field_name] = {}
    else:
        raise AssertionError(f"unknown state field {field_name}")
    encoded = canonical_json_bytes(state)
    observation["next_state_snapshot_bytes"] = encoded.hex()
    observation["next_state_snapshot_root"] = sha256_hex(
        domain_sep_bytes("dex_snapshot", version=4) + encoded
    )


def test_p4b0_refine_001_frozen_fixture_verdict_is_21_refines_3_mismatches() -> None:
    """P4B0-REFINE-001, P4B0-RESULT-001."""

    fixture_ids = tuple(
        cast(str, _mapping(fixture)["fixture_id"]) for fixture in _sequence(_artifact()["fixtures"])
    )
    results = {fixture_id: _evaluate_fixture(fixture_id) for fixture_id in fixture_ids}
    refines = {fixture_id for fixture_id, result in results.items() if type(result) is RefinesV1}
    mismatches = {
        fixture_id: result for fixture_id, result in results.items() if type(result) is MismatchV1
    }
    assert len(refines) == 21
    assert set(mismatches) == {
        "add_liquidity_boundary_valid",
        "add_liquidity_smallest_accepted",
        "create_pool_smallest_accepted",
    }
    assert all(result.code == "state_field_mismatch" for result in mismatches.values())
    assert all(result.path == ("next_state", "lp_balances") for result in mismatches.values())
    assert not any(type(result) is InvalidEvidenceV1 for result in results.values())


@pytest.mark.parametrize(
    "fixture_id",
    (
        "add_liquidity_pool_not_found_rejected",
        "create_pool_duplicate_rejected",
        "remove_liquidity_insufficient_lp_rejected",
        "route_exact_in_pool_not_found_rejected",
        "route_exact_out_max_in_too_low_rejected",
        "swap_exact_in_insufficient_balance_rejected",
        "swap_exact_in_missing_nonce_rejected",
        "swap_exact_out_max_in_too_low_rejected",
    ),
)
def test_p4b0_reject_001_all_rejection_mappings_refine(fixture_id: str) -> None:
    """P4B0-REJECT-001."""

    assert type(_evaluate_fixture(fixture_id)) is RefinesV1


@pytest.mark.parametrize(
    ("field_name", "mutate", "expected_code"),
    (
        (
            "patch_bytes",
            _pop_first_list_field("balance_writes"),
            "incomplete_balance_patch",
        ),
        (
            "replay_bytes",
            _pop_first_list_field("nonce_advances"),
            "replay_nonce_advances_mismatch",
        ),
        (
            "commit_plan_bytes",
            lambda value: _sequence(_mapping(value["patch"])["balance_writes"]).pop(0),
            "plan_patch_mismatch",
        ),
        (
            "bundle_bytes",
            _change_bundle_support_root,
            "bundle_receipt_mismatch",
        ),
    ),
)
def test_p4b0_exact_001_substituted_components_fail_closed(
    field_name: str,
    mutate: Callable[[dict[str, object]], None],
    expected_code: str,
) -> None:
    """P4B0-EXACT-001, P4B0-PATCH-001, P4B0-REPLAY-001."""

    source = _fixture_source("swap_exact_in_boundary_valid")
    _rewrite_component(source, field_name, mutate)
    result = evaluate_refinement_v1(_admit_source(source))
    assert type(result) is InvalidEvidenceV1
    assert result.code == expected_code


def test_p4b0_exact_002_nested_hostile_mutation_is_revalidated() -> None:
    """P4B0-IMMUT-002."""

    pair = _admit_source(_fixture_source("swap_exact_in_smallest_accepted"))
    object.__setattr__(pair.exact.observation, "total_swap_fees", 999)
    result = evaluate_refinement_v1(pair)
    assert type(result) is InvalidEvidenceV1
    assert result.code == "pair_source_bytes_mismatch"


def test_p4b0_determinism_001_equal_inputs_return_equal_decisions() -> None:
    """P4B0-TOTAL-001."""

    pair = _admit_source(_fixture_source("route_exact_in_multi_leg_accepted"))
    first = evaluate_refinement_v1(pair)
    second = evaluate_refinement_v1(pair)
    assert first == second
    assert type(first) is RefinesV1


@pytest.mark.parametrize(
    "mutation",
    ("code", "path", "precedence", "public_reason", "committable_output"),
)
def test_p4b0_reject_002_rejection_substitution_fails_closed(mutation: str) -> None:
    """P4B0-REJECT-002."""

    source = _fixture_source("route_exact_in_pool_not_found_rejected")
    exact_observation = _mapping(_mapping(source["exact"])["observation"])
    rejection = _mapping(exact_observation["rejection"])
    if mutation == "code":
        rejection["code"] = "guard_rejected"
    elif mutation == "path":
        rejection["path"] = ["settlement"]
    elif mutation == "precedence":
        rejection["precedence"] = "guard"
    elif mutation == "public_reason":
        rejection["public_reason"] = "fabricated public reason"
    else:
        accepted = _fixture_source("swap_exact_in_smallest_accepted")
        accepted_exact = _mapping(_mapping(accepted["exact"])["observation"])
        exact_observation["patch_bytes"] = accepted_exact["patch_bytes"]
    result = _evaluate_source(source)
    assert type(result) in {MismatchV1, InvalidEvidenceV1}


def test_p4b0_state_001_projection_inventory_is_exactly_eight_fields() -> None:
    """P4B0-STATE-001."""

    assert SEMANTIC_STATE_FIELD_ORDER_V1 == (
        "balances",
        "pools",
        "lp_balances",
        "nonces",
        "vault",
        "oracle",
        "fee_accumulator",
        "perps",
    )


@pytest.mark.parametrize("field_name", SEMANTIC_STATE_FIELD_ORDER_V1)
def test_p4b0_state_002_each_root_recomputed_state_mutation_fails(field_name: str) -> None:
    """P4B0-STATE-002."""

    source = _fixture_source("swap_exact_in_boundary_valid")
    _rewrite_legacy_state(source, field_name)
    result = _evaluate_source(source)
    assert type(result) in {MismatchV1, InvalidEvidenceV1}
    if type(result) is MismatchV1:
        assert result.code == "state_field_mismatch"
        assert result.path == ("next_state", field_name)


@pytest.mark.parametrize(
    "mutation",
    (
        "settlement_fill",
        "settlement_event",
        "effects_fee",
        "replay_nonce",
        "total_swap_fees",
        "nonce_table_hash",
        "fee_allocation",
    ),
)
def test_p4b0_econ_001_each_economic_mutation_fails_closed(mutation: str) -> None:
    """P4B0-ECON-001."""

    fixture_id = (
        "create_pool_smallest_accepted"
        if mutation == "settlement_event"
        else "swap_exact_in_boundary_valid"
    )
    source = _fixture_source(fixture_id)
    if mutation == "settlement_fill":
        _rewrite_component(
            source,
            "settlement_bytes",
            lambda value: _mapping(_sequence(value["fills"])[0]).__setitem__(
                "fee_paid",
                cast(int, _mapping(_sequence(value["fills"])[0])["fee_paid"]) + 1,
            ),
        )
    elif mutation == "settlement_event":
        _rewrite_component(
            source,
            "settlement_bytes",
            lambda value: _mapping(_sequence(value["events"])[0]).__setitem__("status", "FROZEN"),
        )
    elif mutation == "effects_fee":
        _rewrite_component(
            source,
            "effects_bytes",
            lambda value: value.__setitem__(
                "total_swap_fees", cast(int, value["total_swap_fees"]) + 1
            ),
        )
    elif mutation == "replay_nonce":
        _rewrite_component(
            source,
            "replay_bytes",
            lambda value: _mapping(_sequence(value["nonce_advances"])[0]).__setitem__(
                "new_last",
                cast(int, _mapping(_sequence(value["nonce_advances"])[0])["new_last"]) + 1,
            ),
        )
    else:
        exact = _mapping(_mapping(source["exact"])["observation"])
        if mutation == "total_swap_fees":
            exact["total_swap_fees"] = cast(int, exact["total_swap_fees"]) + 1
        elif mutation == "nonce_table_hash":
            exact["next_nonce_table_hash"] = "0x" + "00" * 32
        else:
            exact["fee_allocation"] = {"attacker": 1}
    assert type(_evaluate_source(source)) in {MismatchV1, InvalidEvidenceV1}


@pytest.mark.parametrize("mutation", ("stale_expected", "missing", "duplicate", "reordered"))
def test_p4b0_patch_002_invalid_patch_variants_fail_atomically(mutation: str) -> None:
    """P4B0-PATCH-002."""

    source = _fixture_source("swap_exact_in_boundary_valid")

    def mutate(patch: dict[str, object]) -> None:
        writes = _sequence(patch["balance_writes"])
        if mutation == "stale_expected":
            first = _mapping(writes[0])
            first["expected_old"] = cast(int, first["expected_old"]) + 1
        elif mutation == "missing":
            writes.pop()
        elif mutation == "duplicate":
            writes.append(writes[0])
        else:
            writes.reverse()

    _rewrite_component(source, "patch_bytes", mutate)
    assert type(_evaluate_source(source)) is InvalidEvidenceV1


@pytest.mark.parametrize(
    ("field_name", "expected_code"),
    (("receipt_root", "receipt_root_mismatch"), ("bundle_root", "bundle_root_mismatch")),
)
def test_p4b0_bundle_001_cached_roots_do_not_replace_recomputation(
    field_name: str,
    expected_code: str,
) -> None:
    """P4B0-BUNDLE-001."""

    source = _fixture_source("swap_exact_in_boundary_valid")
    exact = _mapping(_mapping(source["exact"])["observation"])
    exact[field_name] = "0x" + "01" * 32
    result = _evaluate_source(source)
    assert type(result) is InvalidEvidenceV1
    assert result.code == expected_code


@pytest.mark.parametrize(
    "fields",
    (
        ("receipt_bytes", "receipt_root"),
        ("bundle_bytes", "bundle_root"),
        ("commit_plan_bytes",),
        ("outbox_bytes", "outbox_identities"),
    ),
)
def test_p4b0_bundle_002_cross_candidate_substitution_fails(fields: tuple[str, ...]) -> None:
    """P4B0-BUNDLE-002."""

    source = _fixture_source("swap_exact_in_boundary_valid")
    donor_id = (
        "create_pool_smallest_accepted"
        if fields == ("outbox_bytes", "outbox_identities")
        else "swap_exact_in_smallest_accepted"
    )
    donor = _fixture_source(donor_id)
    target_observation = _mapping(_mapping(source["exact"])["observation"])
    donor_observation = _mapping(_mapping(donor["exact"])["observation"])
    for field_name in fields:
        target_observation[field_name] = donor_observation[field_name]
    assert type(_evaluate_source(source)) is InvalidEvidenceV1


@pytest.mark.parametrize("mutation", ("delete", "duplicate", "payload", "idempotency"))
def test_p4b0_outbox_001_outbox_record_mutations_fail(mutation: str) -> None:
    """P4B0-OUTBOX-001."""

    source = _fixture_source("create_pool_smallest_accepted")

    def mutate(outbox: dict[str, object]) -> None:
        records = _sequence(outbox["records"])
        if mutation == "delete":
            records.pop()
        elif mutation == "duplicate":
            records.append(records[0])
        else:
            first = _mapping(records[0])
            if mutation == "payload":
                first["payload"] = "00"
            else:
                first["idempotency_key"] = "0x" + "00" * 32

    _rewrite_component(source, "outbox_bytes", mutate)
    assert type(_evaluate_source(source)) is InvalidEvidenceV1
