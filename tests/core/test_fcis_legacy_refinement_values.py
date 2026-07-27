"""P4B0-A contract tests for values, schemas, admission, and policy."""

from __future__ import annotations

import inspect
import json
from pathlib import Path
from typing import cast

import pytest

from src.core import fcis_legacy_refinement_admission as admission_module
from src.core.fcis_legacy_refinement_admission import (
    BASELINE_ARTIFACT_HASH_V1,
    DIFFERENTIAL_ARTIFACT_HASH_V1,
    PACKET_COMMIT_V1,
    PACKET_TREE_HASH_V1,
    REQUIRED_ANCESTOR_V1,
    _admit_pair_source,
    admit_observation_pair_bytes_v1,
    decode_canonical_evidence_artifact_bytes_v1,
    decode_canonical_json_bytes_v1,
    encode_observation_pair_v1,
    revalidate_observation_pair_v1,
)
from src.core.fcis_legacy_refinement_policy import (
    COMMAND_KIND_ENTRIES_V1,
    EXACT_ONLY_FIELD_ENTRIES_V1,
    POLICY_HASH_V1,
    POLICY_VERSION_V1,
    REJECTION_MAPPINGS_V1,
    SEMANTIC_PROJECTION_ENTRIES_V1,
    VERSION_DELTA_ENTRIES_V1,
    is_known_command_kind_v1,
    lookup_version_delta_v1,
)
from src.core.fcis_legacy_refinement_schema import (
    MAX_REFINEMENT_ARTIFACT_BYTES_V1,
    MAX_REFINEMENT_BYTES_V1,
    MAX_REFINEMENT_COLLECTION_ITEMS_V1,
    MAX_REFINEMENT_DEPTH_V1,
    MAX_REFINEMENT_FIELD_UTF8_BYTES_V1,
    MAX_REFINEMENT_FIXTURES_V1,
    MAX_REFINEMENT_MISMATCH_PAYLOAD_BYTES_V1,
    MAX_REFINEMENT_NODES_V1,
    MAX_REFINEMENT_OBSERVATIONS_V1,
    MAX_REFINEMENT_WITNESS_BYTES_V1,
    OBSERVATION_PAIR_SCHEMA_ID_V1,
    REFINEMENT_RESOURCE_BOUNDS_V1,
    RefinementResourceCodeV1,
    RefinementResourceKindV1,
    check_refinement_resource_limit_v1,
)
from src.core.fcis_legacy_refinement_values import (
    CanonicalParseCodeV1,
    CanonicalParseRejectV1,
    InvalidEvidenceV1,
    ObservationPairV1,
)
from src.state.canonical import canonical_json_bytes, sha256_hex
from src.state.intents import IntentKind
from src.state.owned_json import JsonSourceValueV1
from src.state.snapshot_combinators import AdmitCode, AdmitReject

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


def _fixture_ids() -> tuple[str, ...]:
    return tuple(
        cast(str, _mapping(fixture)["fixture_id"]) for fixture in _sequence(_artifact()["fixtures"])
    )


def _fixture_source(fixture_id: str | None = None) -> dict[str, object]:
    artifact = _artifact()
    fixtures = _sequence(artifact["fixtures"])
    selected = next(
        _mapping(fixture)
        for fixture in fixtures
        if fixture_id is None or _mapping(fixture)["fixture_id"] == fixture_id
    )
    selected_id = cast(str, selected["fixture_id"])
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
            "fixture_id": selected_id,
            "packet_commit": PACKET_COMMIT_V1,
            "packet_tree_hash": PACKET_TREE_HASH_V1,
            "pre_state_bytes": raw["state_snapshot_bytes"],
            "pre_state_root": raw["state_snapshot_root"],
            "reviewed_start_sha": REQUIRED_ANCESTOR_V1,
        }

    return {
        "exact": {
            "binding": binding("exact"),
            "observation": comparison["exact"],
        },
        "legacy": {
            "binding": binding("legacy"),
            "observation": comparison["legacy"],
        },
    }


def _pair_raw(fixture_id: str | None = None) -> bytes:
    return canonical_json_bytes(_fixture_source(fixture_id))


def _admitted_pair(fixture_id: str | None = None) -> ObservationPairV1:
    result = admit_observation_pair_bytes_v1(_pair_raw(fixture_id))
    assert type(result) is ObservationPairV1
    return result


def test_p4b0_input_001_source_bindings() -> None:
    """P4B0-INPUT-001"""

    pair = _admitted_pair()
    for bound in (pair.legacy, pair.exact):
        binding = bound.binding
        assert binding.baseline_artifact_hash == BASELINE_ARTIFACT_HASH_V1
        assert binding.differential_artifact_hash == DIFFERENTIAL_ARTIFACT_HASH_V1
        assert binding.reviewed_start_sha == REQUIRED_ANCESTOR_V1
        assert binding.packet_commit == PACKET_COMMIT_V1
        assert binding.packet_tree_hash == PACKET_TREE_HASH_V1
        assert binding.command_bytes
        assert binding.pre_state_bytes
        assert binding.context_bytes
    assert pair.canonical_source_hash == sha256_hex(pair.canonical_source_bytes)


@pytest.mark.parametrize(
    ("raw", "expected_code"),
    (
        (b'{"a":1,"a":2}', CanonicalParseCodeV1.DUPLICATE_KEY),
        (b'\xef\xbb\xbf{"a":1}', CanonicalParseCodeV1.BOM),
        (b'{"a":1}x', CanonicalParseCodeV1.INVALID_JSON),
        (b'{"a": 1}', CanonicalParseCodeV1.NONCANONICAL_JSON),
        (b'{"b":2,"a":1}', CanonicalParseCodeV1.NONCANONICAL_JSON),
        (b'{"a":1.5}', CanonicalParseCodeV1.FLOAT_FORBIDDEN),
        (b'{"a":1e2}', CanonicalParseCodeV1.FLOAT_FORBIDDEN),
        (b'{"a":-0}', CanonicalParseCodeV1.NONCANONICAL_JSON),
        (b'{"a":NaN}', CanonicalParseCodeV1.NONFINITE_FORBIDDEN),
        (b'{"a":"\xff"}', CanonicalParseCodeV1.INVALID_UTF8),
        (b'{"a":"\\ud800"}', CanonicalParseCodeV1.INVALID_UTF8),
    ),
)
def test_p4b0_parse_001_rejects_ambiguous_bytes(
    raw: bytes,
    expected_code: CanonicalParseCodeV1,
) -> None:
    """P4B0-PARSE-001"""

    result = decode_canonical_json_bytes_v1(raw)
    assert type(result) is CanonicalParseRejectV1
    assert result.code is expected_code


def test_p4b0_parse_002_round_trip_and_full_consumption() -> None:
    """P4B0-PARSE-002"""

    raw = canonical_json_bytes({"a": [1, True, None], "z": "exact"})
    decoded = decode_canonical_json_bytes_v1(raw)
    assert type(decoded) is dict
    assert canonical_json_bytes(decoded) == raw


def test_p4b0_admit_001_every_frozen_observation_uses_closed_schema() -> None:
    """P4B0-ADMIT-001"""

    fixture_ids = _fixture_ids()
    assert len(fixture_ids) == MAX_REFINEMENT_FIXTURES_V1
    for fixture_id in fixture_ids:
        pair = _admitted_pair(fixture_id)
        assert revalidate_observation_pair_v1(pair) is pair
        assert encode_observation_pair_v1(pair) == pair.canonical_source_bytes


def test_p4b0_admit_002_no_parallel_pre_admission_validator() -> None:
    public_source = inspect.getsource(admission_module.admit_observation_pair_bytes_v1)
    assert public_source.index("decode_canonical_json_bytes_v1") < public_source.index(
        "_admit_pair_source"
    )
    assert public_source.index("_admit_pair_source") < public_source.index("_build_pair")
    assert "fromhex" not in public_source
    assert "type(decoded) is dict" not in public_source
    assert "isinstance" not in inspect.getsource(admission_module)


def test_p4b0_immut_001_alias_subclass_and_hostile_mutation_fail_closed() -> None:
    """P4B0-IMMUT-001"""

    source = _fixture_source()
    pair = admit_observation_pair_bytes_v1(canonical_json_bytes(source))
    assert type(pair) is ObservationPairV1
    original_fixture = pair.legacy.binding.fixture_id
    _mapping(_mapping(source["legacy"])["binding"])["fixture_id"] = "caller_mutated"
    assert pair.legacy.binding.fixture_id == original_fixture

    class PairSubclass(ObservationPairV1):
        pass

    substituted = object.__new__(PairSubclass)
    substitution_result = revalidate_observation_pair_v1(substituted)
    assert type(substitution_result) is InvalidEvidenceV1
    assert substitution_result.code == "pair_exact_type_mismatch"

    object.__setattr__(pair.exact.observation, "algorithm_id", "mutated")
    mutation_result = revalidate_observation_pair_v1(pair)
    assert type(mutation_result) is InvalidEvidenceV1
    assert mutation_result.code == "pair_source_bytes_mismatch"


def test_p4b0_policy_001_registry_is_closed_unique_and_hash_bound() -> None:
    """P4B0-POLICY-001"""

    stable_ids = (
        *(entry.stable_id for entry in VERSION_DELTA_ENTRIES_V1),
        *(entry.stable_id for entry in REJECTION_MAPPINGS_V1),
        *(entry.stable_id for entry in EXACT_ONLY_FIELD_ENTRIES_V1),
        *(entry.stable_id for entry in SEMANTIC_PROJECTION_ENTRIES_V1),
        *(entry.stable_id for entry in COMMAND_KIND_ENTRIES_V1),
    )
    assert len(stable_ids) == len(set(stable_ids))
    assert POLICY_VERSION_V1.endswith("/v1")
    assert POLICY_HASH_V1.startswith("0x") and len(POLICY_HASH_V1) == 66
    assert {entry.command_kind for entry in COMMAND_KIND_ENTRIES_V1} == {
        member.value for member in IntentKind
    }


@pytest.mark.parametrize("injected_field", ("policy", "constructor", "ignored_paths"))
def test_p4b0_policy_002_input_cannot_supply_policy_behavior(injected_field: str) -> None:
    """P4B0-POLICY-002"""

    source = _fixture_source()
    source[injected_field] = ["*"] if injected_field == "ignored_paths" else "attacker"
    result = admit_observation_pair_bytes_v1(canonical_json_bytes(source))
    assert type(result) is InvalidEvidenceV1
    assert result.code == "admit_item_limit"


@pytest.mark.parametrize(
    "field_name",
    (
        "command_bytes",
        "command_hash",
        "pre_state_bytes",
        "pre_state_root",
        "context_bytes",
        "context_hash",
    ),
)
def test_p4b0_input_002_one_sided_input_substitution_rejects(field_name: str) -> None:
    """P4B0-INPUT-002"""

    source = _fixture_source()
    legacy_binding = _mapping(_mapping(source["legacy"])["binding"])
    if field_name == "command_bytes":
        values = _sequence(legacy_binding[field_name])
        values[0] = cast(str, values[0]) + "00"
    elif field_name in ("pre_state_bytes", "context_bytes"):
        legacy_binding[field_name] = cast(str, legacy_binding[field_name]) + "00"
    else:
        legacy_binding[field_name] = "0x" + "00" * 32
    result = admit_observation_pair_bytes_v1(canonical_json_bytes(source))
    assert type(result) is InvalidEvidenceV1
    assert result.code in {
        "command_hash_mismatch",
        "context_hash_mismatch",
        "pre_state_root_mismatch",
        "same_input_mismatch",
    }


def test_p4b0_version_001_every_frozen_delta_is_source_registered() -> None:
    """P4B0-VERSION-001"""

    for fixture_id in _fixture_ids():
        pair = _admitted_pair(fixture_id)
        legacy = pair.legacy.observation
        exact = pair.exact.observation
        values = (
            ("algorithm_id", legacy.algorithm_id, exact.algorithm_id),
            ("algorithm_version", str(legacy.algorithm_version), str(exact.algorithm_version)),
            ("codec_version", str(legacy.codec_version), str(exact.codec_version)),
            ("schema_version", str(legacy.schema_version), str(exact.schema_version)),
            (
                "snapshot_version",
                "none" if legacy.snapshot_version is None else str(legacy.snapshot_version),
                "none" if exact.snapshot_version is None else str(exact.snapshot_version),
            ),
            (
                "support_root_version",
                "none" if legacy.support_root_version is None else str(legacy.support_root_version),
                "none" if exact.support_root_version is None else str(exact.support_root_version),
            ),
        )
        for field_name, legacy_value, exact_value in values:
            assert (
                lookup_version_delta_v1(
                    field_name,
                    legacy_value,
                    exact_value,
                    legacy.result_kind,
                )
                is not None
            )


@pytest.mark.parametrize(
    ("field_name", "unknown_value"),
    (
        ("algorithm_id", "unknown_algorithm"),
        ("algorithm_version", 999),
        ("codec_version", 999),
        ("schema_version", 999),
        ("snapshot_version", 999),
        ("support_root_version", 999),
    ),
)
def test_p4b0_version_002_unknown_version_fails_closed(
    field_name: str,
    unknown_value: object,
) -> None:
    """P4B0-VERSION-002"""

    source = _fixture_source()
    exact_observation = _mapping(_mapping(source["exact"])["observation"])
    exact_observation[field_name] = unknown_value
    result = admit_observation_pair_bytes_v1(canonical_json_bytes(source))
    assert type(result) is InvalidEvidenceV1
    assert result.code == "unknown_version_delta"
    assert result.path == (field_name,)


@pytest.mark.parametrize(
    "mutation",
    (
        "command_kind",
        "result_kind",
        "unknown_field",
        "unknown_status",
        "observation_variant",
    ),
)
def test_p4b0_unknown_001_unknown_shapes_fail_closed(mutation: str) -> None:
    """P4B0-UNKNOWN-001"""

    source = _fixture_source()
    if mutation == "command_kind":
        _mapping(_mapping(source["legacy"])["binding"])["command_kind"] = "UNKNOWN"
        _mapping(_mapping(source["exact"])["binding"])["command_kind"] = "UNKNOWN"
    elif mutation == "result_kind":
        _mapping(_mapping(source["exact"])["observation"])["result_kind"] = "unknown"
    elif mutation == "unknown_field":
        _mapping(_mapping(source["exact"])["observation"])["new_field"] = 1
    elif mutation == "unknown_status":
        legacy = _mapping(_mapping(source["legacy"])["observation"])
        legacy["receipt_bytes"] = {"status": "*"}
    else:
        _mapping(source["exact"])["observation"] = []
    result = admit_observation_pair_bytes_v1(canonical_json_bytes(source))
    assert type(result) is InvalidEvidenceV1


def test_p4b0_unknown_002_registry_coverage_is_exact() -> None:
    """P4B0-UNKNOWN-002"""

    command_values = tuple(entry.command_kind for entry in COMMAND_KIND_ENTRIES_V1)
    assert len(command_values) == len(set(command_values))
    assert set(command_values) == {member.value for member in IntentKind}
    assert not is_known_command_kind_v1("UNDECLARED")
    version_keys = tuple(
        (entry.field_name, entry.legacy_value, entry.exact_value, entry.result_kind)
        for entry in VERSION_DELTA_ENTRIES_V1
    )
    assert len(version_keys) == len(set(version_keys))


def test_p4b0_budget_001_limits_and_neighbors_are_explicit() -> None:
    """P4B0-BUDGET-001"""

    bounds = REFINEMENT_RESOURCE_BOUNDS_V1
    assert (
        bounds.max_bytes,
        bounds.max_depth,
        bounds.max_nodes,
        bounds.max_fixtures,
        bounds.max_observations,
        bounds.max_collection_items,
        bounds.max_field_utf8_bytes,
        bounds.max_mismatch_payload_bytes,
        bounds.max_witness_bytes,
    ) == (
        MAX_REFINEMENT_BYTES_V1,
        MAX_REFINEMENT_DEPTH_V1,
        MAX_REFINEMENT_NODES_V1,
        MAX_REFINEMENT_FIXTURES_V1,
        MAX_REFINEMENT_OBSERVATIONS_V1,
        MAX_REFINEMENT_COLLECTION_ITEMS_V1,
        MAX_REFINEMENT_FIELD_UTF8_BYTES_V1,
        MAX_REFINEMENT_MISMATCH_PAYLOAD_BYTES_V1,
        MAX_REFINEMENT_WITNESS_BYTES_V1,
    )
    at_limit = decode_canonical_json_bytes_v1(b"0" * MAX_REFINEMENT_BYTES_V1)
    assert type(at_limit) is CanonicalParseRejectV1
    assert at_limit.code is not CanonicalParseCodeV1.BYTE_LIMIT
    over_limit = decode_canonical_json_bytes_v1(b"0" * (MAX_REFINEMENT_BYTES_V1 + 1))
    assert type(over_limit) is CanonicalParseRejectV1
    assert over_limit.code is CanonicalParseCodeV1.BYTE_LIMIT

    aggregate = decode_canonical_evidence_artifact_bytes_v1(DIFFERENTIAL_PATH.read_bytes())
    assert type(aggregate) is dict
    aggregate_over_limit = decode_canonical_evidence_artifact_bytes_v1(
        b"0" * (MAX_REFINEMENT_ARTIFACT_BYTES_V1 + 1)
    )
    assert type(aggregate_over_limit) is CanonicalParseRejectV1
    assert aggregate_over_limit.code is CanonicalParseCodeV1.BYTE_LIMIT

    limit_cases = (
        (RefinementResourceKindV1.BYTES, MAX_REFINEMENT_BYTES_V1),
        (RefinementResourceKindV1.DEPTH, MAX_REFINEMENT_DEPTH_V1),
        (RefinementResourceKindV1.NODES, MAX_REFINEMENT_NODES_V1),
        (RefinementResourceKindV1.FIXTURES, MAX_REFINEMENT_FIXTURES_V1),
        (RefinementResourceKindV1.OBSERVATIONS, MAX_REFINEMENT_OBSERVATIONS_V1),
        (
            RefinementResourceKindV1.COLLECTION_ITEMS,
            MAX_REFINEMENT_COLLECTION_ITEMS_V1,
        ),
        (
            RefinementResourceKindV1.FIELD_UTF8_BYTES,
            MAX_REFINEMENT_FIELD_UTF8_BYTES_V1,
        ),
        (
            RefinementResourceKindV1.MISMATCH_PAYLOAD_BYTES,
            MAX_REFINEMENT_MISMATCH_PAYLOAD_BYTES_V1,
        ),
        (RefinementResourceKindV1.WITNESS_BYTES, MAX_REFINEMENT_WITNESS_BYTES_V1),
    )
    for kind, maximum in limit_cases:
        assert check_refinement_resource_limit_v1(kind, maximum) is None
        rejected = check_refinement_resource_limit_v1(kind, maximum + 1)
        assert rejected is not None
        assert rejected.code is RefinementResourceCodeV1.LIMIT_EXCEEDED
        assert rejected.kind is kind
        assert rejected.observed == maximum + 1
        assert rejected.maximum == maximum

    with pytest.raises(TypeError, match="exact integer"):
        check_refinement_resource_limit_v1(RefinementResourceKindV1.BYTES, True)

    bounded_source = _fixture_source()
    bounded_exact = _mapping(_mapping(bounded_source["exact"])["observation"])
    identity = {
        "effect_identity": "0x" + "01" * 32,
        "effect_index": 0,
        "idempotency_key": "0x" + "02" * 32,
    }
    bounded_exact["outbox_identities"] = [identity] * MAX_REFINEMENT_COLLECTION_ITEMS_V1
    assert (
        type(admit_observation_pair_bytes_v1(canonical_json_bytes(bounded_source)))
        is ObservationPairV1
    )

    field_source = _fixture_source()
    field_exact = _mapping(_mapping(field_source["exact"])["observation"])
    field_exact["next_state_snapshot_bytes"] = "00" * (MAX_REFINEMENT_FIELD_UTF8_BYTES_V1 // 2)
    assert (
        type(admit_observation_pair_bytes_v1(canonical_json_bytes(field_source)))
        is ObservationPairV1
    )
    field_exact["next_state_snapshot_bytes"] = (
        cast(
            str,
            field_exact["next_state_snapshot_bytes"],
        )
        + "0"
    )
    field_reject = admit_observation_pair_bytes_v1(canonical_json_bytes(field_source))
    assert type(field_reject) is InvalidEvidenceV1
    assert field_reject.code == "admit_byte_limit"


def test_p4b0_budget_002_deep_wide_oversized_and_cycle_shapes_reject() -> None:
    """P4B0-BUDGET-002"""

    deep = b"[" * (MAX_REFINEMENT_DEPTH_V1 + 1) + b"0" + b"]" * (MAX_REFINEMENT_DEPTH_V1 + 1)
    deep_result = decode_canonical_json_bytes_v1(deep)
    assert type(deep_result) is CanonicalParseRejectV1
    assert deep_result.code is CanonicalParseCodeV1.DEPTH_LIMIT

    wide_source = _fixture_source()
    exact_observation = _mapping(_mapping(wide_source["exact"])["observation"])
    exact_observation["outbox_identities"] = [
        f"id-{index}" for index in range(MAX_REFINEMENT_COLLECTION_ITEMS_V1 + 1)
    ]
    wide_result = admit_observation_pair_bytes_v1(canonical_json_bytes(wide_source))
    assert type(wide_result) is InvalidEvidenceV1
    assert wide_result.code in {"admit_item_limit", "admit_byte_limit"}

    cyclic_source = _fixture_source()
    cyclic_source["legacy"] = cyclic_source
    cycle_result = _admit_pair_source(
        OBSERVATION_PAIR_SCHEMA_ID_V1,
        cast(JsonSourceValueV1, cyclic_source),
    )
    assert type(cycle_result) is AdmitReject
    assert cycle_result.code is AdmitCode.CYCLE
    assert cycle_result.path
    assert not hasattr(cycle_result, "value")
