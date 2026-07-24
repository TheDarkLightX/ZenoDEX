from __future__ import annotations

import copy
import hashlib
import json
from collections.abc import Iterator
from typing import Any, cast

import pytest

from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate

EXPECTED_FIXTURE_BYTES = 12_472
EXPECTED_FIXTURE_SHA256 = "4aef5bb5bbc792b741d3949372c757e6e021bc4feabf50dfa045ebe5f4d58976"
EXPECTED_CANDIDATE_ID = "719db33cbac91d95251592c874a08754530f8210c3504e844af5e1f490cda6ac"


def _position_digest(index: int, *, size: int = 32) -> str:
    raw = bytes(((index * 37) + (offset * 19) + (offset * offset * 3)) % 256 for offset in range(size))
    assert raw != raw[::-1]
    assert any(raw)
    return raw.hex()


def _inventory() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for index, role in enumerate(candidate.REQUIRED_EVIDENCE_ROLES_V1):
        artifact_sha256 = _position_digest(index + 1)
        bound_identity = (
            artifact_sha256
            if role in candidate.RAW_ARTIFACT_DIGEST_ROLES_V1
            else _position_digest(index + 101)
        )
        rows.append(
            {
                "artifact_sha256": artifact_sha256,
                "bound_identity": bound_identity,
                "codec": candidate.EXPECTED_EVIDENCE_CODEC_BY_ROLE_V1[role],
                "role": role,
                "size_bytes": 1_003 + (index * 211),
            }
        )
    return rows


def _set_inventory_total_size(body: dict[str, Any], total_size_bytes: int) -> None:
    rows = body["evidence_inventory"]
    remaining = total_size_bytes
    for index, role in enumerate(candidate.REQUIRED_EVIDENCE_ROLES_V1):
        rows_after = len(rows) - index - 1
        size_bytes = min(
            candidate.MAX_EVIDENCE_BYTES_BY_ROLE_V1[role],
            remaining - rows_after,
        )
        assert size_bytes > 0
        rows[index]["size_bytes"] = size_bytes
        remaining -= size_bytes
    assert remaining == 0


def _body() -> dict[str, Any]:
    inventory = _inventory()
    identity_by_role = {row["role"]: row["bound_identity"] for row in inventory}
    return {
        "authority": {name: False for name in candidate.AUTHORITY_FIELDS_V1},
        "evidence_inventory": inventory,
        "format_flags": 1,
        "lineage": {
            "minimum_rollback_revision": 0x0102_0304,
            "parent_candidate_id": _position_digest(41),
            "proposed_activation_epoch": 0x0102_0304_0506_0708,
            "proposed_expiration_epoch": 0x1122_3344_5566_7788,
            "release_revision": 0x0102_0304_0506,
            "revocation_policy_root": identity_by_role["revocation_policy"],
            "revocation_record_root": None,
            "rollback_policy_root": identity_by_role["rollback_policy"],
        },
        "manifests": {
            "authority_manifest_sha256": identity_by_role["authority_manifest"],
            "replay_manifest_sha256": identity_by_role["replay_manifest"],
            "verifier_manifest_sha256": identity_by_role["verifier_manifest"],
        },
        "non_claims": list(candidate.NON_CLAIMS_V1),
        "policies": {
            "data_availability_policy_root": identity_by_role[
                "data_availability_policy"
            ],
            "finality_policy_root": identity_by_role["finality_policy"],
            "operational_policy_root": identity_by_role["operational_policy"],
        },
        "proofs": {
            "v6_image_id_root": identity_by_role["v6_image_identity_manifest"],
            "v6_journal_root": identity_by_role["v6_journal_bundle"],
            "v6_mutation_root": identity_by_role["v6_mutation_report"],
            "v6_program_root": identity_by_role["v6_program_bundle"],
            "v6_receipt_root": identity_by_role["v6_receipt_bundle"],
            "v7_image_id_root": identity_by_role["v7_image_identity_manifest"],
            "v7_journal_root": identity_by_role["v7_journal"],
            "v7_mutation_root": identity_by_role["v7_mutation_report"],
            "v7_program_root": identity_by_role["v7_program"],
            "v7_receipt_root": identity_by_role["v7_receipt"],
        },
        "reserved_u32": 0,
        "runtime": {
            "artifact_set_id": identity_by_role["runtime_artifact_manifest"],
            "authority_input_profile_sha256": identity_by_role[
                "authority_input_profile"
            ],
            "firecracker_profile_sha256": identity_by_role["firecracker_profile"],
            "machine_config_sha256": identity_by_role["machine_config"],
            "root_supervisor_contract_sha256": identity_by_role[
                "root_supervisor_contract"
            ],
            "root_supervisor_executable_sha256": identity_by_role[
                "root_supervisor_executable"
            ],
            "runtime_manifest_sha256": identity_by_role["runtime_manifest"],
        },
        "schema": candidate.SPOT_V7_RELEASE_CANDIDATE_MANIFEST_SCHEMA_V1,
        "scope": {
            "application_id": "zenodex",
            "chain_id": "tau-chain-314159",
            "domain_id": "spot-domain-271828",
            "proof_profile_sha256": identity_by_role["proof_profile"],
            "receipt_security_profile_sha256": identity_by_role[
                "receipt_security_profile"
            ],
            "release_profile": candidate.SPOT_V7_RELEASE_PROFILE_V1,
        },
        "source_build": {
            "build_container_manifest_sha256": identity_by_role[
                "build_container_manifest"
            ],
            "build_input_closure_root": identity_by_role["build_input_closure"],
            "source_closure_root": identity_by_role["source_closure"],
            "source_commit": _position_digest(46, size=20),
            "source_tree": _position_digest(47, size=20),
            "toolchain_manifest_sha256": identity_by_role["toolchain_manifest"],
        },
        "status": candidate.SPOT_V7_RELEASE_CANDIDATE_MANIFEST_STATUS_V1,
    }


def _document(raw: bytes) -> dict[str, Any]:
    value = json.loads(raw)
    assert type(value) is dict
    return value


def _canonical(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n"
    ).encode("ascii")


def _leaf_paths(value: object, prefix: tuple[object, ...] = ()) -> Iterator[tuple[object, ...]]:
    if type(value) is dict:
        for key in sorted(value):
            yield from _leaf_paths(value[key], (*prefix, key))
        return
    if type(value) is list:
        for index, item in enumerate(value):
            yield from _leaf_paths(item, (*prefix, index))
        return
    yield prefix


def _get(root: object, path: tuple[object, ...]) -> object:
    value = root
    for part in path:
        if type(part) is str:
            assert type(value) is dict
            value = value[part]
        else:
            assert type(value) is list
            value = value[cast(int, part)]
    return value


def _set(root: object, path: tuple[object, ...], replacement: object) -> None:
    parent = root
    for part in path[:-1]:
        if type(part) is str:
            assert type(parent) is dict
            parent = parent[part]
        else:
            assert type(parent) is list
            parent = parent[cast(int, part)]
    final = path[-1]
    if type(final) is str:
        assert type(parent) is dict
        parent[final] = replacement
    else:
        assert type(parent) is list
        parent[cast(int, final)] = replacement


def _mutated_scalar(value: object) -> object:
    if value is None:
        return _position_digest(93)
    if type(value) is bool:
        return not value
    if type(value) is int:
        return value + 1
    if type(value) is str:
        if len(value) in {40, 64} and all(character in "0123456789abcdef" for character in value):
            return value[::-1]
        return value + "-changed"
    raise AssertionError(f"unsupported scalar {value!r}")


def test_position_distinct_fixture_recomposes_and_remains_authority_false() -> None:
    raw = candidate.recompose_spot_v7_release_candidate_manifest_v1(_body())
    parsed = candidate.parse_exact_spot_v7_release_candidate_manifest_v1(raw)

    assert len(raw) == EXPECTED_FIXTURE_BYTES
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_FIXTURE_SHA256
    assert parsed.canonical_bytes == raw
    assert parsed.candidate_id.hex() == EXPECTED_CANDIDATE_ID
    assert parsed.candidate_id.hex() == _document(raw)["candidate_id"]
    assert parsed.release_revision == 0x0102_0304_0506
    assert parsed.parent_candidate_id == bytes.fromhex(_position_digest(41))
    assert parsed.candidate_selected is False
    assert parsed.candidate_current is False
    assert parsed.activation_authority is False
    assert parsed.revocation_authority is False
    assert parsed.rollback_authority is False
    assert parsed.source_to_binary_verified is False
    assert parsed.proof_evidence_verified is False
    assert parsed.runtime_execution_verified is False
    assert parsed.release_authority is False
    assert parsed.settlement_authority is False
    assert parsed.production_authority is False

    digests = [
        bytes.fromhex(cast(str, row["artifact_sha256"])) for row in _inventory()
    ]
    assert len(digests) == len(set(digests))
    assert all(digest != digest[::-1] for digest in digests)


def test_checker_requires_the_independently_expected_candidate_id() -> None:
    raw = candidate.recompose_spot_v7_release_candidate_manifest_v1(_body())
    parsed = candidate.parse_exact_spot_v7_release_candidate_manifest_v1(raw)
    checked = candidate.check_exact_spot_v7_release_candidate_manifest_v1(
        raw,
        expected_candidate_id=parsed.candidate_id,
    )
    assert checked.candidate_id == parsed.candidate_id
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.check_exact_spot_v7_release_candidate_manifest_v1(
            raw,
            expected_candidate_id=bytes.fromhex(_position_digest(94)),
        )
    assert captured.value.code == "release_candidate_expected_id"


@pytest.mark.parametrize(
    ("raw", "code"),
    (
        (b'{"schema":"a","schema":"b"}\n', "release_candidate_json"),
        (b'{"schema":"a","sch\\u0065ma":"b"}\n', "release_candidate_json"),
        (b'{"revision":1.5}\n', "release_candidate_json"),
        (b'{"revision":NaN}\n', "release_candidate_json"),
        (b'{}', "release_candidate_json"),
        (b'\xff', "release_candidate_json"),
        (b'{"a":{"b":{"c":{"d":{"e":1}}}}}\n', "release_candidate_depth"),
    ),
)
def test_exact_decoder_rejects_ambiguous_or_unbounded_json(raw: bytes, code: str) -> None:
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.parse_exact_spot_v7_release_candidate_manifest_v1(raw)
    assert captured.value.code == code


def test_unknown_top_nested_and_inventory_fields_reject() -> None:
    raw = candidate.recompose_spot_v7_release_candidate_manifest_v1(_body())
    baseline = _document(raw)
    mutations = []
    top = copy.deepcopy(baseline)
    top["unknown"] = 1
    mutations.append(top)
    nested = copy.deepcopy(baseline)
    nested["scope"]["unknown"] = 1
    mutations.append(nested)
    row = copy.deepcopy(baseline)
    row["evidence_inventory"][0]["unknown"] = 1
    mutations.append(row)
    for mutated in mutations:
        with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
            candidate.parse_exact_spot_v7_release_candidate_manifest_v1(_canonical(mutated))
        assert captured.value.code in {
            "release_candidate_fields",
            "release_candidate_scope",
            "release_candidate_inventory_row",
        }


def test_every_flag_and_reserved_bit_has_a_rejecting_witness() -> None:
    for field in ("format_flags", "reserved_u32"):
        for bit in range(32):
            body = _body()
            body[field] ^= 1 << bit
            with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
                candidate.recompose_spot_v7_release_candidate_manifest_v1(body)
            assert captured.value.code == f"release_candidate_{field}"


@pytest.mark.parametrize(
    ("path", "replacement", "code"),
    (
        (("authority", "candidate_selected"), 0, "release_candidate_authority"),
        (("format_flags",), True, "release_candidate_format_flags"),
        (("lineage", "release_revision"), True, "release_candidate_revision"),
        (
            ("evidence_inventory", 0, "size_bytes"),
            True,
            "release_candidate_inventory_size",
        ),
    ),
)
def test_boolean_and_integer_representations_do_not_collapse(
    path: tuple[object, ...],
    replacement: object,
    code: str,
) -> None:
    body = _body()
    _set(body, path, replacement)
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.recompose_spot_v7_release_candidate_manifest_v1(body)
    assert captured.value.code == code


def test_lineage_optional_states_are_explicit_and_bounded() -> None:
    no_parent = _body()
    no_parent["lineage"]["parent_candidate_id"] = None
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.recompose_spot_v7_release_candidate_manifest_v1(no_parent)
    assert captured.value.code == "release_candidate_parent"

    revocation_record = _body()
    revocation_record["lineage"]["revocation_record_root"] = _position_digest(95)
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.recompose_spot_v7_release_candidate_manifest_v1(revocation_record)
    assert captured.value.code == "release_candidate_revocation_state"

    no_expiration = _body()
    no_expiration["lineage"]["proposed_expiration_epoch"] = None
    baseline = candidate.parse_exact_spot_v7_release_candidate_manifest_v1(
        candidate.recompose_spot_v7_release_candidate_manifest_v1(_body())
    )
    alternate = candidate.parse_exact_spot_v7_release_candidate_manifest_v1(
        candidate.recompose_spot_v7_release_candidate_manifest_v1(no_expiration)
    )
    assert alternate.candidate_id != baseline.candidate_id


def test_inventory_role_order_codec_aliasing_and_wrong_field_digest_reject() -> None:
    reversed_rows = _body()
    reversed_rows["evidence_inventory"].reverse()
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.recompose_spot_v7_release_candidate_manifest_v1(reversed_rows)
    assert captured.value.code == "release_candidate_inventory_order"

    wrong_codec = _body()
    wrong_codec["evidence_inventory"][0]["codec"] = "opaque_bytes_v1"
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.recompose_spot_v7_release_candidate_manifest_v1(wrong_codec)
    assert captured.value.code == "release_candidate_inventory_codec"

    wrong_field = _body()
    wrong_field["proofs"]["v7_receipt_root"] = wrong_field["proofs"]["v7_journal_root"]
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.recompose_spot_v7_release_candidate_manifest_v1(wrong_field)
    assert captured.value.code == "release_candidate_inventory_binding"

    alias = _body()
    alias["evidence_inventory"][1]["artifact_sha256"] = alias[
        "evidence_inventory"
    ][0]["artifact_sha256"]
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.recompose_spot_v7_release_candidate_manifest_v1(alias)
    assert captured.value.code == "release_candidate_inventory_digest"


def test_inventory_aggregate_size_accepts_exact_limit_and_rejects_limit_plus_one() -> None:
    exact = _body()
    _set_inventory_total_size(exact, candidate.MAX_EVIDENCE_BYTES_V1)
    candidate.recompose_spot_v7_release_candidate_manifest_v1(exact)

    oversized = _body()
    _set_inventory_total_size(oversized, candidate.MAX_EVIDENCE_BYTES_V1 + 1)
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.recompose_spot_v7_release_candidate_manifest_v1(oversized)
    assert captured.value.code == "release_candidate_inventory_total_size"


def test_raw_artifact_digest_and_semantic_identity_are_distinct_and_non_substitutable() -> None:
    body = _body()
    runtime_row = next(
        row
        for row in body["evidence_inventory"]
        if row["role"] == "runtime_artifact_manifest"
    )
    assert runtime_row["artifact_sha256"] != runtime_row["bound_identity"]
    assert body["runtime"]["artifact_set_id"] == runtime_row["bound_identity"]

    raw_substitution = copy.deepcopy(body)
    raw_substitution["runtime"]["artifact_set_id"] = runtime_row["artifact_sha256"]
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.recompose_spot_v7_release_candidate_manifest_v1(raw_substitution)
    assert captured.value.code == "release_candidate_inventory_binding"

    raw_role = copy.deepcopy(body)
    proof_profile_row = next(
        row
        for row in raw_role["evidence_inventory"]
        if row["role"] == "proof_profile"
    )
    proof_profile_row["bound_identity"] = _position_digest(199)
    with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
        candidate.recompose_spot_v7_release_candidate_manifest_v1(raw_role)
    assert captured.value.code == "release_candidate_inventory_identity"


def test_raw_swaps_and_reversals_cannot_preserve_the_candidate_identity() -> None:
    raw = candidate.recompose_spot_v7_release_candidate_manifest_v1(_body())
    baseline = _document(raw)
    mutations: list[dict[str, Any]] = []

    swap = copy.deepcopy(baseline)
    swap["proofs"]["v7_receipt_root"], swap["proofs"]["v7_journal_root"] = (
        swap["proofs"]["v7_journal_root"],
        swap["proofs"]["v7_receipt_root"],
    )
    mutations.append(swap)

    reverse = copy.deepcopy(baseline)
    reverse["runtime"]["machine_config_sha256"] = reverse["runtime"][
        "machine_config_sha256"
    ][::-1]
    mutations.append(reverse)

    inventory_swap = copy.deepcopy(baseline)
    inventory_swap["evidence_inventory"][0], inventory_swap["evidence_inventory"][1] = (
        inventory_swap["evidence_inventory"][1],
        inventory_swap["evidence_inventory"][0],
    )
    mutations.append(inventory_swap)

    for mutated in mutations:
        with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1):
            candidate.parse_exact_spot_v7_release_candidate_manifest_v1(_canonical(mutated))


def test_every_candidate_body_leaf_has_an_active_distinguishing_witness() -> None:
    body = _body()
    baseline = candidate.parse_exact_spot_v7_release_candidate_manifest_v1(
        candidate.recompose_spot_v7_release_candidate_manifest_v1(body)
    )
    paths = tuple(_leaf_paths(body))
    assert len(paths) == 220

    for path in paths:
        mutated = copy.deepcopy(body)
        _set(mutated, path, _mutated_scalar(_get(mutated, path)))
        try:
            result = candidate.parse_exact_spot_v7_release_candidate_manifest_v1(
                candidate.recompose_spot_v7_release_candidate_manifest_v1(mutated)
            )
        except candidate.SpotV7ReleaseCandidateRejectV1 as exc:
            assert exc.code.startswith("release_candidate_")
        else:
            assert result.candidate_id != baseline.candidate_id, path


def test_derived_root_and_candidate_id_mutations_reject_at_their_own_boundaries() -> None:
    baseline = _document(candidate.recompose_spot_v7_release_candidate_manifest_v1(_body()))
    for field, code in (
        ("evidence_inventory_root", "release_candidate_inventory_root"),
        ("candidate_id", "release_candidate_id"),
    ):
        mutated = copy.deepcopy(baseline)
        mutated[field] = mutated[field][::-1]
        with pytest.raises(candidate.SpotV7ReleaseCandidateRejectV1) as captured:
            candidate.parse_exact_spot_v7_release_candidate_manifest_v1(_canonical(mutated))
        assert captured.value.code == code


def test_candidate_type_has_no_public_unvalidated_constructor() -> None:
    with pytest.raises(TypeError, match="validated construction"):
        candidate.SpotV7ReleaseCandidateManifestV1()
