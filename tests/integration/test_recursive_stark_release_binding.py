from __future__ import annotations

import hashlib
import json
import pickle
from dataclasses import FrozenInstanceError

import pytest

from src.integration import recursive_stark_release_binding as release_binding_module
from src.integration.recursive_stark_release_binding import (
    MAX_RELEASE_BINDING_BYTES_V1,
    RECURSIVE_STARK_RELEASE_BINDING_SCHEMA_V1,
    RecursiveStarkReleaseBindingError,
    TrustedRecursiveStarkReleaseBinding,
    load_recursive_stark_release_binding_v1,
    recursive_stark_release_binding_config_digest_v1,
)

AUTHORITY_SHA256 = "ef9d2c732f2bd79d1b617a266566d9f9b566516c95248220d5b6198c1538754d"
REPLAY_SHA256 = "sha256:9b50fb6eec7c7220556ac570b817ba6187439938fae67fe00cf9c200796e0ea2"
CHAIN_ID = "tau-devnet-recursive-smoke"
CONFIG_DIGEST = "0xc64d52198f049eb8b5aa7280e1a007d64ffbbf0c80beb4ede14b4292ddc1efd1"


def _body() -> dict[str, object]:
    return {
        "schema": RECURSIVE_STARK_RELEASE_BINDING_SCHEMA_V1,
        "chain_id": CHAIN_ID,
        "epoch_id": 1,
        "proof_profile": "recursive_epoch_v1",
        "authority_manifest_sha256": AUTHORITY_SHA256,
        "replay_manifest_sha256": REPLAY_SHA256,
    }


def _canonical(body: dict[str, object] | None = None) -> bytes:
    return json.dumps(
        _body() if body is None else body,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("ascii")


def _load(raw: bytes):
    return load_recursive_stark_release_binding_v1(
        raw,
        expected_config_digest=recursive_stark_release_binding_config_digest_v1(raw),
        expected_chain_id=CHAIN_ID,
        expected_epoch_id=1,
        expected_proof_profile="recursive_epoch_v1",
    )


def test_loader_returns_frozen_scope_bound_value() -> None:
    raw = _canonical()

    binding = _load(raw)

    assert binding.schema == RECURSIVE_STARK_RELEASE_BINDING_SCHEMA_V1
    assert binding.chain_id == CHAIN_ID
    assert binding.epoch_id == 1
    assert binding.proof_profile == "recursive_epoch_v1"
    assert binding.authority_manifest_sha256 == AUTHORITY_SHA256
    assert binding.replay_manifest_sha256 == REPLAY_SHA256
    with pytest.raises(FrozenInstanceError):
        binding.chain_id = "attacker-chain"


def test_trusted_type_exposes_no_unchecked_factory() -> None:
    assert not hasattr(TrustedRecursiveStarkReleaseBinding, "_from_validated")
    assert not hasattr(release_binding_module, "_trusted_binding_from_validated")


def test_trusted_type_rejects_direct_construction_and_subclassing() -> None:
    with pytest.raises(TypeError, match="created by the loader"):
        TrustedRecursiveStarkReleaseBinding()
    with pytest.raises(TypeError, match="cannot be subclassed"):
        type("ForgedRecursiveStarkReleaseBinding", (TrustedRecursiveStarkReleaseBinding,), {})


def test_trusted_type_rejects_pickle_serialization_and_reconstruction() -> None:
    with pytest.raises(TypeError, match="cannot be pickled"):
        pickle.dumps(_load(_canonical()))

    payload = (
        b"csrc.integration.recursive_stark_release_binding\n"
        b"TrustedRecursiveStarkReleaseBinding\n(tR."
    )
    with pytest.raises(TypeError, match="created by the loader"):
        pickle.loads(payload)


def test_config_digest_is_domain_separated_and_deterministic() -> None:
    raw = _canonical()

    first = recursive_stark_release_binding_config_digest_v1(raw)
    second = recursive_stark_release_binding_config_digest_v1(raw)

    assert first == second
    assert first == CONFIG_DIGEST
    assert first != "0x" + hashlib.sha256(raw).hexdigest()


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("authority_manifest_sha256", "33" * 32),
        ("replay_manifest_sha256", "sha256:" + "44" * 32),
    ],
)
def test_loader_rejects_digest_bound_artifact_substitution(field: str, value: str) -> None:
    trusted_raw = _canonical()
    trusted_digest = recursive_stark_release_binding_config_digest_v1(trusted_raw)
    substituted = _body()
    substituted[field] = value

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        load_recursive_stark_release_binding_v1(
            _canonical(substituted),
            expected_config_digest=trusted_digest,
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )

    assert exc_info.value.code == "CONFIG_DIGEST_MISMATCH"


@pytest.mark.parametrize(
    ("expected_chain_id", "expected_epoch_id", "expected_proof_profile", "code"),
    [
        ("attacker-chain", 1, "recursive_epoch_v1", "CHAIN_ID_MISMATCH"),
        (CHAIN_ID, 2, "recursive_epoch_v1", "EPOCH_ID_MISMATCH"),
        (CHAIN_ID, 1, "recursive_epoch_v2", "PROOF_PROFILE_MISMATCH"),
    ],
)
def test_loader_rejects_trusted_scope_mismatch(
    expected_chain_id: str,
    expected_epoch_id: int,
    expected_proof_profile: str,
    code: str,
) -> None:
    raw = _canonical()

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        load_recursive_stark_release_binding_v1(
            raw,
            expected_config_digest=recursive_stark_release_binding_config_digest_v1(raw),
            expected_chain_id=expected_chain_id,
            expected_epoch_id=expected_epoch_id,
            expected_proof_profile=expected_proof_profile,
        )

    assert exc_info.value.code == code


@pytest.mark.parametrize("mutation", ["unknown", "missing"])
def test_loader_rejects_ambiguous_field_sets(mutation: str) -> None:
    body = _body()
    if mutation == "unknown":
        body["proof_report"] = {"ok": True}
    else:
        body.pop("replay_manifest_sha256")

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        load_recursive_stark_release_binding_v1(
            _canonical(body),
            expected_config_digest="0x" + "55" * 32,
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )

    assert exc_info.value.code == "FIELD_SET_MISMATCH"


def test_loader_rejects_duplicate_json_key() -> None:
    raw = _canonical()
    duplicate = raw[:-1] + b',"schema":"substituted"}'

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        load_recursive_stark_release_binding_v1(
            duplicate,
            expected_config_digest="0x" + "55" * 32,
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )

    assert exc_info.value.code == "DUPLICATE_JSON_KEY"


def test_duplicate_key_error_does_not_echo_control_characters() -> None:
    raw = b'{"schema\\u001b\\n":1,"schema\\u001b\\n":2}'

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        load_recursive_stark_release_binding_v1(
            raw,
            expected_config_digest="0x" + "55" * 32,
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )

    assert exc_info.value.code == "DUPLICATE_JSON_KEY"
    assert exc_info.value.detail == "release binding contains a duplicate JSON key"
    assert "\x1b" not in str(exc_info.value)
    assert "\n" not in str(exc_info.value)


def test_loader_rejects_noncanonical_json_bytes() -> None:
    raw = json.dumps(_body(), indent=2, sort_keys=True).encode("ascii")

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        load_recursive_stark_release_binding_v1(
            raw,
            expected_config_digest="0x" + "55" * 32,
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )

    assert exc_info.value.code == "NONCANONICAL_JSON"


@pytest.mark.parametrize(
    ("epoch_literal", "code"),
    [("7.0", "FLOAT_FORBIDDEN"), ("NaN", "NONFINITE_FORBIDDEN")],
)
def test_loader_rejects_float_and_nonfinite_numbers(epoch_literal: str, code: str) -> None:
    raw = _canonical().replace(b'"epoch_id":1', f'"epoch_id":{epoch_literal}'.encode("ascii"))

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        load_recursive_stark_release_binding_v1(
            raw,
            expected_config_digest="0x" + "55" * 32,
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )

    assert exc_info.value.code == code


def test_loader_rejects_non_ascii_bytes() -> None:
    raw = _canonical().replace(CHAIN_ID.encode("ascii"), CHAIN_ID.encode("ascii") + b"\xc3\xa9")

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        load_recursive_stark_release_binding_v1(
            raw,
            expected_config_digest="0x" + "55" * 32,
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )

    assert exc_info.value.code == "ASCII_REQUIRED"


def test_loader_rejects_split_view_bytes_subclass() -> None:
    trusted_raw = _canonical()
    malicious_body = _body()
    malicious_body["authority_manifest_sha256"] = "33" * 32
    malicious_body["replay_manifest_sha256"] = "sha256:" + "44" * 32
    malicious_text = _canonical(malicious_body).decode("ascii")

    class SplitViewBytes(bytes):
        def decode(self, encoding: str = "utf-8", errors: str = "strict") -> str:
            return malicious_text

        def __ne__(self, other: object) -> bool:
            return False

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        load_recursive_stark_release_binding_v1(
            SplitViewBytes(trusted_raw),
            expected_config_digest=recursive_stark_release_binding_config_digest_v1(trusted_raw),
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )

    assert exc_info.value.code == "BINDING_TYPE"


def test_loader_rejects_hostile_expected_string_subclasses() -> None:
    raw = _canonical()
    digest = recursive_stark_release_binding_config_digest_v1(raw)

    class HostileStr(str):
        def encode(self, encoding: str = "utf-8", errors: str = "strict") -> bytes:
            return CHAIN_ID.encode(encoding, errors)

        def __eq__(self, other: object) -> bool:
            return True

    with pytest.raises(RecursiveStarkReleaseBindingError) as digest_exc:
        load_recursive_stark_release_binding_v1(
            raw,
            expected_config_digest=HostileStr(digest),
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )
    assert digest_exc.value.code == "EXPECTED_CONFIG_DIGEST_INVALID"

    with pytest.raises(RecursiveStarkReleaseBindingError) as scope_exc:
        load_recursive_stark_release_binding_v1(
            raw,
            expected_config_digest=digest,
            expected_chain_id=HostileStr("attacker-chain"),
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )
    assert scope_exc.value.code == "EXPECTED_CHAIN_ID_INVALID"


def test_loader_rejects_oversized_input_before_json_parsing() -> None:
    raw = b" " * (MAX_RELEASE_BINDING_BYTES_V1 + 1)

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        load_recursive_stark_release_binding_v1(
            raw,
            expected_config_digest="0x" + "55" * 32,
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
        )

    assert exc_info.value.code == "BINDING_BYTE_LIMIT"


def test_rejection_returns_no_trusted_value_or_output(capsys: pytest.CaptureFixture[str]) -> None:
    raw = _canonical()
    trusted_values: list[object] = []

    with pytest.raises(RecursiveStarkReleaseBindingError) as exc_info:
        trusted_values.append(
            load_recursive_stark_release_binding_v1(
                raw,
                expected_config_digest="0x" + "55" * 32,
                expected_chain_id=CHAIN_ID,
                expected_epoch_id=1,
                expected_proof_profile="recursive_epoch_v1",
            )
        )

    assert exc_info.value.code == "CONFIG_DIGEST_MISMATCH"
    assert trusted_values == []
    assert capsys.readouterr() == ("", "")


def test_loader_has_no_proof_or_report_override_channel() -> None:
    raw = _canonical()

    with pytest.raises(TypeError, match="unexpected keyword argument"):
        load_recursive_stark_release_binding_v1(
            raw,
            expected_config_digest=recursive_stark_release_binding_config_digest_v1(raw),
            expected_chain_id=CHAIN_ID,
            expected_epoch_id=1,
            expected_proof_profile="recursive_epoch_v1",
            proof_report={"ok": True},  # type: ignore[call-arg]
        )
