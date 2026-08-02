"""Focused F01 authoritative history-atom tests."""

from __future__ import annotations

import json
from dataclasses import replace

import pytest

from experiments.fcis_m6_f01_history_atom_check import build_atom
from src.core.fcis_m6_f01_history_atom import (
    F01HistoryAtomCodeV1,
    F01HistoryAtomError,
    F01HistoryAtomRejectV1,
    F01HistoryAtomV1,
    F01ProofContextRequirementV1,
    decode_history_atom_v1,
    encode_history_atom_v1,
)
from src.state.canonical import canonical_json_bytes


def test_complete_atom_round_trips_with_anf_context_nullifier_and_outbox() -> None:
    atom = build_atom()
    encoded = encode_history_atom_v1(atom)
    decoded = decode_history_atom_v1(encoded)

    assert type(decoded) is F01HistoryAtomV1
    assert decoded == atom
    assert atom.anf_root in encoded.decode("utf-8")
    assert atom.proof_context_root in encoded.decode("utf-8")
    assert atom.nullifier.nullifier_root in encoded.decode("utf-8")
    assert atom.outbox[0].effect_id in encoded.decode("utf-8")


def test_decoder_rejects_missing_unknown_and_noncanonical_fields() -> None:
    atom = build_atom()
    wire = json.loads(encode_history_atom_v1(atom).decode("utf-8"))
    value = wire["value"]
    assert type(value) is dict

    del value["anf_root"]
    missing = decode_history_atom_v1(canonical_json_bytes(wire))
    assert type(missing) is F01HistoryAtomRejectV1
    assert missing.code is F01HistoryAtomCodeV1.MISSING_FIELD

    unknown_wire = json.loads(encode_history_atom_v1(atom).decode("utf-8"))
    unknown_value = unknown_wire["value"]
    assert type(unknown_value) is dict
    unknown_value["foreign"] = True
    unknown = decode_history_atom_v1(canonical_json_bytes(unknown_wire))
    assert type(unknown) is F01HistoryAtomRejectV1
    assert unknown.code is F01HistoryAtomCodeV1.UNKNOWN_FIELD

    noncanonical = encode_history_atom_v1(atom).replace(b'"schema":', b' "schema":', 1)
    noncanonical_result = decode_history_atom_v1(noncanonical)
    assert type(noncanonical_result) is F01HistoryAtomRejectV1
    assert noncanonical_result.code is F01HistoryAtomCodeV1.NONCANONICAL_BYTES


def test_constructor_rejects_crossed_nullifier_and_effect() -> None:
    atom = build_atom()
    foreign_nullifier = atom.nullifier
    object.__setattr__(foreign_nullifier, "nullifier_root", "0x" + "f" * 64)
    with pytest.raises(F01HistoryAtomError, match="nullifier root"):
        replace(atom, nullifier=foreign_nullifier)

    effect_atom = build_atom()
    foreign_effect = replace(effect_atom.outbox[0], effect_id="0x" + "e" * 64)
    with pytest.raises(F01HistoryAtomError, match="effect ID"):
        replace(effect_atom, outbox=(foreign_effect,))


def test_proof_context_presence_is_closed() -> None:
    atom = build_atom()
    with pytest.raises(F01HistoryAtomError, match="sentinel"):
        replace(
            atom,
            proof_context_requirement=F01ProofContextRequirementV1.NOT_REQUIRED,
        )


def test_untrusted_nonbytes_and_wrong_collection_fail_closed() -> None:
    atom = build_atom()
    with pytest.raises(F01HistoryAtomError, match="exact F01HistoryAtomV1"):
        encode_history_atom_v1({})
    with pytest.raises(F01HistoryAtomError, match="exact tuple"):
        replace(atom, outbox=[atom.outbox[0]])
