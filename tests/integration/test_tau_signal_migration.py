from __future__ import annotations

from copy import deepcopy
from dataclasses import FrozenInstanceError
from hashlib import sha256
from itertools import product
from typing import Callable, NamedTuple

import pytest

from src.agents.strategy_ir import (
    NotionalCaps,
    PolicyBackend,
    RiskLimits,
    StrategyAction,
    StrategyIR,
    StrategyTemplate,
    StrategyWindow,
)
from src.agents.tau_policy_adapter import (
    build_external_signal_source_registry_guard_tau_policy_receipt,
)
from src.integration.autotrader_signal_profile import (
    SignalProfile,
    decode_profile,
    encode_profile,
)
from src.integration.autotrader_signal_registry import (
    ExternalSignalSourceRegistry,
    ExternalSignalSourceRegistryEntry,
)
from src.integration.autotrader_signals import (
    EXTERNAL_SIGNAL_COMPACT_SCHEMA,
    EXTERNAL_SIGNAL_SCHEMA,
    AutoTraderObservationPacket,
    ExternalSignalObservation,
    QuoteReceiptSignalPacket,
    SignalSourceKind,
    SignalTrustTier,
    external_signal_observation_from_dict,
    external_signal_observations_from_object,
)
from src.state.canonical import canonical_json_bytes

_SOURCE_BY_INDEX = (
    SignalSourceKind.ROUTE_QUOTE_RECEIPT,
    SignalSourceKind.LOCAL_PROTOCOL_STATE,
    SignalSourceKind.ATTESTED_EXTERNAL,
    SignalSourceKind.ADVISORY_EXTERNAL,
)
_TRUST_BY_INDEX = (
    SignalTrustTier.ADVISORY,
    SignalTrustTier.ATTESTED,
    SignalTrustTier.VERIFIED,
    SignalTrustTier.PROTOCOL,
)

# This is the transport contract written independently of the implementation.
# Wire bits are source[0:2], trust[2:4], freshness[4], auth[5], advisory[6].
_SOURCE_INDEX_BY_KIND = {
    SignalSourceKind.ROUTE_QUOTE_RECEIPT: 0,
    SignalSourceKind.LOCAL_PROTOCOL_STATE: 1,
    SignalSourceKind.ATTESTED_EXTERNAL: 2,
    SignalSourceKind.ADVISORY_EXTERNAL: 3,
}
_TRUST_INDEX_BY_TIER = {
    SignalTrustTier.ADVISORY: 0,
    SignalTrustTier.ATTESTED: 1,
    SignalTrustTier.VERIFIED: 2,
    SignalTrustTier.PROTOCOL: 3,
}
_COMPACT_FIELDS = frozenset({"schema", "signal_id", "source_id", "profile_code", "tags"})


class _ProfileCase(NamedTuple):
    source_kind: SignalSourceKind
    trust_tier: SignalTrustTier
    freshness_ok: bool
    auth_ok: bool
    advisory_only: bool


class _Outcome(NamedTuple):
    accepted: bool
    value: object | None
    error_type: str | None
    error: str | None


def _profile_cases() -> tuple[_ProfileCase, ...]:
    return tuple(
        _ProfileCase(source, trust, freshness, auth, advisory)
        for source, trust, freshness, auth, advisory in product(
            _SOURCE_BY_INDEX,
            _TRUST_BY_INDEX,
            (False, True),
            (False, True),
            (False, True),
        )
    )


def _manual_wire_code(case: _ProfileCase) -> int:
    """Return the independently specified seven-bit wire code."""

    return (
        _SOURCE_INDEX_BY_KIND[case.source_kind]
        | (_TRUST_INDEX_BY_TIER[case.trust_tier] << 2)
        | (int(case.freshness_ok) << 4)
        | (int(case.auth_ok) << 5)
        | (int(case.advisory_only) << 6)
    )


def _manual_accepts(case: _ProfileCase) -> bool:
    """Mirror the current external contract using names, not numeric helpers."""

    if case.source_kind is SignalSourceKind.ADVISORY_EXTERNAL:
        return case.trust_tier is SignalTrustTier.ADVISORY and case.advisory_only
    if case.source_kind is SignalSourceKind.ATTESTED_EXTERNAL:
        if case.trust_tier not in (SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED):
            return False
        return case.advisory_only or (case.auth_ok and case.freshness_ok)
    return False


def _manual_error(case: _ProfileCase) -> str | None:
    """Return the expected V1 guard error in its documented precedence order."""

    if case.source_kind not in (
        SignalSourceKind.ADVISORY_EXTERNAL,
        SignalSourceKind.ATTESTED_EXTERNAL,
    ):
        return "external signal contract rejected: source_kind_unsupported"
    if case.trust_tier is SignalTrustTier.PROTOCOL:
        return "external signal contract rejected: trust_tier_invalid"
    if case.source_kind is SignalSourceKind.ADVISORY_EXTERNAL:
        if case.trust_tier is not SignalTrustTier.ADVISORY or not case.advisory_only:
            return "external signal contract rejected: advisory_external_invalid"
        return None
    if case.trust_tier not in (SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED):
        return "external signal contract rejected: attested_external_invalid"
    if not case.advisory_only and not (case.auth_ok and case.freshness_ok):
        return "external signal contract rejected: attested_external_invalid"
    return None


def _manual_profile(case: _ProfileCase) -> SignalProfile:
    return SignalProfile(
        source_index=_SOURCE_INDEX_BY_KIND[case.source_kind],
        trust_index=_TRUST_INDEX_BY_TIER[case.trust_tier],
        freshness_ok=case.freshness_ok,
        auth_ok=case.auth_ok,
        advisory_only=case.advisory_only,
    )


def _v1_payload(case: _ProfileCase, *, signal_id: str = "signal.alpha") -> dict[str, object]:
    return {
        "schema": EXTERNAL_SIGNAL_SCHEMA,
        "signal_id": signal_id,
        "source_id": "provider.alpha",
        "source_kind": case.source_kind.value,
        "trust_tier": case.trust_tier.value,
        "freshness_ok": case.freshness_ok,
        "auth_ok": case.auth_ok,
        "advisory_only": case.advisory_only,
        "tags": ["market", "market"],
    }


def _v2_payload(case: _ProfileCase, *, signal_id: str = "signal.alpha") -> dict[str, object]:
    return {
        "schema": EXTERNAL_SIGNAL_COMPACT_SCHEMA,
        "signal_id": signal_id,
        "source_id": "provider.alpha",
        "profile_code": _manual_wire_code(case),
        "tags": ["market"],
    }


def _outcome(
    parser: Callable[[dict[str, object]], ExternalSignalObservation],
    payload: dict[str, object],
) -> _Outcome:
    try:
        value = parser(payload)
    except (TypeError, ValueError, ArithmeticError) as exc:
        return _Outcome(False, None, type(exc).__name__, str(exc))
    return _Outcome(True, value, None, None)


def _primary_signal() -> QuoteReceiptSignalPacket:
    return QuoteReceiptSignalPacket(
        current_epoch=10,
        quote_epoch=9,
        asset_in="zUSD",
        asset_out="BTC",
        amount_in=100,
        amount_out=95,
        receipt_hash="receipt.hash.1",
    )


def _local_strategy() -> StrategyIR:
    return StrategyIR(
        strategy_id="local.strat.1",
        owner_pubkey="owner.pubkey.1",
        policy_backend=PolicyBackend.LOCAL,
        template=StrategyTemplate.DCA,
        asset_universe=("BTC", "zUSD"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        notional_caps=NotionalCaps(per_order_max=100, per_window_max=500, lifetime_max=1_000),
        risk_limits=RiskLimits(max_slippage_bps=100, max_oracle_staleness_epochs=3),
        strategy_window=StrategyWindow(valid_from_epoch=1, valid_until_epoch=100),
        template_params={
            "fixed_order_size": 100,
            "cadence_epochs": 4,
            "asset_in": "zUSD",
            "asset_out": "BTC",
        },
    )


def _registry_for(signal: ExternalSignalObservation) -> ExternalSignalSourceRegistry:
    allowed_tiers = (
        (SignalTrustTier.ADVISORY,)
        if signal.source_kind is SignalSourceKind.ADVISORY_EXTERNAL
        else (SignalTrustTier.ATTESTED, SignalTrustTier.VERIFIED)
    )
    return ExternalSignalSourceRegistry(
        entries=(
            ExternalSignalSourceRegistryEntry(
                source_id=signal.source_id,
                source_kind=signal.source_kind,
                allowed_trust_tiers=allowed_tiers,
                require_advisory_only=signal.source_kind is SignalSourceKind.ADVISORY_EXTERNAL,
                require_auth=False,
                require_freshness=False,
            ),
        )
    )


def _packet_outcome(signal: ExternalSignalObservation) -> _Outcome:
    try:
        packet = AutoTraderObservationPacket(
            current_epoch=10,
            primary_signal=_primary_signal(),
            external_signals=(signal,),
            signal_source_registry=_registry_for(signal),
        )
    except (TypeError, ValueError, ArithmeticError) as exc:
        return _Outcome(False, None, type(exc).__name__, str(exc))
    return _Outcome(True, packet.to_dict(), None, None)


def _hash(value: object) -> str:
    return sha256(canonical_json_bytes(value)).hexdigest()


def test_profile_codec_exhaustively_matches_independent_wire_bit_layout() -> None:
    cases = _profile_cases()
    assert len(cases) == 128

    for case in cases:
        profile = _manual_profile(case)
        expected_code = _manual_wire_code(case)
        actual_code = encode_profile(profile)

        assert actual_code == expected_code
        assert 0 <= actual_code < 128
        assert decode_profile(actual_code) == profile


def test_profile_value_is_immutable() -> None:
    profile = _manual_profile(
        _ProfileCase(
            SignalSourceKind.ATTESTED_EXTERNAL,
            SignalTrustTier.VERIFIED,
            True,
            True,
            False,
        )
    )
    with pytest.raises(FrozenInstanceError):
        profile.source_index = 0  # type: ignore[misc]


def test_v2_exhaustive_128_profiles_preserve_v1_outcome_and_exact_guard_error() -> None:
    v1_accepted = 0
    v2_accepted = 0

    for case in _profile_cases():
        v1 = _outcome(external_signal_observation_from_dict, _v1_payload(case))
        v2 = _outcome(external_signal_observation_from_dict, _v2_payload(case))
        expected_error = _manual_error(case)

        assert v1.accepted is _manual_accepts(case)
        assert v1.error == expected_error
        assert v2.accepted == v1.accepted
        assert v2.error_type == v1.error_type
        assert v2.error == v1.error

        if v1.accepted:
            v1_accepted += 1
        if v2.accepted:
            v2_accepted += 1
            assert isinstance(v1.value, ExternalSignalObservation)
            assert isinstance(v2.value, ExternalSignalObservation)
            assert v2.value == v1.value
            assert v2.value.to_dict() == v1.value.to_dict()

    assert v1_accepted == 14
    assert v2_accepted == 14


def test_v2_reserved_bit_rejects_all_128_reserved_codes() -> None:
    for code in range(0x80, 0x100):
        with pytest.raises(ValueError, match="code_reserved"):
            decode_profile(code)
        payload = _v2_payload(
            _ProfileCase(
                SignalSourceKind.ADVISORY_EXTERNAL,
                SignalTrustTier.ADVISORY,
                False,
                False,
                True,
            )
        )
        payload["profile_code"] = code
        with pytest.raises(ValueError, match="code_reserved"):
            external_signal_observation_from_dict(payload)


def test_v2_compact_shape_is_closed_and_uses_exact_schema() -> None:
    valid = _v2_payload(
        _ProfileCase(
            SignalSourceKind.ADVISORY_EXTERNAL,
            SignalTrustTier.ADVISORY,
            True,
            False,
            True,
        )
    )
    assert set(valid) == _COMPACT_FIELDS
    assert external_signal_observation_from_dict(valid).to_dict()["schema"] == EXTERNAL_SIGNAL_SCHEMA

    for missing in sorted(_COMPACT_FIELDS):
        malformed = dict(valid)
        del malformed[missing]
        if missing == "schema":
            with pytest.raises(TypeError, match="external signal source_kind must be a string"):
                external_signal_observation_from_dict(malformed)
        else:
            with pytest.raises(ValueError, match="external signal compact fields"):
                external_signal_observation_from_dict(malformed)

    malformed = dict(valid)
    malformed["source_kind"] = "advisory_external"
    with pytest.raises(ValueError, match="external signal compact fields"):
        external_signal_observation_from_dict(malformed)

    malformed = dict(valid)
    malformed["trust_tier"] = "advisory"
    with pytest.raises(ValueError, match="external signal compact fields"):
        external_signal_observation_from_dict(malformed)

    wrong_schema = dict(valid)
    wrong_schema["schema"] = "zenodex/autotrader-external-signal/v1"
    with pytest.raises((TypeError, ValueError)):
        external_signal_observation_from_dict(wrong_schema)


@pytest.mark.parametrize("bad_code", [True, False, 1.0, 1.5, "1", None])
def test_v2_profile_code_requires_exact_int(bad_code: object) -> None:
    payload = _v2_payload(
        _ProfileCase(
            SignalSourceKind.ADVISORY_EXTERNAL,
            SignalTrustTier.ADVISORY,
            True,
            False,
            True,
        )
    )
    payload["profile_code"] = bad_code
    with pytest.raises(TypeError, match="code_type"):
        external_signal_observation_from_dict(payload)


@pytest.mark.parametrize("bad_code", [-1, 256, 10**30])
def test_v2_profile_code_rejects_out_of_u8_range(bad_code: int) -> None:
    payload = _v2_payload(
        _ProfileCase(
            SignalSourceKind.ADVISORY_EXTERNAL,
            SignalTrustTier.ADVISORY,
            True,
            False,
            True,
        )
    )
    payload["profile_code"] = bad_code
    with pytest.raises(ValueError, match="code_range"):
        external_signal_observation_from_dict(payload)


def test_v2_parser_rejects_non_object_and_bad_tags() -> None:
    with pytest.raises(TypeError, match="external signal entry must be an object"):
        external_signal_observation_from_dict([])  # type: ignore[arg-type]

    payload = _v2_payload(
        _ProfileCase(
            SignalSourceKind.ADVISORY_EXTERNAL,
            SignalTrustTier.ADVISORY,
            True,
            False,
            True,
        )
    )
    payload["tags"] = "market"
    with pytest.raises(ValueError, match="external signal tags must be a list"):
        external_signal_observation_from_dict(payload)


def test_legacy_v1_normalization_and_hash_remain_stable() -> None:
    case = _ProfileCase(
        SignalSourceKind.ADVISORY_EXTERNAL,
        SignalTrustTier.ADVISORY,
        True,
        False,
        True,
    )
    v1_payload = _v1_payload(case)
    v1 = external_signal_observation_from_dict(v1_payload)
    compact = v1.to_compact_dict()
    v2 = external_signal_observation_from_dict(compact)

    assert v1.to_dict()["schema"] == EXTERNAL_SIGNAL_SCHEMA
    assert v2.to_dict() == v1.to_dict()
    assert _hash(v2.to_dict()) == _hash(v1.to_dict())
    assert set(compact) == _COMPACT_FIELDS
    assert compact["profile_code"] == _manual_wire_code(case)

    legacy_extension = dict(v1_payload)
    legacy_extension["legacy_extension"] = "retained-v1-acceptance"
    assert external_signal_observation_from_dict(legacy_extension).to_dict() == v1.to_dict()


@pytest.mark.parametrize("schema_mode", ["v1", "unknown", "missing"])
def test_legacy_v1_shape_ignores_profile_code_and_preserves_schema_semantics(
    schema_mode: str,
) -> None:
    case = _ProfileCase(
        SignalSourceKind.ADVISORY_EXTERNAL,
        SignalTrustTier.ADVISORY,
        True,
        False,
        True,
    )
    payload = _v1_payload(case)
    payload["profile_code"] = 0
    if schema_mode == "unknown":
        payload["schema"] = "zenodex/autotrader-external-signal/legacy"
    elif schema_mode == "missing":
        del payload["schema"]

    parsed = external_signal_observation_from_dict(payload)

    assert parsed.source_kind is SignalSourceKind.ADVISORY_EXTERNAL
    assert parsed.trust_tier is SignalTrustTier.ADVISORY
    assert parsed.advisory_only is True
    assert parsed.to_dict()["schema"] == EXTERNAL_SIGNAL_SCHEMA
    assert "profile_code" not in parsed.to_dict()


def _assert_v1_v2_boundary_parity(
    *,
    case: _ProfileCase,
    field: str,
    value: object,
) -> tuple[_Outcome, _Outcome]:
    v1_payload = _v1_payload(case)
    v2_payload = _v2_payload(case)
    v1_payload[field] = value
    v2_payload[field] = deepcopy(value)

    v1 = _outcome(external_signal_observation_from_dict, v1_payload)
    v2 = _outcome(external_signal_observation_from_dict, v2_payload)
    assert v2.accepted == v1.accepted
    assert v2.error_type == v1.error_type
    assert v2.error == v1.error
    if v1.accepted:
        assert isinstance(v1.value, ExternalSignalObservation)
        assert isinstance(v2.value, ExternalSignalObservation)
        assert v2.value == v1.value
        assert v2.value.to_dict() == v1.value.to_dict()
    return v1, v2


@pytest.mark.parametrize(
    ("field", "value", "expected_accepted"),
    [
        ("signal_id", "", False),
        ("signal_id", "x", True),
        ("signal_id", "s" * 128, True),
        ("signal_id", "s" * 129, False),
        ("signal_id", "bad signal!", False),
        ("signal_id", "  signal.trimmed  ", True),
        ("signal_id", 1, False),
        ("signal_id", True, False),
        ("signal_id", 1.0, False),
        ("signal_id", None, False),
        ("source_id", "", False),
        ("source_id", "x", True),
        ("source_id", "s" * 128, True),
        ("source_id", "s" * 129, False),
        ("source_id", "bad source!", False),
        ("source_id", "  provider.trimmed  ", True),
        ("source_id", 1, False),
        ("source_id", True, False),
        ("source_id", 1.0, False),
        ("source_id", None, False),
    ],
)
def test_v1_v2_id_boundary_corpus_preserves_outcome_and_fields(
    field: str,
    value: object,
    expected_accepted: bool,
) -> None:
    case = _ProfileCase(
        SignalSourceKind.ADVISORY_EXTERNAL,
        SignalTrustTier.ADVISORY,
        True,
        False,
        True,
    )
    v1, _v2 = _assert_v1_v2_boundary_parity(case=case, field=field, value=value)
    assert v1.accepted is expected_accepted


@pytest.mark.parametrize(
    ("tags", "expected_accepted"),
    [
        ([], True),
        (["x"], True),
        (["t" * 128], True),
        (["t" * 129], False),
        ([""], False),
        (["bad tag!"], False),
        (["  market  ", "market", "market"], True),
        (["x"] * 128, True),
        (["x"] * 129, True),
        ("market", False),
        ([1], False),
        (None, False),
        (("market",), True),
    ],
)
def test_v1_v2_tag_boundary_corpus_preserves_outcome_and_fields(
    tags: object,
    expected_accepted: bool,
) -> None:
    case = _ProfileCase(
        SignalSourceKind.ADVISORY_EXTERNAL,
        SignalTrustTier.ADVISORY,
        True,
        False,
        True,
    )
    v1, _v2 = _assert_v1_v2_boundary_parity(case=case, field="tags", value=tags)
    assert v1.accepted is expected_accepted
    if v1.accepted:
        assert isinstance(v1.value, ExternalSignalObservation)
        if tags == ["  market  ", "market", "market"]:
            assert v1.value.tags == ("market",)


def test_bulk_loader_accepts_v2_and_preserves_v1_values() -> None:
    accepted = []
    compact_rows = []
    for case in _profile_cases():
        v1 = _outcome(external_signal_observation_from_dict, _v1_payload(case))
        if not v1.accepted:
            continue
        assert isinstance(v1.value, ExternalSignalObservation)
        accepted.append(v1.value)
        compact_rows.append(v1.value.to_compact_dict())

    loaded = external_signal_observations_from_object({"external_signals": compact_rows})
    assert loaded == tuple(accepted)
    assert len(loaded) == 14


def test_bulk_loader_rejects_mixed_reserved_input_atomically_and_recovers() -> None:
    advisory_case = _ProfileCase(
        SignalSourceKind.ADVISORY_EXTERNAL,
        SignalTrustTier.ADVISORY,
        True,
        False,
        True,
    )
    trusted_case = _ProfileCase(
        SignalSourceKind.ATTESTED_EXTERNAL,
        SignalTrustTier.VERIFIED,
        True,
        True,
        False,
    )
    valid_rows = [
        _v2_payload(advisory_case, signal_id="signal.advisory"),
        _v2_payload(trusted_case, signal_id="signal.trusted"),
    ]
    mixed_payload: dict[str, object] = {
        "external_signals": [
            valid_rows[0],
            {**_v2_payload(advisory_case, signal_id="signal.reserved"), "profile_code": 128},
            valid_rows[1],
        ]
    }
    original_input = deepcopy(mixed_payload)

    with pytest.raises(ValueError, match="code_reserved"):
        external_signal_observations_from_object(mixed_payload)

    assert mixed_payload == original_input

    valid_payload: dict[str, object] = {"external_signals": deepcopy(valid_rows)}
    valid_input_before = deepcopy(valid_payload)
    first_load = external_signal_observations_from_object(valid_payload)
    second_load = external_signal_observations_from_object(valid_payload)
    assert first_load == second_load
    assert valid_payload == valid_input_before
    assert len(first_load) == 2


def test_actual_packet_registry_and_tau_receipt_have_v1_v2_parity() -> None:
    packet_accepted = 0
    strategy = _local_strategy()

    for case in _profile_cases():
        v1_outcome = _outcome(external_signal_observation_from_dict, _v1_payload(case))
        v2_outcome = _outcome(external_signal_observation_from_dict, _v2_payload(case))
        if not v1_outcome.accepted:
            continue
        assert isinstance(v1_outcome.value, ExternalSignalObservation)
        assert isinstance(v2_outcome.value, ExternalSignalObservation)
        v1_signal = v1_outcome.value
        v2_signal = v2_outcome.value
        v1_registry = _registry_for(v1_signal)
        v2_registry = _registry_for(v2_signal)

        v1_binding = v1_registry.validate(v1_signal)
        v2_binding = v2_registry.validate(v2_signal)
        assert v2_binding == v1_binding
        assert v1_binding.ok is True

        v1_receipt = build_external_signal_source_registry_guard_tau_policy_receipt(
            strategy=strategy,
            signal=v1_signal,
            registry=v1_registry,
        )
        v2_receipt = build_external_signal_source_registry_guard_tau_policy_receipt(
            strategy=strategy,
            signal=v2_signal,
            registry=v2_registry,
        )
        assert v2_receipt.to_dict() == v1_receipt.to_dict()
        assert v1_receipt.expected_ok == v1_binding.ok
        assert v2_receipt.expected_ok == v2_binding.ok

        v1_packet = _packet_outcome(v1_signal)
        v2_packet = _packet_outcome(v2_signal)
        assert v2_packet.accepted == v1_packet.accepted
        assert v2_packet.error_type == v1_packet.error_type
        assert v2_packet.error == v1_packet.error
        if v1_packet.accepted:
            packet_accepted += 1
            assert v2_packet.value == v1_packet.value

    # The packet contract additionally partitions signals into advisory or trusted.
    assert packet_accepted == 6


def test_tau_receipt_missing_registry_rejects_identically_after_compact_decode() -> None:
    case = _ProfileCase(
        SignalSourceKind.ATTESTED_EXTERNAL,
        SignalTrustTier.VERIFIED,
        True,
        True,
        False,
    )
    v1 = external_signal_observation_from_dict(_v1_payload(case))
    v2 = external_signal_observation_from_dict(_v2_payload(case))
    strategy = _local_strategy()
    v1_receipt = build_external_signal_source_registry_guard_tau_policy_receipt(
        strategy=strategy,
        signal=v1,
        registry=None,
    )
    v2_receipt = build_external_signal_source_registry_guard_tau_policy_receipt(
        strategy=strategy,
        signal=v2,
        registry=None,
    )
    assert v1_receipt.to_dict() == v2_receipt.to_dict()
    assert v1_receipt.expected_ok is False


def test_named_swap_flags_mutant_is_caught_by_field_parity() -> None:
    case = _ProfileCase(
        SignalSourceKind.ATTESTED_EXTERNAL,
        SignalTrustTier.VERIFIED,
        True,
        False,
        False,
    )
    correct_code = _manual_wire_code(case)
    swapped_code = (
        correct_code & ~(1 << 4) & ~(1 << 5)
    ) | (1 << 4 if case.auth_ok else 0) | (1 << 5 if case.freshness_ok else 0)

    assert correct_code != swapped_code
    decoded_correct = decode_profile(correct_code)
    decoded_swapped = decode_profile(swapped_code)
    assert decoded_correct.freshness_ok is True
    assert decoded_correct.auth_ok is False
    assert decoded_swapped.freshness_ok is False
    assert decoded_swapped.auth_ok is True

    # Both verdicts reject, so checking only accepted/rejected would miss this mutation.
    original = _outcome(external_signal_observation_from_dict, _v1_payload(case))
    swapped_payload = _v2_payload(case)
    swapped_payload["profile_code"] = swapped_code
    swapped = _outcome(external_signal_observation_from_dict, swapped_payload)
    assert original.accepted is False
    assert swapped.accepted is False
    assert swapped.error == original.error
    assert decoded_swapped != _manual_profile(case)
