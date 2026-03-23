from __future__ import annotations

from dataclasses import dataclass

import pytest

import src.integration.tau_net_client as tau_net_client


@dataclass(frozen=True)
class _AppStateCase:
    name: str
    raw: str
    expected_hash: str | None = None
    error_match: str | None = None


@dataclass(frozen=True)
class _StateProofCase:
    name: str
    raw: str
    expected_state_hash: str | None = None
    expected_present: bool | None = None
    error_match: str | None = None
    error_types: tuple[type[BaseException], ...] = (tau_net_client.TauNetRpcError,)


@dataclass(frozen=True)
class _TauStateCase:
    name: str
    raw: str
    expected_app_hash: str | None = None
    error_match: str | None = None


def _client_with_rpc(handler):
    client = tau_net_client.TauNetTcpClient()
    client.rpc = handler  # type: ignore[method-assign]
    return client


@pytest.mark.parametrize(
    "case",
    [
        _AppStateCase(
            name="valid_hash",
            raw='{"app_hash":"' + "ab" * 32 + '","app_state":{"schema":"zenodex/tau_app_state/v1"}}',
            expected_hash="ab" * 32,
        ),
        _AppStateCase(
            name="empty_hash_allowed",
            raw='{"app_hash":"","app_state":{"schema":"zenodex/tau_app_state/v1"}}',
            expected_hash="",
        ),
        _AppStateCase(
            name="non_object_rejected",
            raw='["not","an","object"]',
            error_match="getappstate full returned non-object JSON",
        ),
        _AppStateCase(
            name="invalid_hash_rejected",
            raw='{"app_hash":"zz","app_state":{"schema":"zenodex/tau_app_state/v1"}}',
            error_match="getappstate full app_hash must be a 64-hex string",
        ),
    ],
    ids=lambda case: case.name,
)
def test_getappstate_view_contract_parity(case: _AppStateCase) -> None:
    client = _client_with_rpc(lambda cmd: case.raw if cmd == "getappstate full" else "")
    if case.error_match is not None:
        with pytest.raises(tau_net_client.TauNetRpcError, match=case.error_match):
            client.getappstate_view()
        return
    view = client.getappstate_view()
    assert view.app_hash == case.expected_hash


@pytest.mark.parametrize(
    "case",
    [
        _StateProofCase(
            name="present_true_valid",
            raw='{"state_hash":"'
            + "cd" * 32
            + '","present":true,"proof_type":"risc0.tauswap_transition.v1","proof_bytes":321,"proof_sha256":"'
            + "ef" * 32
            + '","error":"ok"}',
            expected_state_hash="cd" * 32,
            expected_present=True,
        ),
        _StateProofCase(
            name="present_false_empty_hash_valid",
            raw='{"state_hash":"","present":false,"error":"not_ready"}',
            expected_state_hash="",
            expected_present=False,
        ),
        _StateProofCase(
            name="present_not_bool_rejected",
            raw='{"state_hash":"","present":"yes"}',
            error_match="getstateproof full present must be a bool",
        ),
        _StateProofCase(
            name="present_true_missing_hash_rejected",
            raw='{"state_hash":"","present":true}',
            error_match="getstateproof full state_hash must be a 64-hex string when present=true",
        ),
        _StateProofCase(
            name="empty_proof_type_rejected",
            raw='{"state_hash":"' + "cd" * 32 + '","present":true,"proof_type":" "}',
            error_match="getstateproof full proof_type must be a non-empty string",
        ),
        _StateProofCase(
            name="negative_proof_bytes_rejected",
            raw='{"state_hash":"' + "cd" * 32 + '","present":true,"proof_bytes":-1}',
            error_match="getstateproof full proof_bytes must be a non-negative integer",
            error_types=(ValueError,),
        ),
        _StateProofCase(
            name="invalid_proof_sha_rejected",
            raw='{"state_hash":"' + "cd" * 32 + '","present":true,"proof_sha256":"zz"}',
            error_match="getstateproof full proof_sha256 must be a 64-hex string",
        ),
        _StateProofCase(
            name="non_string_error_rejected",
            raw='{"state_hash":"' + "cd" * 32 + '","present":true,"error":7}',
            error_match="getstateproof full error must be a string",
        ),
    ],
    ids=lambda case: case.name,
)
def test_getstateproof_view_contract_parity(case: _StateProofCase) -> None:
    client = _client_with_rpc(lambda cmd: case.raw if cmd == "getstateproof full" else "")
    if case.error_match is not None:
        with pytest.raises(case.error_types, match=case.error_match):
            client.getstateproof_view()
        return
    view = client.getstateproof_view()
    assert view.state_hash == case.expected_state_hash
    assert view.present is case.expected_present


@pytest.mark.parametrize(
    "case",
    [
        _TauStateCase(
            name="valid_with_app_hash",
            raw='{"rules":"rule_text","accounts_hash":"' + "12" * 32 + '","app_hash":"' + "ab" * 32 + '"}',
            expected_app_hash="ab" * 32,
        ),
        _TauStateCase(
            name="valid_empty_app_hash",
            raw='{"rules":"rule_text","accounts_hash":"' + "12" * 32 + '","app_hash":""}',
            expected_app_hash="",
        ),
        _TauStateCase(
            name="present_false_rejected",
            raw='{"present":false,"error":"tau_state_not_found"}',
            error_match="reported no committed tau_state payload: tau_state_not_found",
        ),
        _TauStateCase(
            name="nonempty_error_rejected",
            raw='{"error":"transport_down","rules":"rule_text","accounts_hash":"' + "12" * 32 + '"}',
            error_match="returned an error: transport_down",
        ),
        _TauStateCase(
            name="rules_not_string_rejected",
            raw='{"rules":1,"accounts_hash":"' + "12" * 32 + '"}',
            error_match="rules must be a string",
        ),
        _TauStateCase(
            name="accounts_hash_invalid_rejected",
            raw='{"rules":"rule_text","accounts_hash":"zz"}',
            error_match="accounts_hash must be a 64-hex string",
        ),
        _TauStateCase(
            name="app_hash_invalid_rejected",
            raw='{"rules":"rule_text","accounts_hash":"' + "12" * 32 + '","app_hash":"zz"}',
            error_match="app_hash must be a 64-hex string",
        ),
        _TauStateCase(
            name="present_not_bool_rejected",
            raw='{"present":"no","rules":"rule_text","accounts_hash":"' + "12" * 32 + '"}',
            error_match="present must be a bool",
        ),
        _TauStateCase(
            name="error_not_string_rejected",
            raw='{"error":9,"rules":"rule_text","accounts_hash":"' + "12" * 32 + '"}',
            error_match="error must be a string",
        ),
    ],
    ids=lambda case: case.name,
)
def test_gettaustate_view_contract_parity(case: _TauStateCase) -> None:
    client = _client_with_rpc(lambda cmd: case.raw if cmd == f"gettaustate {'ab' * 32}" else "")
    if case.error_match is not None:
        with pytest.raises(tau_net_client.TauNetRpcError, match=case.error_match):
            client.gettaustate_view("ab" * 32)
        return
    view = client.gettaustate_view("ab" * 32)
    assert view.app_hash == case.expected_app_hash
