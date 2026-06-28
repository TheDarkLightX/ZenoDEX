"""Session admission store: through the API, the head only moves forward.

The adversarial bench measures the improvement (equivocation 2->1, rollback
1->0, forgery admission 5/5->0/5); these tests pin the module contract:
initialization binding, admission refusals with the store unchanged, state
tamper evidence, persistence round-trips, and the receipts-replayed audit.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

import src.integration.zeno_ledger_signature as sig
from src.integration.autonomous_governance_q_policy import (
    policy_content_hash_v1,
)
from src.integration.autonomous_governance_session import (
    continue_autonomous_governance_surface_trajectory_v1,
)
from src.integration.autonomous_governance_session_pin import (
    session_genesis_payload_v1,
    session_registry_hash_v1,
)
from src.integration.autonomous_governance_session_store import (
    admit_autonomous_governance_session_continuation_v1,
    current_session_store_head_v1,
    initialize_autonomous_governance_session_store_v1,
    verify_autonomous_governance_session_store_v1,
)
from src.integration.autonomous_governance_trajectory import (
    run_autonomous_governance_surface_trajectory_v1,
)
from src.integration.zeno_governance_authority import (
    governance_action_payload_hash_v0,
)
from tests.integration.test_autonomous_governance_session_pin import (
    _backend,
    _envelopes_for,
    _open_session,
    _policy_pin,
    _registry,
    _tau_receipt,
)

_BUDGET = {"fee_bps": 50, "funding_cap_bps": 25, "buyburn_bps": 200, "reserve_bps": 200}

pytestmark = pytest.mark.skipif(
    not sig._BLS_AVAILABLE, reason="py_ecc BLS dependency unavailable"
)


def _policy(policy_id: str = "session_store_policy_a") -> dict[str, Any]:
    policy = {
        "schema": "zenodex.autonomous_governance.q_policy.v1",
        "policy_id": policy_id,
        "version": 1,
        "safety": {
            "max_freshness_lag_epochs": 2,
            "max_divergence_bps": 75,
            "max_volatility_bps": 1_000,
            "min_liquidity_depth_bps": 1_000,
            "min_cooldown_epochs": 1,
            "emergency_pause": False,
        },
        "selection": {
            "mode": "first_admissible",
            "anti_oscillation": {"enabled": True, "parameters": ["fee_bps"]},
            "trajectory_budget": {"enabled": True, "limits": dict(_BUDGET)},
        },
        "state_bins": {"deviation_bps": [25, 100, 300]},
        "actions": [
            {"id": "hold", "deltas": {}},
            {"id": "raise_fee_10", "deltas": {"fee_bps": 10}},
        ],
        "q_layers": [
            {
                "id": "price_deviation_pressure",
                "features": ["deviation_bps"],
                "q_table": {
                    "0": {"hold": 3},
                    "1": {"hold": 3},
                    "2": {"raise_fee_10": 5, "hold": 1},
                    "3": {"raise_fee_10": 8, "hold": 1},
                },
            },
        ],
    }
    return {**policy, "policy_hash": policy_content_hash_v1(policy)}


def _surface_state() -> dict[str, int]:
    return {
        "fee_bps": 30, "buyburn_bps": 6_000, "stakers_bps": 0,
        "reserve_bps": 2_000, "hosts_bps": 2_000, "mcr_bps": 11_000,
        "ccr_bps": 15_000, "staker_bps": 5_000, "funding_cap_bps": 120,
    }


def _steps(count: int, first_epoch: int) -> list[dict[str, Any]]:
    return [
        {
            "observation": {
                "observed_price_bps": 10_400, "target_price_bps": 10_000,
                "volatility_bps": 100, "divergence_bps": 10,
                "freshness_lag_epochs": 0, "liquidity_depth_bps": 5_000,
            },
            "current_epoch": first_epoch + index,
            "proposal_epoch": first_epoch + index - 24,
        }
        for index in range(count)
    ]


def _genesis_receipt(policy: dict[str, Any]) -> dict[str, Any]:
    return run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=_steps(3, 100),
        expected_policy_hash=str(policy["policy_hash"]),
    )


def _authority_bundle(policy: dict[str, Any], receipt: dict[str, Any]) -> dict[str, Any]:
    registry = _registry()
    policy_pin = _policy_pin(policy, registry)
    opened = _open_session(policy, policy_pin, receipt, registry)
    assert opened["ok"] is True, opened["errors"]
    payload = session_genesis_payload_v1(
        policy_hash=str(policy["policy_hash"]),
        policy_pin_hash=str(policy_pin["pin_hash"]),
        genesis_trajectory_hash=str(receipt["trajectory_hash"]),
        genesis_chain_head=str(receipt["chain_head"]),
        registry_hash=session_registry_hash_v1(registry),
        proposal_epoch=10,
    )
    return {
        "policy_pin": policy_pin,
        "registry": registry,
        "signature_envelopes": _envelopes_for(governance_action_payload_hash_v0(payload)),
        "current_epoch": 20,
        "proposal_epoch": 10,
        "min_delay_epochs": 3,
        "tau_policy_receipt": _tau_receipt(),
        "backend_descriptors": [_backend().public_dict()],
        "production_mode": True,
        "genesis_pin": dict(opened["pin"]),
    }


def _genesis_pin(policy: dict[str, Any], receipt: dict[str, Any]) -> dict[str, Any]:
    return dict(_authority_bundle(policy, receipt)["genesis_pin"])


def _store(policy: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    receipt = _genesis_receipt(policy)
    authority = _authority_bundle(policy, receipt)
    init = initialize_autonomous_governance_session_store_v1(
        genesis_pin=authority.pop("genesis_pin"),
        genesis_receipt=receipt,
        policy=policy,
        **authority,
    )
    assert init["ok"] is True, init["errors"]
    return dict(init["store"]), receipt


def _continue(policy: dict[str, Any], parent: dict[str, Any], first_epoch: int) -> dict[str, Any]:
    return continue_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        previous_receipt=parent,
        steps=_steps(3, first_epoch),
        expected_policy_hash=str(policy["policy_hash"]),
    )


def test_initialize_refuses_forged_genesis_pin_without_quorum_context() -> None:
    policy = _policy()
    receipt = _genesis_receipt(policy)
    forged = dict(_genesis_pin(policy, receipt))
    forged["authority_receipt_hash"] = "0x" + "cc" * 32

    from src.integration.autonomous_governance_session_pin import _session_pin_body_hash

    body = dict(forged)
    body.pop("pin_hash")
    forged["pin_hash"] = _session_pin_body_hash(body)
    init = initialize_autonomous_governance_session_store_v1(
        genesis_pin=forged, genesis_receipt=receipt, policy=policy
    )

    assert init["ok"] is False
    assert init["store"] == {}
    assert "session_store_genesis_authority_context_required" in init["errors"]


def test_initialize_binds_pin_receipt_and_policy() -> None:
    policy = _policy()
    store, receipt = _store(policy)
    assert store["segment_count"] == 1
    head = current_session_store_head_v1(store)
    assert head["ok"] is True
    assert head["surface_state"] == receipt["final_state"]

    audit = verify_autonomous_governance_session_store_v1(store=store, policy=policy)
    assert audit["ok"] is True
    assert audit["authenticity_verified"] is True
    assert audit["scope"] == "receipts_replayed"


def test_initialize_refuses_unbound_pin_and_wrong_policy() -> None:
    policy = _policy()
    receipt = _genesis_receipt(policy)
    pin = _genesis_pin(policy, receipt)

    other_receipt = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=_steps(4, 100),
        expected_policy_hash=str(policy["policy_hash"]),
    )
    authority = _authority_bundle(policy, receipt)
    unbound = initialize_autonomous_governance_session_store_v1(
        genesis_pin=pin, genesis_receipt=other_receipt, policy=policy, **{k: v for k, v in authority.items() if k != "genesis_pin"}
    )
    assert unbound["ok"] is False
    assert unbound["store"] == {}
    assert any(
        "pin_receipt_binding_mismatch" in str(error) for error in unbound["errors"]
    )

    other_policy = _policy("session_store_policy_b")
    mismatched = initialize_autonomous_governance_session_store_v1(
        genesis_pin=pin, genesis_receipt=receipt, policy=other_policy, **{k: v for k, v in authority.items() if k != "genesis_pin"}
    )
    assert mismatched["ok"] is False
    assert "session_store_policy_hash_mismatch" in mismatched["errors"]

    junk = initialize_autonomous_governance_session_store_v1(
        genesis_pin={"schema": "junk"}, genesis_receipt=receipt, policy=policy, **{k: v for k, v in authority.items() if k != "genesis_pin"}
    )
    assert junk["ok"] is False
    assert junk["store"] == {}


def test_admission_moves_the_head_and_only_forward() -> None:
    policy = _policy()
    store, genesis_receipt = _store(policy)

    first = _continue(policy, genesis_receipt, 103)
    admission = admit_autonomous_governance_session_continuation_v1(
        store=store, receipt=first, policy=policy
    )
    assert admission["admitted"] is True, admission["errors"]
    advanced = admission["store"]
    assert advanced["segment_count"] == 2
    assert current_session_store_head_v1(advanced)["surface_state"] == first["final_state"]

    # Equivocation: the fork branch is refused and the store unchanged.
    fork = _continue(policy, genesis_receipt, 120)
    refused = admit_autonomous_governance_session_continuation_v1(
        store=advanced, receipt=fork, policy=policy
    )
    assert refused["admitted"] is False
    assert "session_store_admission_refused" in refused["errors"]
    assert any("advance_chain_head_mismatch" in str(e) for e in refused["errors"])
    assert refused["store"] == advanced

    # Rollback: re-presenting the consumed segment is refused.
    replay = admit_autonomous_governance_session_continuation_v1(
        store=advanced, receipt=first, policy=policy
    )
    assert replay["admitted"] is False
    assert replay["store"] == advanced


def test_admission_is_deterministic() -> None:
    policy = _policy()
    store, genesis_receipt = _store(policy)
    first = _continue(policy, genesis_receipt, 103)
    a = admit_autonomous_governance_session_continuation_v1(
        store=store, receipt=first, policy=policy
    )
    b = admit_autonomous_governance_session_continuation_v1(
        store=store, receipt=first, policy=policy
    )
    assert a == b
    assert a["admission_hash"] == b["admission_hash"]


def test_tampered_store_state_is_refused_everywhere() -> None:
    policy = _policy()
    store, genesis_receipt = _store(policy)
    tampered = dict(store)
    pins = [dict(pin) for pin in tampered["pin_chain"]]
    pins[-1] = {**pins[-1], "trajectory_used_final": {**dict(pins[-1]["trajectory_used_final"]), "fee_bps": 0}}
    tampered["pin_chain"] = tuple(pins)

    first = _continue(policy, genesis_receipt, 103)
    admission = admit_autonomous_governance_session_continuation_v1(
        store=tampered, receipt=first, policy=policy
    )
    assert admission["admitted"] is False
    assert "session_store_hash_mismatch" in admission["errors"]

    audit = verify_autonomous_governance_session_store_v1(store=tampered, policy=policy)
    assert audit["ok"] is False
    assert audit["authenticity_verified"] is False

    head = current_session_store_head_v1(tampered)
    assert head["ok"] is False


@pytest.mark.parametrize("store", [None, 42, "store", [], {}])
def test_malformed_store_state_is_refused(store: object) -> None:
    policy = _policy()
    receipt = _genesis_receipt(policy)
    first = _continue(policy, receipt, 103)
    admission = admit_autonomous_governance_session_continuation_v1(
        store=store, receipt=first, policy=policy
    )
    assert admission["admitted"] is False
    assert admission["ok"] is False


def test_store_state_survives_json_persistence() -> None:
    policy = _policy()
    store, genesis_receipt = _store(policy)
    first = _continue(policy, genesis_receipt, 103)
    store = admit_autonomous_governance_session_continuation_v1(
        store=store, receipt=first, policy=policy
    )["store"]

    persisted = json.loads(json.dumps(store))
    audit = verify_autonomous_governance_session_store_v1(
        store=persisted, policy=policy
    )
    assert audit["ok"] is True, audit["errors"]
    assert audit["authenticity_verified"] is True

    second = _continue(policy, first, 106)
    admission = admit_autonomous_governance_session_continuation_v1(
        store=persisted, receipt=second, policy=policy
    )
    assert admission["admitted"] is True, admission["errors"]
    assert admission["store"]["segment_count"] == 3


def test_unhashable_store_blobs_fail_closed_not_crash() -> None:
    # Codex v6 r2 P2 pair: corrupted blobs with canonical-JSON-rejected values
    # (floats, non-string keys) must yield refusals at every entry point —
    # and the refusal body must not try to hash the raw malformed input.
    policy = _policy()
    store, genesis_receipt = _store(policy)
    first = _continue(policy, genesis_receipt, 103)

    def corrupt(mutate: Any) -> dict[str, Any]:
        corrupted = dict(store)
        pins = [dict(pin) for pin in corrupted["pin_chain"]]
        pins[-1] = mutate(dict(pins[-1]))
        corrupted["pin_chain"] = tuple(pins)
        return corrupted

    float_blob = corrupt(lambda pin: {**pin, "pinned_at_epoch": 1.5})
    bad_key_blob = corrupt(lambda pin: {**pin, 42: "x"})

    for blob in (float_blob, bad_key_blob):
        admission = admit_autonomous_governance_session_continuation_v1(
            store=blob, receipt=first, policy=policy
        )
        assert admission["admitted"] is False
        assert admission["store"] == {}
        assert "session_store_unhashable" in admission["errors"]

        audit = verify_autonomous_governance_session_store_v1(
            store=blob, policy=policy
        )
        assert audit["ok"] is False
        assert "session_store_unhashable" in audit["errors"]

        head = current_session_store_head_v1(blob)
        assert head["ok"] is False


def test_non_mapping_archive_entries_are_refused_before_hashing() -> None:
    # Codex v6 r3 P2: a HASH-CONSISTENT blob with a list-of-pairs entry must
    # be refused on entry shape, never dict()-transformed after the hash check
    # into data the hash did not commit to (materialize-once); non-iterable
    # entries must refuse, not crash.
    from src.integration.autonomous_governance_session_store import (
        _store_body_hash,
    )

    policy = _policy()
    store, genesis_receipt = _store(policy)
    first = _continue(policy, genesis_receipt, 103)

    receipts = [dict(receipt) for receipt in store["receipt_archive"]]
    pairs_entry = sorted((str(k), v) for k, v in receipts[-1].items())
    body = {
        "schema": store["schema"],
        "policy_hash": store["policy_hash"],
        "pin_chain": tuple(dict(pin) for pin in store["pin_chain"]),
        "receipt_archive": (pairs_entry,),
        "segment_count": store["segment_count"],
    }
    hash_consistent = {**body, "store_hash": _store_body_hash(body)}

    blobs: list[dict[str, Any]] = [hash_consistent]
    for bad_entry in ("receipt", 42):
        corrupted = dict(store)
        corrupted["receipt_archive"] = (bad_entry,)
        blobs.append(corrupted)

    for blob in blobs:
        admission = admit_autonomous_governance_session_continuation_v1(
            store=blob, receipt=first, policy=policy
        )
        assert admission["admitted"] is False
        assert admission["store"] == {}
        assert any(
            "session_store_receipt_entry_invalid" in str(error)
            for error in admission["errors"]
        )
        assert (
            verify_autonomous_governance_session_store_v1(store=blob, policy=policy)[
                "ok"
            ]
            is False
        )
        assert current_session_store_head_v1(blob)["ok"] is False


def test_unhashable_pin_string_fields_fail_closed_not_crash() -> None:
    # Codex v6 r6 P2: a surrogate inside a KNOWN string field passes the
    # isinstance checks and must refuse at the pin-hash recompute, not raise —
    # at initialization and through advance_'s current_pin path.
    from src.integration.autonomous_governance_session_pin import (
        advance_autonomous_governance_session_v1,
    )

    policy = _policy()
    receipt = _genesis_receipt(policy)
    hostile_pin = {**_genesis_pin(policy, receipt), "policy_id": "\ud800evil"}

    authority = _authority_bundle(policy, receipt)
    init = initialize_autonomous_governance_session_store_v1(
        genesis_pin=hostile_pin, genesis_receipt=receipt, policy=policy, **{k: v for k, v in authority.items() if k != "genesis_pin"}
    )
    assert init["ok"] is False
    assert init["store"] == {}
    assert any("session_pin_unhashable" in str(e) for e in init["errors"])

    first = _continue(policy, receipt, 103)
    advance = advance_autonomous_governance_session_v1(
        current_pin=hostile_pin, receipt=first, policy=policy
    )
    assert advance["ok"] is False
    assert any("session_pin_unhashable" in str(e) for e in advance["errors"])


def test_cli_session_store_lifecycle(tmp_path: Path) -> None:
    policy = _policy()
    genesis = _genesis_receipt(policy)
    pin = _genesis_pin(policy, genesis)

    init_bundle = tmp_path / "init-session-store.json"
    init_bundle.write_text(
        json.dumps(
            {
                "policy": policy,
                "genesis_pin": pin,
                "genesis_receipt": genesis,
                **{k: v for k, v in _authority_bundle(policy, genesis).items() if k != "genesis_pin"},
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    initialized = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "init-session-store",
            str(init_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert initialized.returncode == 0, initialized.stderr
    init_result = json.loads(initialized.stdout)
    assert init_result["ok"] is True, init_result["errors"]
    store = init_result["store"]

    first = _continue(policy, genesis, 103)
    admit_bundle = tmp_path / "admit-session-continuation.json"
    admit_bundle.write_text(
        json.dumps(
            {
                "policy": policy,
                "store": store,
                "trajectory_receipt": first,
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    admitted = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "admit-session-continuation",
            str(admit_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert admitted.returncode == 0, admitted.stderr
    admission = json.loads(admitted.stdout)
    assert admission["admitted"] is True, admission["errors"]
    advanced_store = admission["store"]

    verify_bundle = tmp_path / "verify-session-store.json"
    verify_bundle.write_text(
        json.dumps({"policy": policy, "store": advanced_store}, sort_keys=True),
        encoding="utf-8",
    )
    verified = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "verify-session-store",
            str(verify_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert verified.returncode == 0, verified.stderr
    verification = json.loads(verified.stdout)
    assert verification["ok"] is True, verification["errors"]
    assert verification["authenticity_verified"] is True

    headed = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "session-store-head",
            str(verify_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert headed.returncode == 0, headed.stderr
    head = json.loads(headed.stdout)
    assert head["ok"] is True, head["errors"]
    assert head["surface_state"] == first["final_state"]


def test_boolean_segment_count_is_refused_even_hash_consistent() -> None:
    # Codex v6 r6 P2: True == 1 must not satisfy the count check; a
    # hash-consistent blob with segment_count=true is malformed.
    from src.integration.autonomous_governance_session_store import (
        _store_body_hash,
    )

    policy = _policy()
    store, genesis_receipt = _store(policy)
    body = {
        "schema": store["schema"],
        "policy_hash": store["policy_hash"],
        "pin_chain": tuple(dict(pin) for pin in store["pin_chain"]),
        "receipt_archive": tuple(dict(r) for r in store["receipt_archive"]),
        "segment_count": True,
    }
    hash_consistent = {**body, "store_hash": _store_body_hash(body)}

    first = _continue(policy, genesis_receipt, 103)
    admission = admit_autonomous_governance_session_continuation_v1(
        store=hash_consistent, receipt=first, policy=policy
    )
    assert admission["admitted"] is False
    assert "session_store_segment_count_invalid" in admission["errors"]
    assert (
        verify_autonomous_governance_session_store_v1(
            store=hash_consistent, policy=policy
        )["ok"]
        is False
    )
    assert current_session_store_head_v1(hash_consistent)["ok"] is False


def test_count_broken_blob_fails_fast_before_materialization() -> None:
    # Codex v6 r5 P2: count/cap failures must return before per-entry copies,
    # so a non-mapping entry deeper in the blob is never even inspected.
    policy = _policy()
    store, _ = _store(policy)
    broken = dict(store)
    broken["receipt_archive"] = (*broken["receipt_archive"], "extra-junk-entry")
    audit = verify_autonomous_governance_session_store_v1(store=broken, policy=policy)
    assert audit["ok"] is False
    assert "session_store_archive_count_mismatch" in audit["errors"]
    assert not any(
        "session_store_receipt_entry_invalid" in str(error)
        for error in audit["errors"]
    )


def test_archive_owns_detached_copies_against_caller_mutation() -> None:
    # Codex v6 r5 P2 pair: nested maps must not be shared with caller objects;
    # mutating the original receipt or a returned head snapshot must not
    # corrupt the store underneath its hash.
    policy = _policy()
    receipt = _genesis_receipt(policy)
    authority = _authority_bundle(policy, receipt)
    init = initialize_autonomous_governance_session_store_v1(
        genesis_pin=authority.pop("genesis_pin"),
        genesis_receipt=receipt,
        policy=policy,
        **authority,
    )
    assert init["ok"] is True
    store = init["store"]

    receipt["final_state"]["fee_bps"] = receipt["final_state"]["fee_bps"] + 999
    audit = verify_autonomous_governance_session_store_v1(store=store, policy=policy)
    assert audit["ok"] is True, audit["errors"]

    head = current_session_store_head_v1(store)
    head["head_pin"]["final_state"]["fee_bps"] = 0
    head["surface_state"]["fee_bps"] = 0
    again = verify_autonomous_governance_session_store_v1(store=store, policy=policy)
    assert again["ok"] is True, again["errors"]
    fresh = current_session_store_head_v1(store)
    assert fresh["head_pin"]["final_state"]["fee_bps"] != 0


def test_surrogate_field_names_fail_closed_not_crash() -> None:
    # Codex v6 r4 P2: an unknown field name with an unpaired surrogate must
    # not crash the refusal path when the error string is hashed into the
    # response body — at the store boundary AND through advance_'s body via a
    # hostile pin handed to the admission machinery.
    from src.integration.autonomous_governance_session_pin import (
        advance_autonomous_governance_session_v1,
    )

    policy = _policy()
    store, genesis_receipt = _store(policy)
    first = _continue(policy, genesis_receipt, 103)

    hostile_store = {**dict(store), "\ud800evil": 1}
    admission = admit_autonomous_governance_session_continuation_v1(
        store=hostile_store, receipt=first, policy=policy
    )
    assert admission["admitted"] is False
    assert any(
        "session_store_unknown_field:" in str(error) for error in admission["errors"]
    )
    assert (
        verify_autonomous_governance_session_store_v1(
            store=hostile_store, policy=policy
        )["ok"]
        is False
    )
    assert current_session_store_head_v1(hostile_store)["ok"] is False

    hostile_pin = {**_genesis_pin(policy, genesis_receipt), "\ud800evil": 1}
    advance = advance_autonomous_governance_session_v1(
        current_pin=hostile_pin, receipt=first, policy=policy
    )
    assert advance["ok"] is False
    assert any(
        "session_pin_unknown_field:" in str(error) for error in advance["errors"]
    )


def test_admission_at_segment_cap_refuses_without_bricking(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Codex v6 r1 P2: at exactly the cap, admission must refuse the extra
    # continuation (store unchanged, still serviceable) rather than append a
    # state its own validator rejects.
    import src.integration.autonomous_governance_session_store as store_module

    monkeypatch.setattr(store_module, "MAX_SESSION_STORE_SEGMENTS_V1", 2)
    policy = _policy()
    store, genesis_receipt = _store(policy)

    first = _continue(policy, genesis_receipt, 103)
    admission = admit_autonomous_governance_session_continuation_v1(
        store=store, receipt=first, policy=policy
    )
    assert admission["admitted"] is True, admission["errors"]
    at_cap = admission["store"]
    assert at_cap["segment_count"] == 2

    second = _continue(policy, first, 106)
    refused = admit_autonomous_governance_session_continuation_v1(
        store=at_cap, receipt=second, policy=policy
    )
    assert refused["admitted"] is False
    assert "session_store_segments_at_max" in refused["errors"]
    assert refused["store"] == at_cap

    # The at-cap store is NOT bricked: validation, audit, and head reads work.
    audit = verify_autonomous_governance_session_store_v1(store=at_cap, policy=policy)
    assert audit["ok"] is True, audit["errors"]
    head = current_session_store_head_v1(at_cap)
    assert head["ok"] is True
    assert head["segment_count"] == 2


def test_admission_refuses_wrong_policy_object() -> None:
    policy = _policy()
    other = _policy("session_store_policy_b")
    store, genesis_receipt = _store(policy)
    first = _continue(policy, genesis_receipt, 103)
    admission = admit_autonomous_governance_session_continuation_v1(
        store=store, receipt=first, policy=other
    )
    assert admission["admitted"] is False
    assert "session_store_policy_hash_mismatch" in admission["errors"]
