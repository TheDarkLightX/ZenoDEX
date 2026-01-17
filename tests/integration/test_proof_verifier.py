# [TESTER] v1

from __future__ import annotations

import sys

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig, apply_ops
from src.integration.operations import create_settlement_operation
from src.integration.proof_verifier import MisconfiguredProofVerifier, ProofVerifierConfig, SubprocessProofVerifier, make_proof_verifier
from src.state.canonical import CANONICAL_ENCODING_VERSION, canonical_json_bytes, domain_sep_bytes, sha256_hex
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.state_root import compute_state_root


def _intent_signing_dict_from_tx_intent(intent_dict: dict) -> dict:
    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    return {
        "module": intent.module,
        "version": intent.version,
        "kind": intent.kind.value,
        "intent_id": intent.intent_id,
        "sender_pubkey": intent.sender_pubkey,
        "deadline": intent.deadline,
        "fields": intent.fields or {},
        **({"salt": intent.salt} if intent.salt is not None else {}),
    }


def _settlement_commitment_dict_from_settlement(settlement_obj: dict) -> dict:
    # Must match the canonical commitment rules in src/integration/dex_engine.py.
    out = {k: v for k, v in settlement_obj.items() if k not in ("batch_ref", "events")}
    fills = out.get("fills") or []
    out["fills"] = [
        {k: v for k, v in f.items() if v is not None and k != "reason"} for f in fills if isinstance(f, dict)
    ]
    return out


def _batch_commitment(*, signing_dicts: list[dict], settlement_obj: dict) -> str:
    payload = {
        "schema": "zenodex_batch",
        "schema_version": 1,
        "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
        "intents": signing_dicts,
        "settlement": _settlement_commitment_dict_from_settlement(settlement_obj),
    }
    return sha256_hex(domain_sep_bytes("dex_batch", version=1) + canonical_json_bytes(payload))


def test_batch_commitment_is_independent_of_dict_insertion_order() -> None:
    intent_id = "0x" + "11" * 32
    sender = "0x" + "aa" * 48

    signing_a = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 1,
        "fields": {"asset0": "A", "asset1": "B", "fee_bps": 30, "amount0": 1, "amount1": 2},
    }
    # Same content, different insertion order (including nested fields).
    signing_b = {
        "fields": {"amount1": 2, "amount0": 1, "fee_bps": 30, "asset1": "B", "asset0": "A"},
        "deadline": 1,
        "sender_pubkey": sender,
        "intent_id": intent_id,
        "kind": "CREATE_POOL",
        "version": "0.1",
        "module": "TauSwap",
    }

    settlement_a = {
        "module": "TauSwap",
        "version": "0.1",
        "included_intents": [[intent_id, "FILL"]],
        "fills": [{"intent_id": intent_id, "action": "FILL", "amount_in_filled": 1, "amount_out_filled": 1, "fee_paid": 0}],
        "balance_deltas": [],
        "reserve_deltas": [],
        "lp_deltas": [],
    }
    settlement_b = {
        "lp_deltas": [],
        "reserve_deltas": [],
        "balance_deltas": [],
        "fills": [{"fee_paid": 0, "amount_out_filled": 1, "amount_in_filled": 1, "action": "FILL", "intent_id": intent_id}],
        "included_intents": [[intent_id, "FILL"]],
        "version": "0.1",
        "module": "TauSwap",
    }

    payload_a = {
        "schema": "zenodex_batch",
        "schema_version": 1,
        "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
        "intents": [signing_a],
        "settlement": settlement_a,
    }
    payload_b = {
        "settlement": settlement_b,
        "intents": [signing_b],
        "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
        "schema_version": 1,
        "schema": "zenodex_batch",
    }

    c1 = sha256_hex(domain_sep_bytes("dex_batch", version=1) + canonical_json_bytes(payload_a))
    c2 = sha256_hex(domain_sep_bytes("dex_batch", version=1) + canonical_json_bytes(payload_b))
    assert c1 == c2


def test_engine_rejects_proof_when_verifier_enabled_but_missing_cmd() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "03" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }

    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    settlement = compute_settlement(intents=[intent], pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_obj = create_settlement_operation(settlement)["3"]

    settlement_obj_with_proof = dict(settlement_obj)
    settlement_obj_with_proof["proof"] = {
        "scheme": "dummy",
    }

    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            allow_external_tools=True,
            consensus_mode=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=None),
        ),
        state=state,
        operations={"2": [intent_dict], "3": settlement_obj_with_proof},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "misconfigured" in res.error


def test_engine_proof_binding_is_fail_closed_on_pre_state_commitment_mismatch() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "03" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }

    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    settlement = compute_settlement(intents=[intent], pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_obj = create_settlement_operation(settlement)["3"]

    settlement_obj_with_proof = dict(settlement_obj)
    settlement_obj_with_proof["proof"] = {
        "pre_state_commitment": "0x" + "00" * 32,
        "batch_commitment": "0x" + "00" * 32,
    }

    cmd = [sys.executable, "-c", "import sys; sys.stdin.buffer.read(); print('{\"ok\":true}')"]
    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            allow_external_tools=True,
            consensus_mode=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=cmd),
        ),
        state=state,
        operations={"2": [intent_dict], "3": settlement_obj_with_proof},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "pre_state_commitment mismatch" in res.error


def test_engine_proof_binding_is_fail_closed_on_batch_commitment_mismatch() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "03" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }

    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    settlement = compute_settlement(intents=[intent], pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_obj = create_settlement_operation(settlement)["3"]

    settlement_obj_with_proof = dict(settlement_obj)
    settlement_obj_with_proof["proof"] = {
        "pre_state_commitment": compute_state_root(balances=state.balances, pools=state.pools, lp_balances=state.lp_balances),
        "batch_commitment": "0x" + "00" * 32,
    }

    cmd = [sys.executable, "-c", "import sys; sys.stdin.buffer.read(); print('{\"ok\":true}')"]
    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            allow_external_tools=True,
            consensus_mode=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=cmd),
        ),
        state=state,
        operations={"2": [intent_dict], "3": settlement_obj_with_proof},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert not res.ok
    assert res.error is not None
    assert "batch_commitment mismatch" in res.error


def test_make_proof_verifier_requires_absolute_cmd_when_path_lookup_disabled() -> None:
    v = make_proof_verifier(
        ProofVerifierConfig(
            enabled=True,
            verifier_cmd=["python3", "-c", "print('{\"ok\":true}')"],
            allow_path_lookup=False,
        )
    )
    assert isinstance(v, MisconfiguredProofVerifier)


def test_engine_accepts_proof_when_commitments_match_and_verifier_ok() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id = "0x" + "04" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }

    from src.integration.operations import parse_intents

    intent = parse_intents({"2": [intent_dict]})[0]
    settlement = compute_settlement(intents=[intent], pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_obj = create_settlement_operation(settlement)["3"]

    pre_state_commitment = compute_state_root(balances=state.balances, pools=state.pools, lp_balances=state.lp_balances)
    batch_commitment = _batch_commitment(
        signing_dicts=[_intent_signing_dict_from_tx_intent(intent_dict)],
        settlement_obj=settlement_obj,
    )

    settlement_obj_with_proof = dict(settlement_obj)
    settlement_obj_with_proof["proof"] = {
        "pre_state_commitment": pre_state_commitment,
        "batch_commitment": batch_commitment,
        "scheme": "dummy",
    }

    cmd = [sys.executable, "-c", "import sys; sys.stdin.buffer.read(); print('{\"ok\":true}')"]
    res = apply_ops(
        config=DexEngineConfig(
            allow_missing_settlement=False,
            require_intent_signatures=False,
            allow_external_tools=True,
            consensus_mode=False,
            proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=cmd),
        ),
        state=state,
        operations={"2": [intent_dict], "3": settlement_obj_with_proof},
        block_timestamp=0,
        tx_sender_pubkey=sender,
    )
    assert res.ok, res.error


def test_engine_proof_commitment_ignores_optional_nulls_and_reject_reasons() -> None:
    sender = "0x" + "aa" * 48
    asset0 = "0x" + "11" * 32
    asset1 = "0x" + "22" * 32
    intent_id_create = "0x" + "05" * 32
    intent_id_reject = "0x" + "06" * 32

    balances = BalanceTable()
    balances.set(sender, min(asset0, asset1), 1000)
    balances.set(sender, max(asset0, asset1), 2000)
    state = DexState(balances=balances, pools={}, lp_balances=LPTable())

    intent_dict_create = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": intent_id_create,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "asset0": min(asset0, asset1),
        "asset1": max(asset0, asset1),
        "fee_bps": 30,
        "amount0": 1000,
        "amount1": 2000,
        "created_at": 1,
    }
    # Intentionally references an unknown pool_id so it rejects with POOL_NOT_FOUND.
    intent_dict_reject = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": intent_id_reject,
        "sender_pubkey": sender,
        "deadline": 9999999999,
        "pool_id": "0x" + "ff" * 32,
        "asset_in": asset0,
        "asset_out": asset1,
        "amount_in": 1,
        "min_amount_out": 0,
        "recipient": sender,
    }

    from src.integration.operations import parse_intents

    intents = parse_intents({"2": [intent_dict_create, intent_dict_reject]})
    settlement = compute_settlement(intents=intents, pools={}, balances=balances, lp_balances=state.lp_balances)
    settlement_obj_with_nulls = create_settlement_operation(settlement)["3"]

    # Construct a logically equivalent encoding:
    # - remove optional null keys from fills
    # - omit batch_ref
    # - mutate reject reason (should be ignored by commitment)
    settlement_obj_min = {k: v for k, v in settlement_obj_with_nulls.items() if k != "batch_ref"}
    compact_fills = []
    for fill in settlement_obj_min.get("fills", []):
        if not isinstance(fill, dict):
            continue
        compact = {k: v for k, v in fill.items() if v is not None}
        if compact.get("action") == "REJECT":
            compact["reason"] = "SOME_OTHER_REASON"
        compact_fills.append(compact)
    settlement_obj_min["fills"] = compact_fills

    pre_state_commitment = compute_state_root(balances=state.balances, pools=state.pools, lp_balances=state.lp_balances)
    batch_commitment = _batch_commitment(
        signing_dicts=[
            _intent_signing_dict_from_tx_intent(intent_dict_create),
            _intent_signing_dict_from_tx_intent(intent_dict_reject),
        ],
        settlement_obj=settlement_obj_min,
    )

    cmd = [sys.executable, "-c", "import sys; sys.stdin.buffer.read(); print('{\"ok\":true}')"]
    for settlement_obj in (settlement_obj_with_nulls, settlement_obj_min):
        settlement_obj_with_proof = dict(settlement_obj)
        settlement_obj_with_proof["proof"] = {
            "pre_state_commitment": pre_state_commitment,
            "batch_commitment": batch_commitment,
        }
        res = apply_ops(
            config=DexEngineConfig(
                allow_missing_settlement=False,
                require_intent_signatures=False,
                allow_external_tools=True,
                consensus_mode=False,
                proof_config=ProofVerifierConfig(enabled=True, verifier_cmd=cmd),
            ),
            state=state,
            operations={"2": [intent_dict_create, intent_dict_reject], "3": settlement_obj_with_proof},
            block_timestamp=0,
            tx_sender_pubkey=sender,
        )
        assert res.ok, res.error


def test_subprocess_verifier_rejects_non_canonical_payload() -> None:
    cmd = [sys.executable, "-c", "import sys; sys.exit(0)"]
    v = SubprocessProofVerifier(cmd=cmd, timeout_s=1.0, max_bytes=10_000, max_stdout_bytes=1000, max_stderr_bytes=1000)
    ok, err = v.verify({"bad_float": 1.25})
    assert ok is False
    assert err is not None
    assert "invalid proof payload encoding" in err


def test_subprocess_verifier_limits_stdout() -> None:
    cmd = [sys.executable, "-c", "print('A' * 50000)"]
    v = SubprocessProofVerifier(cmd=cmd, timeout_s=2.0, max_bytes=10_000, max_stdout_bytes=1000, max_stderr_bytes=1000)
    ok, err = v.verify({"ok": True})
    assert ok is False
    assert err == "verifier stdout too large"


def test_subprocess_verifier_times_out_if_verifier_never_reads_stdin() -> None:
    # This verifier never reads stdin; large payload should hit backpressure and time out.
    cmd = [sys.executable, "-c", "import time; time.sleep(10)"]
    v = SubprocessProofVerifier(cmd=cmd, timeout_s=0.2, max_bytes=500_000, max_stdout_bytes=1000, max_stderr_bytes=1000)
    ok, err = v.verify({"x": "A" * 200_000})
    assert ok is False
    assert err == "proof verification timed out"


def test_subprocess_verifier_times_out_if_verifier_never_exits() -> None:
    # This verifier reads stdin then sleeps; we should kill it on timeout.
    cmd = [sys.executable, "-c", "import sys, time; sys.stdin.buffer.read(); time.sleep(10)"]
    v = SubprocessProofVerifier(cmd=cmd, timeout_s=0.2, max_bytes=10_000, max_stdout_bytes=1000, max_stderr_bytes=1000)
    ok, err = v.verify({"ok": True})
    assert ok is False
    assert err == "proof verification timed out"
