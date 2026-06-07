from __future__ import annotations

import hashlib

from tools import zeno_ledger_perp_np_risc0_real_proof_smoke as smoke


def _u32(n: int) -> bytes:
    return n.to_bytes(4, "big", signed=False)


def _u64(n: int) -> bytes:
    return n.to_bytes(8, "big", signed=False)


def _i128(n: int) -> bytes:
    return n.to_bytes(16, "big", signed=True)


def _write_str(h: "hashlib._Hash", value: str) -> None:
    raw = value.encode("utf-8")
    h.update(_u32(len(raw)))
    h.update(raw)


def test_smoke_participant_set_hash_uses_guest_domain_sorted_dedup() -> None:
    accounts = [
        {"pubkey": "wallet-b"},
        {"pubkey": "wallet-a"},
        {"pubkey": "wallet-b"},
    ]
    h = hashlib.sha256()
    h.update(b"zenodex.participant_set.v1:")
    h.update(_u32(2))
    _write_str(h, "wallet-a")
    _write_str(h, "wallet-b")

    assert smoke._participant_set_hash("ignored-chain", "ignored-market", accounts) == h.hexdigest()


def test_smoke_receipts_root_uses_guest_status_and_optional_reject_code() -> None:
    receipts = [
        {"pubkey": "wallet-a", "nonce": 2, "delta": 7, "rejected": False, "reject_code": ""},
        {"pubkey": "wallet-b", "nonce": 3, "delta": 0, "rejected": True, "reject_code": "REJ_MARGIN"},
    ]
    h = hashlib.sha256()
    h.update(b"zenodex.perps_np.receipts.v1:")
    h.update(_u32(2))
    _write_str(h, "wallet-a")
    h.update(_u64(2))
    _write_str(h, "filled")
    h.update(_i128(7))
    h.update(bytes([0]))
    _write_str(h, "wallet-b")
    h.update(_u64(3))
    _write_str(h, "rejected")
    h.update(_i128(0))
    h.update(bytes([1]))
    _write_str(h, "REJ_MARGIN")

    assert smoke._receipts_root(receipts) == h.hexdigest()


def test_smoke_state_delta_hash_uses_guest_pre_post_app_hash_only() -> None:
    pre = "11" * 32
    post = "22" * 32
    h = hashlib.sha256()
    h.update(b"zenodex.state_delta.v1:")
    h.update(bytes.fromhex(pre))
    h.update(bytes.fromhex(post))

    assert (
        smoke._state_delta_hash(
            chain_id="ignored-chain",
            market_id="ignored-market",
            pre_state_root=pre,
            post_state_root=post,
            operation_hash="33" * 32,
            receipts_root="44" * 32,
        )
        == h.hexdigest()
    )


def test_smoke_case_builder_expected_hashes_follow_current_snapshot_path() -> None:
    case = smoke._base_four_wallet()
    expected = case["_python_expected"]
    assert expected["pre_app_hash"] == case["_current_pre_app_hash"]
    assert expected["post_app_hash"] == case["_current_post_app_hash"]
    assert expected["state_delta_hash"] == smoke._state_delta_hash(
        chain_id=case["chain_id"],
        market_id=case["market_id"],
        pre_state_root=case["_current_pre_app_hash"],
        post_state_root=case["_current_post_app_hash"],
        operation_hash=case["operation_hash"],
        receipts_root=expected["receipts_root"],
    )
