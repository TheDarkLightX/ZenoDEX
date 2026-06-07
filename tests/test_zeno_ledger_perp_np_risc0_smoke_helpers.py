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


def test_smoke_simulate_match_records_reject_receipts_without_mutation() -> None:
    accounts = [
        smoke._account("wallet-a", 0, 0, 10_000),
        smoke._account("wallet-b", 0, 0, 10_000),
    ]
    next_accounts, receipts = smoke._simulate_match(
        accounts,
        [
            smoke._intent("wallet-a", 1, nonce=2),
            smoke._intent("wallet-b", 1, nonce=1, expiry=0),
            smoke._intent("wallet-missing", 0, nonce=1),
        ],
        price=100,
        now_epoch=1,
        params=smoke._params(),
    )

    by_key = {(r["pubkey"], r["nonce"]): r for r in receipts}
    assert by_key[("wallet-a", 2)]["reject_code"] == "REJ_BAD_NONCE"
    assert by_key[("wallet-b", 1)]["reject_code"] == "REJ_EXPIRED"
    assert by_key[("wallet-missing", 1)]["reject_code"] == "REJ_ACCOUNT"
    assert next_accounts == sorted(accounts, key=lambda a: str(a["pubkey"]))


def test_smoke_simulate_match_collapses_duplicate_nonce_like_guest_btreemap() -> None:
    accounts = [smoke._account("wallet-a", 0, 0, 10_000)]
    _, receipts = smoke._simulate_match(
        accounts,
        [
            smoke._intent("wallet-a", 1, nonce=1),
            smoke._intent("wallet-a", 2, nonce=1),
        ],
        price=100,
        now_epoch=1,
        params=smoke._params(),
    )

    assert receipts == [
        {
            "pubkey": "wallet-a",
            "nonce": 1,
            "delta": 0,
            "rejected": True,
            "reject_code": "REJ_DUP_NONCE",
        }
    ]


def test_smoke_simulate_match_accepts_contiguous_replacement_nonce() -> None:
    accounts = [
        smoke._account("wallet-a", 0, 0, 10_000),
        smoke._account("wallet-b", 0, 0, 10_000),
        smoke._account("wallet-c", 0, 0, 10_000),
    ]
    next_accounts, receipts = smoke._simulate_match(
        accounts,
        [
            smoke._intent("wallet-a", 1, nonce=1),
            smoke._intent("wallet-a", 2, nonce=2),
            smoke._intent("wallet-b", -1, nonce=1),
            smoke._intent("wallet-c", -1, nonce=1),
        ],
        price=100,
        now_epoch=1,
        params=smoke._params(),
    )

    by_key = {(r["pubkey"], r["nonce"]): r for r in receipts}
    assert by_key[("wallet-a", 1)]["reject_code"] == "REJ_SUPERSEDED"
    assert by_key[("wallet-a", 2)]["delta"] == 2
    by_account = {account["pubkey"]: account for account in next_accounts}
    assert by_account["wallet-a"]["nonce"] == 2
    assert by_account["wallet-a"]["position_base"] == 2
