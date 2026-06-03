"""HTTP bridge tests for the local in-memory confidential sealed-bid API.

These tests are self-contained (stdlib only, no Chrome, no npm). They boot the
real :mod:`src.integration.api_server` on a loopback port and drive the full
commit -> open-reveal -> reveal -> settle lifecycle exactly as the Confidential
Workbench UI does, asserting fail-closed behavior, bidder-slot binding (NOT
identity auth — bidder_id is unauthenticated), phase gating, and the honest
claim boundary (no production claim; no asset movement; no signature auth).
"""

from __future__ import annotations

import json
import threading
from http.client import HTTPConnection

import pytest

from src.core.sealed_bid_auction import sealed_bid_reveal_hash


def _start_test_server(*, sealed_bid_enabled: bool = True, attestation_api_enabled: bool = True):
    from src.integration import api_server
    from src.integration.confidential_feature_status import load_confidential_feature_status_from_env
    from src.integration.confidential_sealed_bid_api import SealedBidBatchTable
    from src.state.confidential_requests import ConfidentialRequestTable

    httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
    httpd.cors_origins = set()  # type: ignore[attr-defined]
    httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)  # type: ignore[attr-defined]
    httpd.perps_api_enabled = False  # type: ignore[attr-defined]
    httpd.perps_wallet_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_tau_wallet_api_enabled = False  # type: ignore[attr-defined]
    httpd.zusd_monetary_wallet_api_enabled = False  # type: ignore[attr-defined]
    httpd.autotrader_live_api_enabled = False  # type: ignore[attr-defined]
    httpd.confidential_attestation_api_enabled = bool(attestation_api_enabled)  # type: ignore[attr-defined]
    httpd.dex_api_enabled = False  # type: ignore[attr-defined]
    httpd.demo_api_token = ""  # type: ignore[attr-defined]

    status = load_confidential_feature_status_from_env().to_public_dict()
    # Override only the one field the sealed-bid gate consults so the harness is
    # not coupled to ambient env state.
    status["sealed_bid_enabled"] = bool(sealed_bid_enabled)
    httpd.confidential_feature_status = status  # type: ignore[attr-defined]
    httpd.confidential_request_table = ConfidentialRequestTable()  # type: ignore[attr-defined]
    httpd.confidential_request_lock = threading.Lock()  # type: ignore[attr-defined]
    httpd.confidential_sealed_bid_table = SealedBidBatchTable()  # type: ignore[attr-defined]

    t = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01}, daemon=True)
    t.start()
    host, port = httpd.server_address[:2]
    return httpd, t, str(host), int(port)


def _stop_test_server(httpd, thread: threading.Thread) -> None:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)


def _post(host: str, port: int, path: str, body: dict[str, object]) -> tuple[int, dict[str, object]]:
    conn = HTTPConnection(host, port, timeout=3.0)
    conn.request("POST", path, body=json.dumps(body), headers={"Content-Type": "application/json"})
    resp = conn.getresponse()
    payload = json.loads(resp.read().decode("utf-8"))
    return int(resp.status), payload


def _get(host: str, port: int, path: str) -> tuple[int, dict[str, object]]:
    conn = HTTPConnection(host, port, timeout=3.0)
    conn.request("GET", path)
    resp = conn.getresponse()
    payload = json.loads(resp.read().decode("utf-8"))
    return int(resp.status), payload


def _commitment(*, quantity: int, limit_price: int, nonce: str) -> str:
    # Re-derive the commitment exactly as the browser does (verified to match the
    # Python domain-separated hash in src.core.sealed_bid_auction).
    return sealed_bid_reveal_hash(quantity=quantity, limit_price=limit_price, nonce=nonce)


# --- Happy path ------------------------------------------------------------


def test_sealed_bid_full_flow_settles_accounting_only() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        batch_id = "ui-sealed-bid-flow"
        alice_nonce, bob_nonce = "alice-n", "bob-n"
        alice_commit = _commitment(quantity=4, limit_price=105, nonce=alice_nonce)
        bob_commit = _commitment(quantity=3, limit_price=103, nonce=bob_nonce)

        status, body = _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 5, "bond_amount": 7,
        })
        assert status == 200 and body["ok"] is True
        assert body["batch"]["phase"] == "commit"
        assert body["production_security_claim"] is False
        assert body["asset_settlement_available"] is False

        status, body = _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "alice", "commitment": alice_commit, "bond_amount": 7,
        })
        assert status == 200 and body["ok"] is True
        assert str(body["receipt_hash"]).startswith("0x")
        # The commit receipt must NOT leak private quantity/price/nonce.
        receipt_body = body["receipt"]["body"]
        assert "nonce" not in receipt_body
        assert "quantity" not in receipt_body
        assert "limit_price" not in receipt_body
        assert alice_nonce not in json.dumps(body["receipt"])

        status, body = _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "bob", "commitment": bob_commit, "bond_amount": 7,
        })
        assert status == 200 and body["ok"] is True

        status, body = _post(host, port, "/api/confidential/sealed-bid/open-reveal", {"batch_id": batch_id})
        assert status == 200 and body["batch"]["phase"] == "reveal"

        status, body = _post(host, port, "/api/confidential/sealed-bid/reveal", {
            "batch_id": batch_id, "bidder_id": "alice", "quantity": 4, "limit_price": 105, "nonce": alice_nonce,
        })
        assert status == 200 and body["ok"] is True

        status, body = _post(host, port, "/api/confidential/sealed-bid/reveal", {
            "batch_id": batch_id, "bidder_id": "bob", "quantity": 3, "limit_price": 103, "nonce": bob_nonce,
        })
        assert status == 200 and body["ok"] is True

        status, body = _post(host, port, "/api/confidential/sealed-bid/settle", {"batch_id": batch_id})
        assert status == 200 and body["ok"] is True
        assert body["batch"]["phase"] == "settled"
        # Honest boundary: accounting-only, no asset movement.
        assert body["asset_settlement_executed"] is False
        assert body["asset_settlement_available"] is False
        assert body["production_security_claim"] is False
        assert "production" not in body["claim_scope"]
        # 5 units for sale, Alice (price 105, qty 4) fills first, Bob fills 1 at clearing.
        settlement = body["settlement"]
        assert settlement["total_filled"] == 5
        assert settlement["clearing_price"] == 103
        # Both revealed -> no bond slashed.
        assert body["bond_outcome"]["total_slashed"] == 0
        assert body["bond_outcome"]["total_refunded"] == 14
    finally:
        _stop_test_server(httpd, t)


# --- Fail-closed gates -----------------------------------------------------


def test_sealed_bid_endpoints_404_when_attestation_api_disabled() -> None:
    httpd, t, host, port = _start_test_server(attestation_api_enabled=False)
    try:
        status, body = _get(host, port, "/api/confidential/sealed-bid/status")
        # Route is invisible (no handler claims it) -> 404 not_found.
        assert status == 404
        assert body["error"] == "not_found"
        status, body = _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": "x", "units_for_sale": 1, "bond_amount": 1,
        })
        assert status == 404
    finally:
        _stop_test_server(httpd, t)


def test_sealed_bid_endpoints_503_when_sealed_bid_disabled() -> None:
    httpd, t, host, port = _start_test_server(sealed_bid_enabled=False)
    try:
        status, body = _get(host, port, "/api/confidential/sealed-bid/status")
        assert status == 503
        assert body["error"] == "sealed_bid_disabled"
        status, body = _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": "x", "units_for_sale": 1, "bond_amount": 1,
        })
        assert status == 503
        assert body["error"] == "sealed_bid_disabled"
    finally:
        _stop_test_server(httpd, t)


# --- Account-binding -------------------------------------------------------


def test_sealed_bid_reveal_wrong_nonce_rejected_and_no_state_change() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        batch_id = "binding-nonce"
        commit = _commitment(quantity=4, limit_price=105, nonce="real-nonce")
        _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 5, "bond_amount": 7,
        })
        _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "alice", "commitment": commit, "bond_amount": 7,
        })
        _post(host, port, "/api/confidential/sealed-bid/open-reveal", {"batch_id": batch_id})
        # Wrong nonce -> commitment mismatch -> reject, reveal not recorded.
        status, body = _post(host, port, "/api/confidential/sealed-bid/reveal", {
            "batch_id": batch_id, "bidder_id": "alice", "quantity": 4, "limit_price": 105, "nonce": "WRONG",
        })
        assert status == 400
        assert body["error"] == "reveal_commitment_mismatch"
        # Settling now should slash the (unrevealed) bond — proving reveal was a no-op.
        status, body = _post(host, port, "/api/confidential/sealed-bid/settle", {"batch_id": batch_id})
        assert status == 200
        assert body["bond_outcome"]["total_slashed"] == 7
        assert body["bond_outcome"]["slashed_bid_count"] == 1
        assert body["settlement"]["total_filled"] == 0
    finally:
        _stop_test_server(httpd, t)


def test_sealed_bid_reveal_from_uncommitted_bidder_rejected() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        batch_id = "binding-bidder"
        commit = _commitment(quantity=2, limit_price=100, nonce="n")
        _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 5, "bond_amount": 7,
        })
        _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "alice", "commitment": commit, "bond_amount": 7,
        })
        _post(host, port, "/api/confidential/sealed-bid/open-reveal", {"batch_id": batch_id})
        # Mallory never committed; even with the *correct* params (same hash as
        # alice's commitment) the bidder-identity binding rejects the reveal.
        status, body = _post(host, port, "/api/confidential/sealed-bid/reveal", {
            "batch_id": batch_id, "bidder_id": "mallory", "quantity": 2, "limit_price": 100, "nonce": "n",
        })
        assert status == 404
        assert body["error"] == "no_commit_for_bidder"
    finally:
        _stop_test_server(httpd, t)


def test_sealed_bid_double_commit_rejected() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        batch_id = "double-commit"
        commit = _commitment(quantity=2, limit_price=100, nonce="n")
        _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 5, "bond_amount": 7,
        })
        status, _ = _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "alice", "commitment": commit, "bond_amount": 7,
        })
        assert status == 200
        status, body = _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "alice", "commitment": commit, "bond_amount": 7,
        })
        assert status == 409
        assert body["error"] == "bidder_already_committed"
    finally:
        _stop_test_server(httpd, t)


def test_sealed_bid_duplicate_commitment_from_other_bidder_rejected() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        batch_id = "copied-commitment"
        commit = _commitment(quantity=2, limit_price=100, nonce="alice-secret")
        _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 5, "bond_amount": 7,
        })
        _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "alice", "commitment": commit, "bond_amount": 7,
        })
        # Mallory copies Alice's commitment (cannot reveal it; lacks the preimage).
        status, body = _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "mallory", "commitment": commit, "bond_amount": 7,
        })
        assert status == 409
        assert body["error"] == "duplicate_commitment"
    finally:
        _stop_test_server(httpd, t)


# --- Phase gating ----------------------------------------------------------


def test_sealed_bid_reveal_before_open_rejected() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        batch_id = "phase-reveal-early"
        commit = _commitment(quantity=2, limit_price=100, nonce="n")
        _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 5, "bond_amount": 7,
        })
        _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "alice", "commitment": commit, "bond_amount": 7,
        })
        # Still in commit phase — reveal must be rejected.
        status, body = _post(host, port, "/api/confidential/sealed-bid/reveal", {
            "batch_id": batch_id, "bidder_id": "alice", "quantity": 2, "limit_price": 100, "nonce": "n",
        })
        assert status == 409
        assert body["error"] == "phase_not_reveal"
    finally:
        _stop_test_server(httpd, t)


def test_sealed_bid_settle_before_reveal_phase_rejected() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        batch_id = "phase-settle-early"
        _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 5, "bond_amount": 7,
        })
        status, body = _post(host, port, "/api/confidential/sealed-bid/settle", {"batch_id": batch_id})
        assert status == 409
        assert body["error"] == "phase_not_reveal"
    finally:
        _stop_test_server(httpd, t)


def test_sealed_bid_commit_after_open_reveal_rejected() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        batch_id = "phase-commit-late"
        commit_a = _commitment(quantity=2, limit_price=100, nonce="a")
        commit_b = _commitment(quantity=2, limit_price=100, nonce="b")
        _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 5, "bond_amount": 7,
        })
        _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "alice", "commitment": commit_a, "bond_amount": 7,
        })
        _post(host, port, "/api/confidential/sealed-bid/open-reveal", {"batch_id": batch_id})
        status, body = _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "bob", "commitment": commit_b, "bond_amount": 7,
        })
        assert status == 409
        assert body["error"] == "phase_not_commit"
    finally:
        _stop_test_server(httpd, t)


# --- Unknown batch / malformed input ---------------------------------------


def test_sealed_bid_unknown_batch_rejected() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": "nope", "bidder_id": "alice",
            "commitment": _commitment(quantity=1, limit_price=1, nonce="n"), "bond_amount": 1,
        })
        assert status == 404
        assert body["error"] == "unknown_batch"
    finally:
        _stop_test_server(httpd, t)


def test_sealed_bid_bad_commitment_rejected() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        batch_id = "bad-commitment"
        _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 5, "bond_amount": 7,
        })
        status, body = _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "alice", "commitment": "not-hex", "bond_amount": 7,
        })
        assert status == 400
        assert body["error"] == "bad_request"
    finally:
        _stop_test_server(httpd, t)


def test_sealed_bid_status_reports_honest_boundary() -> None:
    httpd, t, host, port = _start_test_server()
    try:
        status, body = _get(host, port, "/api/confidential/sealed-bid/status")
        assert status == 200
        s = body["status"]
        assert s["production_security_claim"] is False
        assert s["asset_settlement_available"] is False
        assert s["sealed_bid_enabled"] is True
        # Honest auth boundary is machine-checkable + spelled out in non_claims.
        assert s["signature_auth_available"] is False
        assert s["account_authenticated"] is False
        assert "production" not in s["claim_scope"]
        assert any("no production security claim" in c for c in s["non_claims"])
        assert any(
            "unauthenticated label" in c and "signature-bound bidders" in c
            for c in s["non_claims"]
        )
        assert "POST /api/confidential/sealed-bid/settle" in s["endpoints"]
    finally:
        _stop_test_server(httpd, t)


def test_sealed_bid_reset_refuses_to_clobber_in_progress_batch() -> None:
    """Anti-griefing: reset must not silently wipe a batch with recorded commits
    unless force=true. This is defense-in-depth, NOT identity auth."""
    httpd, t, host, port = _start_test_server()
    try:
        batch_id = "ui-sealed-bid-clobber"
        commit = _commitment(quantity=2, limit_price=101, nonce="n0")
        status, _ = _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 5, "bond_amount": 7,
        })
        assert status == 200
        status, _ = _post(host, port, "/api/confidential/sealed-bid/commit", {
            "batch_id": batch_id, "bidder_id": "alice", "commitment": commit, "bond_amount": 7,
        })
        assert status == 200

        # Reset WITHOUT force is refused and leaves the recorded commit intact.
        status, body = _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 9, "bond_amount": 7,
        })
        assert status == 409
        assert body["error"] == "batch_in_progress"
        assert body["commit_count"] == 1
        # The original batch is unchanged (reject-is-no-op): same commit survives.
        status, body = _post(host, port, "/api/confidential/sealed-bid/open-reveal", {"batch_id": batch_id})
        assert status == 200 and body["batch"]["commit_count"] == 1

        # Explicit force=true re-initializes the batch (commits cleared).
        status, body = _post(host, port, "/api/confidential/sealed-bid/reset", {
            "batch_id": batch_id, "units_for_sale": 9, "bond_amount": 7, "force": True,
        })
        assert status == 200 and body["batch"]["phase"] == "commit"
        assert body["batch"]["units_for_sale"] == 9
    finally:
        _stop_test_server(httpd, t)


def test_sealed_bid_signature_auth_is_a_known_documented_gap() -> None:
    """The exact missing production piece, marked (not hidden) per repo policy.

    This surface authenticates NOTHING: bidder_id is a free-form label and there
    is no wallet-signature or canonical-account binding. The commit->reveal check
    is cryptographic (preimage), not identity. Production sealed-bid requires
    signature-bound bidders; until that exists this surface stays local-testnet,
    non-fund, and its status advertises signature_auth_available=False.
    """
    pytest.skip(
        "MISSING for production: signature-bound bidders. sealed-bid commit/reveal "
        "is unauthenticated (bidder_id is a label, not a verified account/pubkey). "
        "Status advertises signature_auth_available=False and account_authenticated="
        "False; production_security_claim stays False. Wire wallet-signature "
        "verification on commit (and bind reveal to the committing signature) before "
        "any production claim."
    )
