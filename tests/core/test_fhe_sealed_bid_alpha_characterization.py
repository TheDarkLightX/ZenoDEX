"""Characterization corpus for ``verify_fhe_sealed_bid_alpha_plan``.

This is a *characterization-corpus-first* lock for the fail-closed confidential
sealed-bid alpha-plan verifier. The verifier is consensus-adjacent: its reject
codes and the *first-failure ordering* are part of the contract.

Strategy
--------
1. Build one valid sealed-bid alpha plan that verifies ``(True, "ok")``.
2. Apply a corpus of single (and a few double) mutations. Each mutation targets
   exactly one reject code or relative-precedence guarantee.
3. Record ``(ok, error)`` for every corpus entry against the *current* verifier
   into a committed JSON fixture (``tests/core/fixtures/...``). This locks every
   reject code AND the first-failure ordering before any refactor.
4. A reproduction test asserts the (refactored) verifier reproduces the fixture
   EXACTLY, and that the corpus covers the full reject-code surface.

Critical correctness note (the trap)
-------------------------------------
``verify_fhe_sealed_bid_alpha_plan`` recomputes the body receipt hash and rejects
with ``hash_mismatch`` *before* checking scheme / oracle / budget / public_result.
So a body mutation that targets any code below the hash check (line ~263) MUST
recompute the receipt hash, or it collapses to ``hash_mismatch`` and exercises
none of the downstream checks. Each corpus entry therefore declares whether the
hash should be recomputed after the body mutation.

Regenerate the fixture (only when intentionally changing locked behavior):
    python3 tests/core/test_fhe_sealed_bid_alpha_characterization.py --regen
"""

from __future__ import annotations

import copy
import json
import sys
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

# Allow ``python3 tests/core/...py --regen`` to import the package.
_ROOT = Path(__file__).resolve().parents[2]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from src.core.fhe_sealed_bid_alpha import (  # noqa: E402
    FHECipherBid,
    compile_fhe_sealed_bid_alpha_plan,
    fhe_sealed_bid_alpha_receipt_hash,
    verify_fhe_sealed_bid_alpha_plan,
)
from src.core.sealed_bid_auction import (  # noqa: E402
    RevealedSealedBid,
    sealed_bid_reveal_hash,
)

FIXTURE_PATH = Path(__file__).resolve().parent / "fixtures" / "fhe_sealed_bid_alpha_characterization.json"

# Full reject-code surface of the verifier (kept in sync with the source).
# The corpus must cover all of these plus the accept code "ok".
ALL_REJECT_CODES: Tuple[str, ...] = (
    "bad_receipt_type",
    "missing_body",
    "bad_schema",
    "missing_receipt_hash",
    "hash_mismatch",
    "bad_scheme",
    "bad_oracle_mode",
    "bad_fallback_policy",
    "bad_result_verification_mode",
    "bad_auction_id",
    "bad_key_id",
    "key_not_approved",
    "bad_cipher_bids",
    "cipher_bid_count_out_of_range",
    "bad_budget",
    "bad_budget_numeric",
    "budget_bid_count_mismatch",
    "compare_ops_mismatch",
    "select_ops_mismatch",
    "add_ops_mismatch",
    "sort_layers_mismatch",
    "estimated_hcu_mismatch",
    "estimated_depth_mismatch",
    "hcu_cap_exceeded",
    "depth_cap_exceeded",
    "bad_public_result",
    "bad_public_result_numeric",
    "units_for_sale_out_of_range",
    "clearing_price_out_of_range",
    "total_filled_out_of_range",
    "fill_count_out_of_range",
    "bad_fills",
    "fill_count_mismatch",
    "decrypt_output_mismatch",
    "bad_fill",
    "bad_fill_bidder_id",
    "bad_fill_commitment",
    "duplicate_fill_key",
    "fill_without_cipher_bid",
    "bad_fill_numeric",
    "filled_quantity_out_of_range",
    "paid_price_mismatch",
    "filled_sum_mismatch",
    "unauthenticated_public_result",
    "bad_trusted_plain_bids",
    "trusted_plain_bid_count_mismatch",
    "trusted_plain_surface_mismatch",
    "trusted_plain_quantity_out_of_range",
    "trusted_plain_price_out_of_range",
    "public_result_mismatch",
    # Exception messages surfaced via ``return False, str(exc)`` from
    # _validate_cipher_bids / estimate_fhe_uniform_price_ops.
    "duplicate_cipher_handle",
    "duplicate_commit_key",
    "bidder_id must be non-empty",
    "commitment must be non-empty",
    "quantity_handle must be non-empty",
    "price_handle must be non-empty",
    "bid_count out of range",
    "decrypt_outputs out of range",
)

# A small subset of reject codes are *defense-in-depth* guards that are
# unreachable within the valid bid envelope, because an earlier check forces the
# value to its bid-count-derived expectation (or an earlier guard shadows them):
#
#   - hcu_cap_exceeded / depth_cap_exceeded: `estimated_hcu`/`estimated_depth_hcu`
#     must first equal `expected.*` (lines ~331/333). Over bid_count in 1..8 the
#     max estimate is 8,731,000 hcu / 2,368,000 depth, both below the 20M/5M caps.
#     The cap guards only fire if the estimator constants change. (Reported, not
#     fixed: locking current behavior.)
#   - "bid_count out of range" (raised by the estimator): shadowed by
#     `cipher_bid_count_out_of_range` (>8) and `budget_bid_count_mismatch` (<1
#     requires 0 cipher bids -> `cipher_bid_count_out_of_range`). No receipt can
#     pass the prior guards while presenting an out-of-range bid_count to the
#     estimator.
#
# These are intentionally NOT forced into the corpus (doing so would fabricate
# reachability). They are excluded from the strict reachable-coverage assertion
# and tracked here so a future change that makes them reachable is noticed.
DEFENSE_IN_DEPTH_UNREACHABLE: Tuple[str, ...] = (
    "hcu_cap_exceeded",
    "depth_cap_exceeded",
    "bid_count out of range",
)


# --------------------------------------------------------------------------- #
# Base valid plan + per-call argument axes.
# --------------------------------------------------------------------------- #

def _base_commitments() -> Tuple[str, str, str]:
    c1 = sealed_bid_reveal_hash(quantity=5, limit_price=100, nonce="n1")
    c2 = sealed_bid_reveal_hash(quantity=4, limit_price=80, nonce="n2")
    c3 = sealed_bid_reveal_hash(quantity=3, limit_price=120, nonce="n3")
    return c1, c2, c3


def _base_plain_bids() -> List[RevealedSealedBid]:
    c1, c2, c3 = _base_commitments()
    return [
        RevealedSealedBid(bidder_id="alice", commitment=c1, quantity=5, limit_price=100),
        RevealedSealedBid(bidder_id="bob", commitment=c2, quantity=4, limit_price=80),
        RevealedSealedBid(bidder_id="carol", commitment=c3, quantity=3, limit_price=120),
    ]


def _base_cipher_bids() -> List[FHECipherBid]:
    c1, c2, c3 = _base_commitments()
    return [
        FHECipherBid(bidder_id="alice", commitment=c1, quantity_handle="qh1", price_handle="ph1"),
        FHECipherBid(bidder_id="bob", commitment=c2, quantity_handle="qh2", price_handle="ph2"),
        FHECipherBid(bidder_id="carol", commitment=c3, quantity_handle="qh3", price_handle="ph3"),
    ]


def _base_plan() -> Dict[str, Any]:
    """A valid plan whose 3-bid partial fill exercises arithmetic + public_result."""
    return compile_fhe_sealed_bid_alpha_plan(
        auction_id="auc-1",
        units_for_sale=10,
        bids=_base_plain_bids(),
        cipher_bids=_base_cipher_bids(),
        key_id="key-A",
    )


DEFAULT_APPROVED_KEYS: Tuple[str, ...] = ("key-A",)


# --------------------------------------------------------------------------- #
# Corpus definition.
#
# A corpus entry mutates the verifier call. To keep ``--regen`` and the
# reproduction test sharing one definition, every entry is a callable that
# returns the full set of call arguments ``(receipt, approved_key_ids,
# trusted_plain_bids)``.
#
# Body mutations that target a code below the hash gate MUST recompute the
# receipt hash; ``mutate_body`` does that automatically. Mutations targeting the
# hash gate itself (``hash_mismatch`` / ``missing_receipt_hash``) and structural
# mutations operate on the raw receipt without recompute.
# --------------------------------------------------------------------------- #

CallArgs = Tuple[Any, Tuple[str, ...], Any]
CaseFn = Callable[[], CallArgs]


def _valid_args() -> CallArgs:
    return _base_plan(), DEFAULT_APPROVED_KEYS, tuple(_base_plain_bids())


def mutate_body(fn: Callable[[Dict[str, Any]], None]) -> CaseFn:
    """Mutate ``receipt['body']`` then recompute the receipt hash.

    Use for any reject code that lives below the hash gate (line ~263).
    """

    def make() -> CallArgs:
        receipt = _base_plan()
        fn(receipt["body"])
        receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])
        return receipt, DEFAULT_APPROVED_KEYS, tuple(_base_plain_bids())

    return make


def mutate_receipt(fn: Callable[[Any], Any]) -> CaseFn:
    """Replace the raw receipt object with the callable's return (no hash recompute).

    The callable receives the freshly built receipt and MUST return the receipt
    object to verify (so in-place edits should ``return receipt``). This avoids
    the footgun where a mutating expression returns its own value (e.g. the
    popped element) and silently replaces the receipt.
    """

    def make() -> CallArgs:
        receipt = _base_plan()
        out = fn(receipt)
        return out, DEFAULT_APPROVED_KEYS, tuple(_base_plain_bids())

    return make


def mutate_args(
    *,
    approved: Tuple[str, ...] | None = None,
    trusted: Any = "__keep__",
    body: Callable[[Dict[str, Any]], None] | None = None,
) -> CaseFn:
    """Mutate the non-body call axes (and optionally the body, with recompute)."""

    def make() -> CallArgs:
        receipt = _base_plan()
        if body is not None:
            body(receipt["body"])
            receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])
        keys = DEFAULT_APPROVED_KEYS if approved is None else approved
        tb: Any = tuple(_base_plain_bids()) if trusted == "__keep__" else trusted
        return receipt, keys, tb

    return make


def _del(d: Dict[str, Any], key: str) -> None:
    d.pop(key, None)


# Each entry: (name, CaseFn). Ordered roughly by the verifier's own precedence
# so the fixture reads as the trust-domain pipeline.
CORPUS: List[Tuple[str, CaseFn]] = [
    # ---- accept ----
    ("ok_valid", _valid_args),

    # ---- structural envelope ----
    ("bad_receipt_type__not_dict", mutate_receipt(lambda r: ["not", "a", "dict"])),
    ("missing_body__no_body", mutate_receipt(lambda r: {k: v for k, v in r.items() if k != "body"})),
    ("missing_body__body_not_dict", mutate_receipt(lambda r: {**r, "body": "nope"})),

    # ---- schema (checked BEFORE the hash gate) ----
    ("bad_schema__wrong", mutate_receipt(lambda r: (r["body"].__setitem__("schema", "wrong/v9"), r)[1])),

    # ---- replay / integrity (hash) ----
    ("missing_receipt_hash__deleted", mutate_receipt(lambda r: (r.pop("receipt_hash"), r)[1])),
    ("missing_receipt_hash__empty", mutate_receipt(lambda r: (r.__setitem__("receipt_hash", ""), r)[1])),
    ("missing_receipt_hash__not_str", mutate_receipt(lambda r: (r.__setitem__("receipt_hash", 1234), r)[1])),
    # body changed but hash NOT recomputed -> hash_mismatch.
    ("hash_mismatch__body_tampered", mutate_receipt(lambda r: (r["body"].__setitem__("auction_id", "tampered"), r)[1])),
    ("hash_mismatch__hash_corrupted", mutate_receipt(lambda r: (r.__setitem__("receipt_hash", "0x" + "f" * 64), r)[1])),

    # ---- confidentiality-claim / host config (below hash gate) ----
    ("bad_scheme__wrong", mutate_body(lambda b: b.__setitem__("scheme", "evil-scheme"))),
    ("bad_oracle_mode__wrong", mutate_body(lambda b: b.__setitem__("oracle_mode", "sync_decrypt"))),
    ("bad_fallback_policy__wrong", mutate_body(lambda b: b.__setitem__("fallback_policy", "none"))),
    ("bad_result_verification_mode__wrong", mutate_body(lambda b: b.__setitem__("result_verification_mode", "zk_v1"))),
    ("bad_auction_id__empty", mutate_body(lambda b: b.__setitem__("auction_id", ""))),
    ("bad_auction_id__not_str", mutate_body(lambda b: b.__setitem__("auction_id", 7))),
    ("bad_key_id__empty", mutate_body(lambda b: b.__setitem__("key_id", ""))),
    ("bad_key_id__not_str", mutate_body(lambda b: b.__setitem__("key_id", 9))),
    ("key_not_approved__unknown_key", mutate_args(approved=("key-OTHER",))),
    ("key_not_approved__empty_set", mutate_args(approved=())),

    # ---- cipher surface (privacy / committee) ----
    ("bad_cipher_bids__not_list", mutate_body(lambda b: b.__setitem__("cipher_bids", {"x": 1}))),
    (
        "cipher_validate__empty_bidder_id",
        mutate_body(lambda b: b["cipher_bids"][0].__setitem__("bidder_id", "")),
    ),
    (
        "cipher_validate__empty_commitment",
        mutate_body(lambda b: b["cipher_bids"][0].__setitem__("commitment", "")),
    ),
    (
        "cipher_validate__empty_quantity_handle",
        mutate_body(lambda b: b["cipher_bids"][0].__setitem__("quantity_handle", "")),
    ),
    (
        "cipher_validate__empty_price_handle",
        mutate_body(lambda b: b["cipher_bids"][0].__setitem__("price_handle", "")),
    ),
    (
        "cipher_validate__duplicate_handle",
        mutate_body(lambda b: b["cipher_bids"][1].__setitem__("quantity_handle", "qh1")),
    ),
    (
        "cipher_validate__duplicate_commit_key",
        # Make bid[1] identical (bidder_id,commitment) to bid[0] but unique handles.
        mutate_body(
            lambda b: (
                b["cipher_bids"][1].__setitem__("bidder_id", b["cipher_bids"][0]["bidder_id"]),
                b["cipher_bids"][1].__setitem__("commitment", b["cipher_bids"][0]["commitment"]),
            )
        ),
    ),

    # ---- budget arithmetic (math) ----
    ("bad_budget__not_dict", mutate_body(lambda b: b.__setitem__("budget", [1, 2, 3]))),
    ("bad_budget_numeric__non_numeric", mutate_body(lambda b: b["budget"].__setitem__("bid_count", "x"))),
    ("budget_bid_count_mismatch__too_low", mutate_body(lambda b: b["budget"].__setitem__("bid_count", 2))),
    ("compare_ops_mismatch__off_by_one", mutate_body(lambda b: b["budget"].__setitem__("compare_ops", b["budget"]["compare_ops"] + 1))),
    ("select_ops_mismatch__off_by_one", mutate_body(lambda b: b["budget"].__setitem__("select_ops", b["budget"]["select_ops"] + 1))),
    ("add_ops_mismatch__off_by_one", mutate_body(lambda b: b["budget"].__setitem__("add_ops", b["budget"]["add_ops"] + 1))),
    ("sort_layers_mismatch__off_by_one", mutate_body(lambda b: b["budget"].__setitem__("sort_layers", b["budget"]["sort_layers"] + 1))),
    ("estimated_hcu_mismatch__off_by_one", mutate_body(lambda b: b["budget"].__setitem__("estimated_hcu", b["budget"]["estimated_hcu"] + 1))),
    ("estimated_depth_mismatch__off_by_one", mutate_body(lambda b: b["budget"].__setitem__("estimated_depth_hcu", b["budget"]["estimated_depth_hcu"] + 1))),
    # decrypt_outputs out of the estimator's allowed range -> str(exc) from estimator.
    ("estimator_decrypt_outputs_out_of_range", mutate_body(lambda b: b["budget"].__setitem__("decrypt_outputs", 999))),

    # ---- public_result arithmetic (math) ----
    ("bad_public_result__not_dict", mutate_body(lambda b: b.__setitem__("public_result", 5))),
    ("bad_public_result_numeric__non_numeric", mutate_body(lambda b: b["public_result"].__setitem__("clearing_price", "x"))),
    ("units_for_sale_out_of_range__zero", mutate_body(lambda b: b["public_result"].__setitem__("units_for_sale", 0))),
    ("clearing_price_out_of_range__negative", mutate_body(lambda b: b["public_result"].__setitem__("clearing_price", -1))),
    ("total_filled_out_of_range__over_units", mutate_body(lambda b: b["public_result"].__setitem__("total_filled", b["public_result"]["units_for_sale"] + 1))),
    ("fill_count_out_of_range__over_bid_count", mutate_body(lambda b: b["public_result"].__setitem__("fill_count", b["budget"]["bid_count"] + 1))),
    ("bad_fills__not_list", mutate_body(lambda b: b["public_result"].__setitem__("fills", {"x": 1}))),
    # Drop one fill so len(fills) != fill_count (fill_count still in range vs bid_count).
    ("fill_count_mismatch__short_fills", mutate_body(lambda b: b["public_result"].__setitem__("fills", b["public_result"]["fills"][:-1]))),

    # ---- fills loop (math, internal precedence) ----
    ("bad_fill__not_dict", mutate_body(lambda b: b["public_result"]["fills"].__setitem__(0, ["nope"]))),
    ("bad_fill_bidder_id__empty", mutate_body(lambda b: b["public_result"]["fills"][0].__setitem__("bidder_id", ""))),
    ("bad_fill_commitment__empty", mutate_body(lambda b: b["public_result"]["fills"][0].__setitem__("commitment", ""))),
    (
        "duplicate_fill_key__second_equals_first",
        mutate_body(
            lambda b: (
                b["public_result"]["fills"][1].__setitem__("bidder_id", b["public_result"]["fills"][0]["bidder_id"]),
                b["public_result"]["fills"][1].__setitem__("commitment", b["public_result"]["fills"][0]["commitment"]),
            )
        ),
    ),
    (
        "fill_without_cipher_bid__unknown_key",
        mutate_body(
            lambda b: (
                b["public_result"]["fills"][0].__setitem__("bidder_id", "ghost"),
                b["public_result"]["fills"][0].__setitem__("commitment", "0x" + "a" * 64),
            )
        ),
    ),
    ("bad_fill_numeric__non_numeric_qty", mutate_body(lambda b: b["public_result"]["fills"][0].__setitem__("filled_quantity", "x"))),
    ("filled_quantity_out_of_range__zero", mutate_body(lambda b: b["public_result"]["fills"][0].__setitem__("filled_quantity", 0))),
    ("paid_price_mismatch__not_clearing", mutate_body(lambda b: b["public_result"]["fills"][0].__setitem__("paid_price", b["public_result"]["clearing_price"] + 1))),

    # ---- trusted replay (host/committee authentication) ----
    ("unauthenticated_public_result__none", mutate_args(trusted=None)),
    ("trusted_plain_bid_count_mismatch__short", mutate_args(trusted=tuple(_base_plain_bids()[:-1]))),
    (
        "trusted_plain_surface_mismatch__rename",
        mutate_args(
            trusted=tuple(
                [
                    RevealedSealedBid(bidder_id="ghost", commitment="0x" + "b" * 64, quantity=5, limit_price=100),
                ]
                + _base_plain_bids()[1:]
            )
        ),
    ),
]


# Cases whose trusted_plain_bids carry the right surface keys (so we reach the
# per-bid validation and replay), built relative to the base surface.
def _trusted_with(idx_mutator: Callable[[List[RevealedSealedBid]], List[RevealedSealedBid]]) -> CaseFn:
    def make() -> CallArgs:
        receipt = _base_plan()
        bids = idx_mutator(_base_plain_bids())
        return receipt, DEFAULT_APPROVED_KEYS, tuple(bids)

    return make


def _replace_bid(bids: List[RevealedSealedBid], idx: int, **kw: Any) -> List[RevealedSealedBid]:
    import dataclasses

    bids[idx] = dataclasses.replace(bids[idx], **kw)
    return bids


def _case_cipher_count_over_max() -> CallArgs:
    # Append cipher bids past MAX_ALPHA_BIDS (8). _validate_cipher_bids passes
    # (unique handles/keys) so the explicit count guard fires.
    receipt = _base_plan()
    body = receipt["body"]
    for i in range(6):  # 3 base + 6 = 9 > 8
        body["cipher_bids"].append(
            {
                "bidder_id": f"extra{i}",
                "commitment": "0x" + str(i % 10) * 64,
                "quantity_handle": f"extra_qh{i}",
                "price_handle": f"extra_ph{i}",
            }
        )
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(body)
    return receipt, DEFAULT_APPROVED_KEYS, tuple(_base_plain_bids())


def _case_decrypt_output_mismatch() -> CallArgs:
    # decrypt_outputs kept inside the estimator's allowed range (4) but != len(fills)+2 (5).
    # Op counts are independent of decrypt_outputs, so the budget block still matches.
    receipt = _base_plan()
    receipt["body"]["budget"]["decrypt_outputs"] = 4
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])
    return receipt, DEFAULT_APPROVED_KEYS, tuple(_base_plain_bids())


def _case_filled_sum_mismatch() -> CallArgs:
    # total_filled in range (<= units) but != sum(filled_quantity) of the fills.
    receipt = _base_plan()
    pr = receipt["body"]["public_result"]
    pr["total_filled"] = pr["units_for_sale"] - 1  # 9, real sum is 10
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])
    return receipt, DEFAULT_APPROVED_KEYS, tuple(_base_plain_bids())


CORPUS.extend(
    [
        ("cipher_bid_count_out_of_range__nine_bids", _case_cipher_count_over_max),
        ("decrypt_output_mismatch__in_range_off", _case_decrypt_output_mismatch),
        ("filled_sum_mismatch__total_below_sum", _case_filled_sum_mismatch),
        (
            "trusted_plain_quantity_out_of_range__zero",
            _trusted_with(lambda bs: _replace_bid(bs, 0, quantity=0)),
        ),
        (
            "trusted_plain_price_out_of_range__zero",
            _trusted_with(lambda bs: _replace_bid(bs, 0, limit_price=0)),
        ),
        # bad_trusted_plain_bids: a surface-matching bid whose quantity is a bool
        # (passes surface keys, but settle raises in re-derivation path)... actually
        # the explicit per-bid guard rejects bool first -> trusted_plain_quantity_out_of_range.
        # To hit "bad_trusted_plain_bids" we make trusted not iterable.
        (
            "bad_trusted_plain_bids__not_iterable",
            mutate_args(trusted=12345),
        ),
        # public_result_mismatch: valid receipt, surface-matching trusted bids, but
        # different quantities so the re-derived settlement differs from the receipt.
        (
            "public_result_mismatch__altered_quantities",
            _trusted_with(lambda bs: _replace_bid(_replace_bid(bs, 0, quantity=1), 1, quantity=1)),
        ),
    ]
)


# --------------------------------------------------------------------------- #
# Double-break precedence cases (lock relative ordering, not just existence).
# --------------------------------------------------------------------------- #

def _double_schema_and_oracle() -> CallArgs:
    # schema is checked BEFORE the hash gate; oracle is below it. Break both,
    # do NOT recompute hash. Current verifier must yield bad_schema (schema
    # precedes hash precedes oracle).
    receipt = _base_plan()
    receipt["body"]["schema"] = "wrong/v9"
    receipt["body"]["oracle_mode"] = "sync_decrypt"
    return receipt, DEFAULT_APPROVED_KEYS, tuple(_base_plain_bids())


def _double_oracle_and_key() -> CallArgs:
    # Both below hash gate; recompute hash. oracle_mode is checked before key_id.
    receipt = _base_plan()
    receipt["body"]["oracle_mode"] = "sync_decrypt"
    receipt["body"]["key_id"] = "key-OTHER"
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])
    return receipt, DEFAULT_APPROVED_KEYS, tuple(_base_plain_bids())


def _double_budget_and_public_result() -> CallArgs:
    # budget block is checked before public_result. Break both; recompute hash.
    receipt = _base_plan()
    receipt["body"]["budget"]["compare_ops"] += 1
    receipt["body"]["public_result"]["units_for_sale"] = 0
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])
    return receipt, DEFAULT_APPROVED_KEYS, tuple(_base_plain_bids())


def _double_fillloop_dupkey_and_badnumeric() -> CallArgs:
    # Inside the fills loop: duplicate_fill_key (on the SECOND fill) is detected
    # before that fill's numeric parse. Make fill[1] duplicate fill[0]'s key AND
    # give fill[1] a non-numeric qty. Must yield duplicate_fill_key.
    receipt = _base_plan()
    fills = receipt["body"]["public_result"]["fills"]
    fills[1]["bidder_id"] = fills[0]["bidder_id"]
    fills[1]["commitment"] = fills[0]["commitment"]
    fills[1]["filled_quantity"] = "not-a-number"
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])
    return receipt, DEFAULT_APPROVED_KEYS, tuple(_base_plain_bids())


def _double_trusted_overrides_publicresult() -> CallArgs:
    # unauthenticated_public_result (trusted=None) is checked AFTER the full
    # public_result arithmetic block. Break a public_result field AND pass
    # trusted=None: arithmetic failure (clearing_price_out_of_range) must win.
    receipt = _base_plan()
    receipt["body"]["public_result"]["clearing_price"] = -1
    receipt["receipt_hash"] = fhe_sealed_bid_alpha_receipt_hash(receipt["body"])
    return receipt, DEFAULT_APPROVED_KEYS, None


PRECEDENCE_CORPUS: List[Tuple[str, CaseFn]] = [
    ("precedence__schema_before_hash_before_oracle", _double_schema_and_oracle),
    ("precedence__oracle_before_key", _double_oracle_and_key),
    ("precedence__budget_before_public_result", _double_budget_and_public_result),
    ("precedence__fillloop_dupkey_before_numeric", _double_fillloop_dupkey_and_badnumeric),
    ("precedence__publicresult_before_trusted", _double_trusted_overrides_publicresult),
]


def _all_cases() -> List[Tuple[str, CaseFn]]:
    return CORPUS + PRECEDENCE_CORPUS


# --------------------------------------------------------------------------- #
# Fixture I/O + evaluation.
# --------------------------------------------------------------------------- #

def _evaluate(case: CaseFn) -> Dict[str, Any]:
    """Run the (current) verifier against one case, catching raised exceptions."""
    receipt, approved, trusted = case()
    try:
        ok, error = verify_fhe_sealed_bid_alpha_plan(
            receipt, approved_key_ids=approved, trusted_plain_bids=trusted
        )
        return {"ok": bool(ok), "error": str(error), "raised": None}
    except Exception as exc:  # pragma: no cover - characterization safety net
        return {"ok": None, "error": None, "raised": f"{type(exc).__name__}: {exc}"}


def build_corpus_records() -> List[Dict[str, Any]]:
    records: List[Dict[str, Any]] = []
    for name, case in _all_cases():
        result = _evaluate(case)
        records.append({"name": name, **result})
    return records


def load_fixture() -> Dict[str, Any]:
    with FIXTURE_PATH.open("r", encoding="utf-8") as fh:
        return json.load(fh)


def regenerate() -> Dict[str, Any]:
    records = build_corpus_records()
    payload = {
        "schema": "zenodex/fhe_sealed_bid_alpha_characterization/v1",
        "target": "src.core.fhe_sealed_bid_alpha.verify_fhe_sealed_bid_alpha_plan",
        "description": (
            "Locked (ok, error) outcomes and first-failure ordering for the "
            "fail-closed FHE sealed-bid alpha-plan verifier."
        ),
        "case_count": len(records),
        "records": records,
    }
    FIXTURE_PATH.parent.mkdir(parents=True, exist_ok=True)
    with FIXTURE_PATH.open("w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, sort_keys=False)
        fh.write("\n")
    return payload


# --------------------------------------------------------------------------- #
# Tests.
# --------------------------------------------------------------------------- #

def test_base_plan_verifies_ok() -> None:
    receipt, approved, trusted = _valid_args()
    ok, error = verify_fhe_sealed_bid_alpha_plan(
        receipt, approved_key_ids=approved, trusted_plain_bids=trusted
    )
    assert (ok, error) == (True, "ok")


def test_corpus_reproduces_fixture_exactly() -> None:
    """The (possibly refactored) verifier must reproduce the locked corpus EXACTLY."""
    assert FIXTURE_PATH.exists(), (
        f"Missing fixture {FIXTURE_PATH}. Generate it with: "
        f"python3 {Path(__file__).name} --regen"
    )
    fixture = load_fixture()
    expected = {rec["name"]: rec for rec in fixture["records"]}
    actual_records = build_corpus_records()
    actual = {rec["name"]: rec for rec in actual_records}

    assert set(actual) == set(expected), (
        "Corpus case set drifted from fixture. "
        f"only-in-code={sorted(set(actual) - set(expected))} "
        f"only-in-fixture={sorted(set(expected) - set(actual))}"
    )
    mismatches: List[str] = []
    for name in expected:
        if actual[name] != expected[name]:
            mismatches.append(f"{name}: expected={expected[name]} actual={actual[name]}")
    assert not mismatches, "Verifier behavior drifted from locked corpus:\n" + "\n".join(mismatches)


def test_corpus_covers_full_reject_surface() -> None:
    """Every reject code in the verifier (plus 'ok') must appear in the corpus.

    This makes coverage a checked invariant: a dropped/unreachable check group
    surfaces immediately as a missing code.
    """
    produced = set()
    for rec in build_corpus_records():
        if rec["error"] is not None:
            produced.add(rec["error"])
    # Strict coverage over the REACHABLE surface (all codes minus the documented
    # defense-in-depth-unreachable ones), plus the accept code.
    reachable_expected = (set(ALL_REJECT_CODES) - set(DEFENSE_IN_DEPTH_UNREACHABLE)) | {"ok"}
    missing = reachable_expected - produced
    assert not missing, f"Corpus does not exercise reachable reject codes: {sorted(missing)}"


def test_defense_in_depth_codes_remain_unreachable_under_current_constants() -> None:
    """Lock the *unreachability* of the cap/estimator-range defense-in-depth guards.

    If a future change makes any of these reachable within the valid envelope,
    this test fails and forces a deliberate decision (add a corpus case + lock,
    or restore the shadowing guard). Tightly bounds the max estimate so the cap
    guards' unreachability is asserted, not assumed.
    """
    from src.core.fhe_sealed_bid_alpha import (
        MAX_ALPHA_BIDS,
        ZAMA_DEVNET_HCU_DEPTH_CAP,
        ZAMA_DEVNET_HCU_TX_CAP,
        estimate_fhe_uniform_price_ops,
    )

    max_hcu = 0
    max_depth = 0
    for bc in range(1, MAX_ALPHA_BIDS + 1):
        est = estimate_fhe_uniform_price_ops(bid_count=bc, decrypt_outputs=bc + 2)
        max_hcu = max(max_hcu, est.estimated_hcu)
        max_depth = max(max_depth, est.estimated_depth_hcu)
    # Because the verifier forces estimated_* == expected.* before the cap check,
    # and expected.* never exceeds the cap over the valid bid envelope, the cap
    # reject codes are unreachable.
    assert max_hcu <= ZAMA_DEVNET_HCU_TX_CAP, (
        f"hcu_cap_exceeded became reachable: max estimate {max_hcu} > cap {ZAMA_DEVNET_HCU_TX_CAP}"
    )
    assert max_depth <= ZAMA_DEVNET_HCU_DEPTH_CAP, (
        f"depth_cap_exceeded became reachable: max estimate {max_depth} > cap {ZAMA_DEVNET_HCU_DEPTH_CAP}"
    )


def test_fixture_in_sync_with_corpus_definition() -> None:
    """Fail loudly if the committed fixture is stale vs the corpus definition."""
    fixture = load_fixture()
    assert fixture["case_count"] == len(fixture["records"]) == len(_all_cases())


def test_precedence_double_breaks_pick_earlier_check() -> None:
    """Explicit precedence locks at trust-domain boundaries.

    Single mutations prove a check exists; these double-breaks prove the
    *relative* ordering between two checks.
    """
    results = {name: _evaluate(case) for name, case in PRECEDENCE_CORPUS}
    # schema (pre-hash) must beat both the hash gate and oracle.
    assert results["precedence__schema_before_hash_before_oracle"]["error"] == "bad_schema"
    # oracle_mode must beat key_id.
    assert results["precedence__oracle_before_key"]["error"] == "bad_oracle_mode"
    # budget block must beat public_result.
    assert results["precedence__budget_before_public_result"]["error"] == "compare_ops_mismatch"
    # inside fills loop: duplicate_fill_key must beat the numeric parse of that fill.
    assert results["precedence__fillloop_dupkey_before_numeric"]["error"] == "duplicate_fill_key"
    # public_result arithmetic must beat the trusted-replay authentication gate.
    assert results["precedence__publicresult_before_trusted"]["error"] == "clearing_price_out_of_range"


# --------------------------------------------------------------------------- #
# Trust-domain labeling (the refactor's crisp privacy/replay/arithmetic claims).
# --------------------------------------------------------------------------- #

def test_trust_domain_labels_cover_all_check_groups() -> None:
    """Every extracted check group is labeled with a valid trust domain.

    Makes the labeling deliverable load-bearing: each ``_check_*`` group present
    in the verifier module must map to exactly one of {host, committee, math},
    and the label registry must not reference any non-existent group.
    """
    import inspect

    import src.core.fhe_sealed_bid_alpha as mod

    # Discover the actual check-group functions defined in the module.
    check_group_funcs = {
        name
        for name, obj in inspect.getmembers(mod, inspect.isfunction)
        if name.startswith("_check_") and obj.__module__ == mod.__name__
    }
    labeled = set(mod._CHECK_GROUP_TRUST_DOMAIN)

    # Bijection: every check group is labeled, and every label points at a real group.
    assert labeled == check_group_funcs, (
        f"label/group mismatch: unlabeled={sorted(check_group_funcs - labeled)} "
        f"stale_labels={sorted(labeled - check_group_funcs)}"
    )
    # Every label is a valid trust domain.
    assert set(mod._CHECK_GROUP_TRUST_DOMAIN.values()) <= set(mod.TRUST_DOMAINS)
    for group, domain in mod._CHECK_GROUP_TRUST_DOMAIN.items():
        assert mod.check_group_trust_domain(group) == domain
    # All three trust domains are actually represented (privacy/replay/arithmetic).
    assert set(mod._CHECK_GROUP_TRUST_DOMAIN.values()) == set(mod.TRUST_DOMAINS)


def test_verify_check_group_order_matches_source_definition_order() -> None:
    """The published ordered group list matches the verifier's source call order.

    Locks that the labeled decomposition list is the real execution order (a
    drift here would mean the labels describe a different pipeline than the one
    that runs). We read the source of ``verify_fhe_sealed_bid_alpha_plan`` and
    assert each ``_check_*`` group is *first mentioned* in the same order as
    ``VERIFY_CHECK_GROUPS``.
    """
    import inspect

    import src.core.fhe_sealed_bid_alpha as mod

    src = inspect.getsource(mod.verify_fhe_sealed_bid_alpha_plan)
    declared_order = [name for name, _domain in mod.VERIFY_CHECK_GROUPS]
    first_pos = {name: src.find(name) for name in declared_order}
    assert all(pos >= 0 for pos in first_pos.values()), (
        f"a declared group is never called in verify(): "
        f"{[n for n, p in first_pos.items() if p < 0]}"
    )
    source_order = sorted(declared_order, key=lambda n: first_pos[n])
    assert source_order == declared_order, (
        f"VERIFY_CHECK_GROUPS order {declared_order} != source call order {source_order}"
    )


# --------------------------------------------------------------------------- #
# TEETH: mutation tests.
#
# Reproducing the fixture proves the corpus *reproduces* current behavior. These
# mutation tests prove the corpus *constrains* it: an injected regression in the
# verifier must make the locked corpus diverge from the fixture (i.e. turn the
# reproduction test RED). Each test monkeypatches one internal check group to
# simulate a specific class of bug, then asserts the corpus catches it on the
# expected case(s). Reverts are automatic (monkeypatch undoes the patch).
# --------------------------------------------------------------------------- #

import src.core.fhe_sealed_bid_alpha as _fhe_mod  # noqa: E402


def _fixture_by_name() -> Dict[str, Dict[str, Any]]:
    return {rec["name"]: rec for rec in load_fixture()["records"]}


def test_teeth_replay_guard_break_is_caught(monkeypatch) -> None:
    """A neutered replay/integrity guard MUST make the corpus diverge from the lock.

    Catches: ``hash_mismatch__body_tampered`` and ``hash_mismatch__hash_corrupted``
    (locked to ``hash_mismatch``) flip to ``ok`` / a downstream code once the
    receipt-hash binding no longer rejects tampered bodies.
    """
    expected = _fixture_by_name()

    # Disable the replay guard: it always passes.
    monkeypatch.setattr(_fhe_mod, "_check_replay_hash", lambda receipt, body: (True, "ok"))

    actual = {rec["name"]: rec for rec in build_corpus_records()}

    # The corpus must now DIVERGE from the fixture (reproduction test would fail).
    mismatched = [n for n in expected if actual[n] != expected[n]]
    assert mismatched, "Neutering the replay guard did NOT change any corpus outcome — no teeth."

    # Specifically, the tampered-body case must no longer reject with hash_mismatch.
    assert expected["hash_mismatch__body_tampered"]["error"] == "hash_mismatch"
    assert actual["hash_mismatch__body_tampered"]["error"] != "hash_mismatch"
    assert "hash_mismatch__body_tampered" in mismatched
    assert "hash_mismatch__hash_corrupted" in mismatched


def test_teeth_arithmetic_relation_break_is_caught(monkeypatch) -> None:
    """A flipped arithmetic relation MUST make the corpus diverge from the lock.

    Simulates the classic '!=' -> '==' inversion in the HCU budget check by
    swapping ``_check_budget_arithmetic`` for a variant that ACCEPTS a corrupted
    ``compare_ops`` and REJECTS the correct one. Catches both ``ok_valid``
    (locked ``ok`` -> now rejects) and ``compare_ops_mismatch__off_by_one``
    (locked reject -> now accepts that field).
    """
    expected = _fixture_by_name()
    orig = _fhe_mod._check_budget_arithmetic

    def inverted(body, cipher_bids):
        # Re-run the real check, then invert ONLY the compare_ops verdict to
        # emulate a `compare_ops != expected` -> `==` source bug.
        budget = body.get("budget")
        if not isinstance(budget, dict):
            return orig(body, cipher_bids)
        try:
            from src.core.fhe_sealed_bid_alpha import estimate_fhe_uniform_price_ops

            bc = int(budget.get("bid_count"))
            do = int(budget.get("decrypt_outputs"))
            co = int(budget.get("compare_ops"))
            exp = estimate_fhe_uniform_price_ops(bid_count=bc, decrypt_outputs=do)
        except Exception:
            return orig(body, cipher_bids)
        ok, error, figures = orig(body, cipher_bids)
        if error == "compare_ops_mismatch":
            # Bug accepts the mismatched compare_ops: pretend it passed and fall
            # through to the rest by re-deriving with the corrupted value patched.
            patched = dict(budget)
            patched["compare_ops"] = exp.compare_ops
            patched_body = dict(body)
            patched_body["budget"] = patched
            return orig(patched_body, cipher_bids)
        if ok and co == exp.compare_ops:
            # Bug rejects the CORRECT compare_ops.
            return False, "compare_ops_mismatch", None
        return ok, error, figures

    monkeypatch.setattr(_fhe_mod, "_check_budget_arithmetic", inverted)

    actual = {rec["name"]: rec for rec in build_corpus_records()}
    mismatched = [n for n in expected if actual[n] != expected[n]]
    assert mismatched, "Inverting the arithmetic relation did NOT change any corpus outcome — no teeth."

    # The off-by-one mutation (locked reject) is now accepted -> diverges.
    assert expected["compare_ops_mismatch__off_by_one"]["error"] == "compare_ops_mismatch"
    assert actual["compare_ops_mismatch__off_by_one"]["error"] != "compare_ops_mismatch"
    # The valid plan (locked ok) is now rejected -> diverges.
    assert expected["ok_valid"]["error"] == "ok"
    assert actual["ok_valid"]["error"] != "ok"


def test_teeth_fillloop_precedence_break_is_caught(monkeypatch) -> None:
    """Reordering the fills-loop conservation check MUST be caught.

    Simulates dropping the final ``filled_sum != total_filled`` conservation
    check (a real risk when extracting a loop). The locked
    ``filled_sum_mismatch__total_below_sum`` case (reject) flips to ``ok``.
    """
    expected = _fixture_by_name()
    orig = _fhe_mod._check_fills_accounting

    def no_conservation(ctx, decrypt_outputs):
        ok, error = orig(ctx, decrypt_outputs)
        if error == "filled_sum_mismatch":
            return True, "ok"  # bug: conservation check removed
        return ok, error

    monkeypatch.setattr(_fhe_mod, "_check_fills_accounting", no_conservation)

    actual = {rec["name"]: rec for rec in build_corpus_records()}
    assert expected["filled_sum_mismatch__total_below_sum"]["error"] == "filled_sum_mismatch"
    assert actual["filled_sum_mismatch__total_below_sum"]["error"] != "filled_sum_mismatch"


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--regen":
        payload = regenerate()
        print(f"Wrote {FIXTURE_PATH} ({payload['case_count']} cases)")
        # Coverage report on regen.
        produced = {r["error"] for r in payload["records"] if r["error"] is not None}
        missing = (set(ALL_REJECT_CODES) | {"ok"}) - produced
        if missing:
            print(f"WARNING: corpus does not cover reject codes: {sorted(missing)}", file=sys.stderr)
        else:
            print("Coverage: all reject codes + ok exercised.")
    else:
        print("Usage: python3 test_fhe_sealed_bid_alpha_characterization.py --regen", file=sys.stderr)
        sys.exit(2)
