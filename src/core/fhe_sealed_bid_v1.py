"""FHE sealed-bid auction settlement v1.

Production homomorphic sealed-bid auction settlement using the Paillier
cryptosystem for additive homomorphic computation over encrypted bids.

Security model:
- Bids (price, quantity) are encrypted under a Paillier public key before
  submission to the settlement engine.
- The settlement engine computes encrypted bid differences homomorphically,
  then queries a comparison oracle that reveals ONLY the sign bit -- never
  the actual price values.
- The clearing price is the only bid price fully decrypted, via async
  decryption of the marginal bid's encrypted price.
- Winning bid quantities are decrypted only because they are part of the
  public settlement result (filled_quantity).  Non-winning bid prices and
  quantities are never decrypted during settlement.
- Individual bid prices are never decrypted: all ranking is done via
  homomorphic subtraction + sign-bit oracle queries.

When no FHE key is provisioned, the module degrades to commit/reveal
(commit_reveal_v1) with production_security_claim=False.

Copyright (c) DarkLightX/Dana Edwards. All rights reserved.
"""

from __future__ import annotations

import math
import secrets
from dataclasses import dataclass
from typing import Any, Dict, Iterable, Tuple

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .domain_limits import is_strict_int
from .sealed_bid_auction import (
    MAX_PRICE,
    MAX_UNITS,
    RevealedSealedBid,
    SealedBidFill,
    settle_uniform_price_sealed_bids,
)

# ── Constants ───────────────────────────────────────────────────────────

MAX_V1_BIDS = 8
MAX_V1_UNITS = 63
SCHEME_FHE = "paillier-homomorphic-v1"
SCHEME_FALLBACK = "commit_reveal_v1"
_RECEIPT_DOMAIN = "zenodex.fhe_sealed_bid_v1/v1"
_MILLER_RABIN_ROUNDS = 20


def _receipt_int(value: Any) -> int | None:
    if not is_strict_int(value):
        return None
    return value

# ── Paillier key types ──────────────────────────────────────────────────


@dataclass(frozen=True)
class PaillierPublicKey:
    """Paillier public key: modulus n and generator g (= n + 1)."""
    n: int
    n_sq: int
    g: int


@dataclass(frozen=True)
class PaillierPrivateKey:
    """Paillier private key: lambda and mu for decryption."""
    public: PaillierPublicKey
    lam: int
    mu: int


@dataclass(frozen=True)
class PaillierKeyPair:
    """A Paillier key pair with an associated key_id."""
    public_key: PaillierPublicKey
    private_key: PaillierPrivateKey
    key_id: str
    key_bits: int


# ── Paillier primitives ─────────────────────────────────────────────────


def _is_probable_prime(n: int, rounds: int = _MILLER_RABIN_ROUNDS) -> bool:
    """Miller-Rabin probabilistic primality test."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    for _ in range(rounds):
        a = secrets.randbelow(n - 3) + 2
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def _generate_prime(bits: int) -> int:
    """Generate a random prime of approximately *bits* bits."""
    while True:
        candidate = secrets.randbits(bits) | (1 << (bits - 1)) | 1
        if _is_probable_prime(candidate):
            return candidate


def generate_paillier_keypair(
    *, key_bits: int = 256, key_id: str = "fhe-v1-default"
) -> PaillierKeyPair:
    """Generate a Paillier key pair with primes of *key_bits* bits each.

    The modulus n has 2 * key_bits bits.  For production, key_bits >= 1024.
    """
    if key_bits < 64:
        raise ValueError("key_bits must be >= 64")
    while True:
        p = _generate_prime(key_bits)
        q = _generate_prime(key_bits)
        if p == q:
            continue
        n = p * q
        phi = (p - 1) * (q - 1)
        if math.gcd(n, phi) != 1:
            continue
        n_sq = n * n
        lam = phi // math.gcd(p - 1, q - 1)
        mu = pow(lam, -1, n)
        public = PaillierPublicKey(n=n, n_sq=n_sq, g=n + 1)
        private = PaillierPrivateKey(public=public, lam=lam, mu=mu)
        return PaillierKeyPair(
            public_key=public,
            private_key=private,
            key_id=str(key_id),
            key_bits=int(key_bits),
        )


def _random_coprime(n: int) -> int:
    """Generate a random r in [1, n) with gcd(r, n) = 1."""
    while True:
        r = secrets.randbelow(n - 1) + 1
        if math.gcd(r, n) == 1:
            return r


def _encrypt_value(public_key: PaillierPublicKey, plaintext: int) -> int:
    """Paillier encryption: c = (1 + m*n) * r^n mod n^2 (g = n+1)."""
    n = public_key.n
    if plaintext < 0 or plaintext >= n:
        raise ValueError("plaintext out of range for Paillier encryption")
    r = _random_coprime(n)
    return ((1 + plaintext * n) * pow(r, n, public_key.n_sq)) % public_key.n_sq


def _decrypt_value(private_key: PaillierPrivateKey, ciphertext: int) -> int:
    """Paillier decryption: m = L(c^lam mod n^2) * mu mod n."""
    n_sq = private_key.public.n_sq
    n = private_key.public.n
    c_lam = pow(ciphertext, private_key.lam, n_sq)
    l_val = (c_lam - 1) // n
    return (l_val * private_key.mu) % n


def _homomorphic_add(pk: PaillierPublicKey, c1: int, c2: int) -> int:
    """E(m1 + m2) = c1 * c2 mod n^2."""
    return (c1 * c2) % pk.n_sq


def _homomorphic_sub(pk: PaillierPublicKey, c1: int, c2: int) -> int:
    """E(m1 - m2) = c1 * c2^(-1) mod n^2."""
    c2_inv = pow(c2, -1, pk.n_sq)
    return (c1 * c2_inv) % pk.n_sq


def _homomorphic_scalar_mul(pk: PaillierPublicKey, c: int, k: int) -> int:
    """E(k * m) = c^k mod n^2."""
    return pow(c, k, pk.n_sq)


def _validate_ciphertext(
    public_key: PaillierPublicKey, ciphertext: object, *, name: str
) -> int:
    if not isinstance(ciphertext, int) or isinstance(ciphertext, bool):
        raise ValueError(f"{name} must be an int ciphertext")
    candidate = int(ciphertext)
    if candidate <= 0 or candidate >= public_key.n_sq:
        raise ValueError(f"{name} out of ciphertext range")
    if math.gcd(candidate, public_key.n_sq) != 1:
        raise ValueError(f"{name} must be invertible modulo n^2")
    return candidate


# ── Comparison oracle ───────────────────────────────────────────────────


@dataclass(frozen=True)
class ComparisonResult:
    """Tristate: 1 if a > b, -1 if a < b, 0 if equal."""

    value: int


def compare_encrypted(
    private_key: PaillierPrivateKey,
    public_key: PaillierPublicKey,
    c_a: int,
    c_b: int,
) -> ComparisonResult:
    """Compare two encrypted values without revealing individual plaintexts.

    Uses additive blinding: a random value R (much larger than the max
    possible bid) is homomorphically added to E(a - b) before decryption.
    The decrypted value is (a - b + R) mod n, which does not reveal a - b
    without knowing R.  Only the sign is extracted by comparing the
    blinded result against R.  R is generated fresh per call and never
    stored or returned, so the exact bid spread cannot be reconstructed.
    """
    import secrets as _secrets

    n = public_key.n
    enc_diff = _homomorphic_sub(public_key, c_a, c_b)
    # Generate a fresh random blinding factor R >> max possible |a - b|.
    # R must be large enough that (a - b + R) is always positive and
    # less than n, so the sign is determined by comparing against R.
    # Use half the modulus bit-length as the blinding size.
    n_bits = n.bit_length()
    r_bits = max(64, n_bits // 4)
    R = _secrets.randbits(r_bits) | (1 << (r_bits - 1))
    enc_r = _encrypt_value(public_key, R)
    enc_blinded = _homomorphic_add(public_key, enc_diff, enc_r)
    blinded = _decrypt_value(private_key, enc_blinded)
    if blinded == R:
        return ComparisonResult(0)
    if blinded > R:
        return ComparisonResult(1)
    return ComparisonResult(-1)


# ── Encrypted bid types ─────────────────────────────────────────────────


@dataclass(frozen=True)
class EncryptedBid:
    """A sealed bid with price and quantity encrypted under Paillier."""

    bidder_id: str
    commitment: str
    price_ciphertext: int
    quantity_ciphertext: int


@dataclass(frozen=True)
class FHESettlementResult:
    """Result of an FHE (or fallback) sealed-bid settlement."""

    clearing_price: int
    total_filled: int
    fills: tuple[SealedBidFill, ...]
    production_security_claim: bool
    scheme: str
    key_id: str
    comparison_count: int
    decrypt_count: int
    range_proof_verified: bool = False


def encrypt_bid(
    *,
    public_key: PaillierPublicKey,
    bidder_id: str,
    commitment: str,
    quantity: int,
    limit_price: int,
) -> EncryptedBid:
    """Encrypt a bid's quantity and limit price under the Paillier public key."""
    if not isinstance(bidder_id, str) or not bidder_id:
        raise ValueError("bidder_id must be non-empty")
    if not isinstance(commitment, str) or not commitment:
        raise ValueError("commitment must be non-empty")
    if not isinstance(quantity, int) or isinstance(quantity, bool) or quantity <= 0 or quantity > MAX_UNITS:
        raise ValueError("quantity out of range")
    if not isinstance(limit_price, int) or isinstance(limit_price, bool) or limit_price <= 0 or limit_price > MAX_PRICE:
        raise ValueError("limit_price out of range")
    return EncryptedBid(
        bidder_id=str(bidder_id),
        commitment=str(commitment),
        price_ciphertext=_encrypt_value(public_key, int(limit_price)),
        quantity_ciphertext=_encrypt_value(public_key, int(quantity)),
    )


# ── Homomorphic settlement ──────────────────────────────────────────────


def settle_fhe_sealed_bids(
    *,
    auction_id: str,
    units_for_sale: int,
    encrypted_bids: Iterable[EncryptedBid],
    key_pair: PaillierKeyPair,
    range_proof_verified: bool = False,
) -> FHESettlementResult:
    """Settle a sealed-bid auction using homomorphic computation.

    Bids remain encrypted throughout.  Only sign-bits and the clearing
    price are decrypted.  Winning quantities are part of the public result.
    """
    if not isinstance(auction_id, str) or not auction_id:
        raise ValueError("auction_id must be non-empty")
    if not isinstance(units_for_sale, int) or isinstance(units_for_sale, bool) or units_for_sale <= 0 or units_for_sale > MAX_V1_UNITS:
        raise ValueError("units_for_sale out of range")
    if not isinstance(range_proof_verified, bool):
        raise ValueError("range_proof_verified must be a bool")

    bids = tuple(encrypted_bids)
    if len(bids) == 0 or len(bids) > MAX_V1_BIDS:
        raise ValueError("bid count out of range")

    pk = key_pair.public_key
    sk = key_pair.private_key
    seen: set[tuple[str, str]] = set()
    for b in bids:
        if not isinstance(b, EncryptedBid):
            raise ValueError("encrypted_bids must contain EncryptedBid values")
        if not isinstance(b.bidder_id, str) or not b.bidder_id:
            raise ValueError("bidder_id must be non-empty")
        if not isinstance(b.commitment, str) or not b.commitment:
            raise ValueError("commitment must be non-empty")
        _validate_ciphertext(pk, b.price_ciphertext, name="price_ciphertext")
        _validate_ciphertext(pk, b.quantity_ciphertext, name="quantity_ciphertext")
        key = (b.bidder_id, b.commitment)
        if key in seen:
            raise ValueError("duplicate bid")
        seen.add(key)

    comparison_count = 0
    decrypt_count = 0

    # Sort bids by descending price using comparison oracle (sign bits only).
    # Selection sort: O(n^2) comparisons, fine for n <= 8.
    remaining = list(bids)
    ordered: list[EncryptedBid] = []
    while remaining:
        best_idx = 0
        for i in range(1, len(remaining)):
            cmp = compare_encrypted(
                sk, pk, remaining[i].price_ciphertext, remaining[best_idx].price_ciphertext
            )
            comparison_count += 1
            if cmp.value > 0:
                best_idx = i
            elif cmp.value == 0:
                best_key = (remaining[best_idx].commitment, remaining[best_idx].bidder_id)
                curr_key = (remaining[i].commitment, remaining[i].bidder_id)
                if curr_key < best_key:
                    best_idx = i
        ordered.append(remaining.pop(best_idx))

    # Walk through ordered bids, filling units.
    # Decrypt quantities only for winning bids (part of public result).
    # Decrypt price only for the marginal bid (clearing price).
    remaining_units = int(units_for_sale)
    fills: list[SealedBidFill] = []
    clearing_price = 0
    total_filled = 0
    marginal_idx = -1
    for idx, bid in enumerate(ordered):
        if remaining_units <= 0:
            break
        quantity = _decrypt_value(sk, bid.quantity_ciphertext)
        decrypt_count += 1
        if quantity <= 0 or quantity > MAX_V1_UNITS:
            raise ValueError("decrypted quantity out of range")
        fill_qty = min(int(quantity), remaining_units)
        if fill_qty <= 0:
            continue
        total_filled += fill_qty
        remaining_units -= fill_qty
        fills.append(
            SealedBidFill(
                bidder_id=bid.bidder_id,
                commitment=bid.commitment,
                filled_quantity=fill_qty,
                paid_price=0,
            )
        )
        marginal_idx = idx

    # Decrypt only the marginal bid's price -> clearing price.
    if marginal_idx >= 0:
        clearing_price = _decrypt_value(sk, ordered[marginal_idx].price_ciphertext)
        decrypt_count += 1
        if clearing_price <= 0 or clearing_price > MAX_PRICE:
            raise ValueError("decrypted clearing price out of range")

    if clearing_price > 0:
        fills = [
            SealedBidFill(
                bidder_id=f.bidder_id,
                commitment=f.commitment,
                filled_quantity=f.filled_quantity,
                paid_price=int(clearing_price),
            )
            for f in fills
        ]

    production_claim = key_pair.key_bits >= 1024 and range_proof_verified

    return FHESettlementResult(
        clearing_price=int(clearing_price),
        total_filled=int(total_filled),
        fills=tuple(fills),
        production_security_claim=production_claim,
        scheme=SCHEME_FHE,
        key_id=str(key_pair.key_id),
        comparison_count=int(comparison_count),
        decrypt_count=int(decrypt_count),
        range_proof_verified=range_proof_verified,
    )


# ── Commit/reveal fallback ──────────────────────────────────────────────


def _settle_commit_reveal_fallback(
    *,
    auction_id: str,
    units_for_sale: int,
    revealed_bids: Iterable[RevealedSealedBid],
) -> FHESettlementResult:
    """Degrade to the existing commit/reveal settlement path."""
    settlement = settle_uniform_price_sealed_bids(
        units_for_sale=units_for_sale,
        bids=revealed_bids,
    )
    return FHESettlementResult(
        clearing_price=int(settlement.clearing_price),
        total_filled=int(settlement.total_filled),
        fills=settlement.fills,
        production_security_claim=False,
        scheme=SCHEME_FALLBACK,
        key_id="",
        comparison_count=0,
        decrypt_count=0,
        range_proof_verified=False,
    )


def settle_sealed_bids_with_fhe(
    *,
    auction_id: str,
    units_for_sale: int,
    encrypted_bids: Iterable[EncryptedBid] | None = None,
    revealed_bids: Iterable[RevealedSealedBid] | None = None,
    key_pair: PaillierKeyPair | None = None,
    range_proof_verified: bool = False,
) -> FHESettlementResult:
    """Unified entry point: use FHE when a key is provisioned, else fallback."""
    if key_pair is not None and encrypted_bids is not None:
        return settle_fhe_sealed_bids(
            auction_id=auction_id,
            units_for_sale=units_for_sale,
            encrypted_bids=encrypted_bids,
            key_pair=key_pair,
            range_proof_verified=range_proof_verified,
        )
    if revealed_bids is not None:
        return _settle_commit_reveal_fallback(
            auction_id=auction_id,
            units_for_sale=units_for_sale,
            revealed_bids=revealed_bids,
        )
    raise ValueError(
        "either (encrypted_bids and key_pair) or revealed_bids must be provided"
    )


# ── Receipt and verification ────────────────────────────────────────────


def fhe_sealed_bid_v1_receipt_hash(body: Dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes(_RECEIPT_DOMAIN) + canonical_json_bytes(body))


def _settlement_to_public_result(
    *, clearing_price: int, total_filled: int, fills: tuple[SealedBidFill, ...],
    units_for_sale: int,
) -> Dict[str, Any]:
    return {
        "units_for_sale": int(units_for_sale),
        "clearing_price": int(clearing_price),
        "total_filled": int(total_filled),
        "fill_count": int(len(fills)),
        "fills": [
            {
                "bidder_id": str(f.bidder_id),
                "commitment": str(f.commitment),
                "filled_quantity": int(f.filled_quantity),
                "paid_price": int(f.paid_price),
            }
            for f in fills
        ],
    }


def make_fhe_sealed_bid_v1_receipt(
    *,
    auction_id: str,
    units_for_sale: int,
    result: FHESettlementResult,
) -> Dict[str, Any]:
    """Build a verifiable receipt for an FHE sealed-bid settlement."""
    body = {
        "schema": "zenodex/fhe_sealed_bid_v1/v1",
        "auction_id": str(auction_id),
        "scheme": str(result.scheme),
        "key_id": str(result.key_id),
        "production_security_claim": bool(result.production_security_claim),
        "range_proof_verified": bool(result.range_proof_verified),
        "comparison_count": int(result.comparison_count),
        "decrypt_count": int(result.decrypt_count),
        "limits": {
            "max_bids": int(MAX_V1_BIDS),
            "max_units": int(MAX_V1_UNITS),
            "max_price": int(MAX_PRICE),
        },
        "public_result": _settlement_to_public_result(
            clearing_price=result.clearing_price,
            total_filled=result.total_filled,
            fills=result.fills,
            units_for_sale=units_for_sale,
        ),
    }
    return {"body": body, "receipt_hash": fhe_sealed_bid_v1_receipt_hash(body)}


def verify_fhe_sealed_bid_v1_receipt(
    receipt: Dict[str, Any],
    *,
    approved_key_ids: Iterable[str],
    trusted_plain_bids: Iterable[RevealedSealedBid] | None = None,
) -> Tuple[bool, str]:
    """Verify an FHE sealed-bid v1 receipt.

    When trusted_plain_bids is provided, the public result is checked
    against a deterministic plaintext replay to ensure correctness.
    """
    if not isinstance(receipt, dict):
        return False, "bad_receipt_type"
    body = receipt.get("body")
    if not isinstance(body, dict):
        return False, "missing_body"
    if body.get("schema") != "zenodex/fhe_sealed_bid_v1/v1":
        return False, "bad_schema"

    want_hash = receipt.get("receipt_hash")
    if not isinstance(want_hash, str) or not want_hash:
        return False, "missing_receipt_hash"
    if fhe_sealed_bid_v1_receipt_hash(body) != want_hash:
        return False, "hash_mismatch"

    scheme = body.get("scheme")
    if scheme not in (SCHEME_FHE, SCHEME_FALLBACK):
        return False, "bad_scheme"

    key_id = body.get("key_id")
    if scheme == SCHEME_FHE:
        if not isinstance(key_id, str) or not key_id:
            return False, "bad_key_id"
        if key_id not in {str(x) for x in approved_key_ids if str(x)}:
            return False, "key_not_approved"
        if not isinstance(body.get("production_security_claim"), bool):
            return False, "production_claim_missing"
        if not isinstance(body.get("range_proof_verified"), bool):
            return False, "range_proof_missing"
        if (
            body.get("production_security_claim") is True
            and body.get("range_proof_verified") is not True
        ):
            return False, "production_claim_requires_range_proof"
    else:
        if key_id != "":
            return False, "fallback_should_have_empty_key_id"
        if body.get("production_security_claim") is not False:
            return False, "fallback_should_not_claim_production"

    auction_id = body.get("auction_id")
    if not isinstance(auction_id, str) or not auction_id:
        return False, "bad_auction_id"

    result = body.get("public_result")
    if not isinstance(result, dict):
        return False, "bad_public_result"
    units_for_sale = _receipt_int(result.get("units_for_sale"))
    clearing_price = _receipt_int(result.get("clearing_price"))
    total_filled = _receipt_int(result.get("total_filled"))
    fill_count = _receipt_int(result.get("fill_count"))
    if units_for_sale is None or clearing_price is None or total_filled is None or fill_count is None:
        return False, "bad_public_result_numeric"
    if units_for_sale <= 0 or units_for_sale > MAX_V1_UNITS:
        return False, "units_for_sale_out_of_range"
    if clearing_price < 0 or clearing_price > MAX_PRICE:
        return False, "clearing_price_out_of_range"
    if total_filled < 0 or total_filled > units_for_sale:
        return False, "total_filled_out_of_range"

    fills = result.get("fills")
    if not isinstance(fills, list):
        return False, "bad_fills"
    if len(fills) != fill_count:
        return False, "fill_count_mismatch"
    filled_sum = 0
    for fill in fills:
        if not isinstance(fill, dict):
            return False, "bad_fill"
        filled_quantity = _receipt_int(fill.get("filled_quantity"))
        paid_price = _receipt_int(fill.get("paid_price"))
        if filled_quantity is None or paid_price is None:
            return False, "bad_fill_numeric"
        if filled_quantity <= 0 or filled_quantity > MAX_V1_UNITS:
            return False, "filled_quantity_out_of_range"
        if paid_price != clearing_price:
            return False, "paid_price_mismatch"
        filled_sum += filled_quantity
    if filled_sum != total_filled:
        return False, "filled_sum_mismatch"

    if trusted_plain_bids is None:
        return False, "unauthenticated_public_result"
    plain_bids = tuple(trusted_plain_bids)
    if len(plain_bids) == 0 or len(plain_bids) > MAX_V1_BIDS:
        return False, "trusted_plain_bid_count_out_of_range"
    try:
        expected = settle_uniform_price_sealed_bids(
            units_for_sale=units_for_sale, bids=plain_bids
        )
    except (AttributeError, TypeError, ValueError, OverflowError):
        return False, "bad_trusted_plain_bids"
    expected_result = _settlement_to_public_result(
        clearing_price=expected.clearing_price,
        total_filled=expected.total_filled,
        fills=expected.fills,
        units_for_sale=units_for_sale,
    )
    if expected_result != result:
        return False, "public_result_mismatch"
    return True, "ok"
