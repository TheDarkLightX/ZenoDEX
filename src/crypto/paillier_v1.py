"""Paillier helper primitives for sealed-bid support.

This module owns randomized key generation and encryption. It is deliberately
outside ``src.core`` so deterministic settlement code does not contain hidden
randomness.
"""

from __future__ import annotations

import math
import secrets
from dataclasses import dataclass

_MILLER_RABIN_ROUNDS = 20


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
    """Generate a Paillier key pair with primes of *key_bits* bits each."""

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
