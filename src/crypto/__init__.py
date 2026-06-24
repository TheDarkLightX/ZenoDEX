"""Cryptographic helper implementations.

Modules under ``src.crypto`` may use randomness for key generation or client-side
encryption. Deterministic consensus transitions should import only the
deterministic pieces they need, and keep value-moving settlement semantics in
``src.core``.
"""
