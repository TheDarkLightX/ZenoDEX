"""Multi-process determinism tests.

A hash that's deterministic *within* a single Python process can still
diverge *across* processes if a dependency carries hidden init state — most
notably ``hashlib`` when its OpenSSL backend is configured differently in
parent vs child, but also any ``str.intern`` quirk, locale-dependent JSON
formatting, or PYTHONHASHSEED leak.

These tests spawn child interpreters via ``subprocess.run`` (always fresh,
no inherited state) and assert byte-for-byte agreement with the parent's
output. We exercise both ``fork`` and ``spawn`` semantics, and a fully
isolated subinterpreter spawn that wipes ``PYTHONHASHSEED``.

If any of these fail, the underlying issue is **cross-process commitment
drift** — two operators running the same code on the same hardware would
publish different hashes for the same input. That's a consensus break.
"""

from __future__ import annotations

import multiprocessing as mp
import os
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.zeno_ledger_v0 import hash_v0, merkle_root_v0
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex


_PROJECT_ROOT = Path(__file__).resolve().parents[2]


# -----------------------------------------------------------------------------
# A. Subprocess helpers.
# -----------------------------------------------------------------------------


def _run_in_child(
    script_body: str,
    *,
    env_overrides: dict[str, str] | None = None,
    use_clean_env: bool = False,
) -> str:
    """Run ``script_body`` in a fresh Python interpreter and return stdout.

    ``script_body`` must end by printing the result to stdout (no trailing
    newline guaranteed). The child inherits ``sys.path`` via the project
    root prepend.
    """
    full_script = (
        f"import sys; sys.path.insert(0, {str(_PROJECT_ROOT)!r}); "
        f"{script_body}"
    )
    env = dict(os.environ) if not use_clean_env else {}
    if env_overrides:
        env.update(env_overrides)
    # Ensure PATH is at least set so the python binary is discoverable.
    if "PATH" not in env:
        env["PATH"] = os.environ.get("PATH", "/usr/bin:/bin")
    result = subprocess.run(
        [sys.executable, "-c", full_script],
        capture_output=True,
        text=True,
        env=env,
        timeout=30,
        check=True,
    )
    return result.stdout.strip()


# -----------------------------------------------------------------------------
# B. SHA-256 determinism across child interpreters.
# -----------------------------------------------------------------------------


class TestSha256AcrossChildren:
    def test_empty_bytes_hash_matches_parent(self) -> None:
        parent = sha256_hex(b"")
        child = _run_in_child(
            "from src.state.canonical import sha256_hex; print(sha256_hex(b''))"
        )
        assert parent == child

    def test_abc_bytes_hash_matches_parent(self) -> None:
        parent = sha256_hex(b"abc")
        child = _run_in_child(
            "from src.state.canonical import sha256_hex; print(sha256_hex(b'abc'))"
        )
        assert parent == child

    def test_hash_with_randomized_pythonhashseed_still_matches(self) -> None:
        # PYTHONHASHSEED randomizes Python's str.__hash__ — must NOT affect
        # canonical hashing (which uses sha256, not Python's dict-hash).
        parent = sha256_hex(b"abc")
        child = _run_in_child(
            "from src.state.canonical import sha256_hex; print(sha256_hex(b'abc'))",
            env_overrides={"PYTHONHASHSEED": "random"},
        )
        assert parent == child

    def test_hash_with_fixed_pythonhashseed_zero_matches(self) -> None:
        parent = sha256_hex(b"abc")
        child = _run_in_child(
            "from src.state.canonical import sha256_hex; print(sha256_hex(b'abc'))",
            env_overrides={"PYTHONHASHSEED": "0"},
        )
        assert parent == child

    def test_hash_with_fixed_pythonhashseed_99_matches(self) -> None:
        parent = sha256_hex(b"abc")
        child = _run_in_child(
            "from src.state.canonical import sha256_hex; print(sha256_hex(b'abc'))",
            env_overrides={"PYTHONHASHSEED": "99"},
        )
        assert parent == child


# -----------------------------------------------------------------------------
# C. canonical_json_bytes determinism across children.
# -----------------------------------------------------------------------------


class TestCanonicalJsonAcrossChildren:
    def test_sorted_dict_bytes_match(self) -> None:
        parent = canonical_json_bytes({"b": 2, "a": 1, "c": 3}).decode("utf-8")
        child = _run_in_child(
            "from src.state.canonical import canonical_json_bytes; "
            "print(canonical_json_bytes({'b':2,'a':1,'c':3}).decode('utf-8'))"
        )
        assert parent == child
        assert child == '{"a":1,"b":2,"c":3}'

    def test_unicode_string_bytes_match(self) -> None:
        # zürich UTF-8 bytes should be preserved (ensure_ascii=False).
        parent = canonical_json_bytes("zürich")
        child_hex = _run_in_child(
            "from src.state.canonical import canonical_json_bytes; "
            "print(canonical_json_bytes('zürich').hex())"
        )
        assert parent.hex() == child_hex

    def test_huge_int_bytes_match(self) -> None:
        n = 2**256 - 1
        parent = canonical_json_bytes(n).decode("utf-8")
        child = _run_in_child(
            f"from src.state.canonical import canonical_json_bytes; "
            f"print(canonical_json_bytes({n}).decode('utf-8'))"
        )
        assert parent == child


# -----------------------------------------------------------------------------
# D. hash_v0 / merkle_root_v0 determinism across children.
# -----------------------------------------------------------------------------


class TestHashV0AcrossChildren:
    def test_dict_hash_matches_parent(self) -> None:
        parent = hash_v0("d", {"a": 1, "b": [2, 3]})
        child = _run_in_child(
            "from src.integration.zeno_ledger_v0 import hash_v0; "
            "print(hash_v0('d', {'a':1, 'b':[2,3]}))"
        )
        assert parent == child

    def test_bytes_hash_matches_parent(self) -> None:
        parent = hash_v0("d", b"abc")
        child = _run_in_child(
            "from src.integration.zeno_ledger_v0 import hash_v0; "
            "print(hash_v0('d', b'abc'))"
        )
        assert parent == child

    def test_merkle_root_matches_parent(self) -> None:
        leaves = ["0x" + "11" * 32, "0x" + "22" * 32, "0x" + "33" * 32]
        parent = merkle_root_v0("d", leaves)
        leaves_repr = repr(leaves)
        child = _run_in_child(
            f"from src.integration.zeno_ledger_v0 import merkle_root_v0; "
            f"print(merkle_root_v0('d', {leaves_repr}))"
        )
        assert parent == child


# -----------------------------------------------------------------------------
# E. Determinism across multiprocessing start methods.
# -----------------------------------------------------------------------------


def _hash_in_subprocess(payload: dict[str, object], queue: mp.Queue) -> None:
    """Module-level so ``spawn`` start method can pickle/import it."""
    from src.integration.zeno_ledger_v0 import hash_v0 as _h

    queue.put(_h("d", payload))


class TestMultiprocessingStartMethods:
    def test_fork_child_produces_same_hash(self) -> None:
        if "fork" not in mp.get_all_start_methods():
            pytest.skip("fork start method unavailable on this platform")
        ctx = mp.get_context("fork")
        q: mp.Queue = ctx.Queue()
        payload = {"a": 1, "b": 2}
        p = ctx.Process(target=_hash_in_subprocess, args=(payload, q))
        p.start()
        p.join(timeout=10)
        child_hash = q.get(timeout=2)
        parent_hash = hash_v0("d", payload)
        assert child_hash == parent_hash

    def test_spawn_child_produces_same_hash(self) -> None:
        ctx = mp.get_context("spawn")
        q: mp.Queue = ctx.Queue()
        payload = {"a": 1, "b": 2}
        p = ctx.Process(target=_hash_in_subprocess, args=(payload, q))
        p.start()
        p.join(timeout=15)
        child_hash = q.get(timeout=2)
        parent_hash = hash_v0("d", payload)
        assert child_hash == parent_hash

    def test_forkserver_child_produces_same_hash(self) -> None:
        if "forkserver" not in mp.get_all_start_methods():
            pytest.skip("forkserver start method unavailable on this platform")
        ctx = mp.get_context("forkserver")
        q: mp.Queue = ctx.Queue()
        payload = {"a": 1, "b": 2}
        p = ctx.Process(target=_hash_in_subprocess, args=(payload, q))
        p.start()
        p.join(timeout=15)
        child_hash = q.get(timeout=2)
        parent_hash = hash_v0("d", payload)
        assert child_hash == parent_hash


# -----------------------------------------------------------------------------
# F. Multiple sequential children must agree with each other.
# -----------------------------------------------------------------------------


class TestSequentialChildrenAgree:
    def test_five_sequential_subprocesses_all_agree(self) -> None:
        results: list[str] = []
        for _ in range(5):
            out = _run_in_child(
                "from src.integration.zeno_ledger_v0 import hash_v0; "
                "print(hash_v0('d', {'k': 'v', 'n': 42}))"
            )
            results.append(out)
        assert len(set(results)) == 1, f"divergence detected: {results}"

    def test_parent_matches_five_children(self) -> None:
        parent = hash_v0("d", {"k": "v", "n": 42})
        for _ in range(5):
            child = _run_in_child(
                "from src.integration.zeno_ledger_v0 import hash_v0; "
                "print(hash_v0('d', {'k': 'v', 'n': 42}))"
            )
            assert child == parent


# -----------------------------------------------------------------------------
# G. domain_sep_bytes determinism across children.
# -----------------------------------------------------------------------------


class TestDomainSepBytesAcrossChildren:
    def test_label_v1_bytes_match(self) -> None:
        parent = domain_sep_bytes("x", version=1)
        child_hex = _run_in_child(
            "from src.state.canonical import domain_sep_bytes; "
            "print(domain_sep_bytes('x', version=1).hex())"
        )
        assert parent.hex() == child_hex

    def test_multichar_label_v99_bytes_match(self) -> None:
        parent = domain_sep_bytes("zeno_ledger_v0", version=99)
        child_hex = _run_in_child(
            "from src.state.canonical import domain_sep_bytes; "
            "print(domain_sep_bytes('zeno_ledger_v0', version=99).hex())"
        )
        assert parent.hex() == child_hex


# -----------------------------------------------------------------------------
# H. Clean-environment isolation — proves we don't rely on env vars.
# -----------------------------------------------------------------------------


class TestCleanEnvironmentChildren:
    def test_hash_in_completely_clean_env_matches_parent(self) -> None:
        parent = hash_v0("d", {"a": 1})
        child = _run_in_child(
            "from src.integration.zeno_ledger_v0 import hash_v0; "
            "print(hash_v0('d', {'a': 1}))",
            use_clean_env=True,
        )
        assert child == parent

    def test_sha256_in_clean_env_matches_parent(self) -> None:
        parent = sha256_hex(b"abc")
        child = _run_in_child(
            "from src.state.canonical import sha256_hex; print(sha256_hex(b'abc'))",
            use_clean_env=True,
        )
        assert child == parent
