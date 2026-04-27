from __future__ import annotations

from dataclasses import replace

from src.fire.registry.lock_v1 import (
    build_fire_object_dependency_lock,
    fire_object_lock_file_sha256,
    load_fire_object_dependency_lock,
    verify_fire_object_dependency_lock,
    write_fire_object_dependency_lock,
)
from src.fire.runtime.burn_boost_call_v1 import BurnBoostCallTerms, build_manifest, compile_terms


def _sample_lock():
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    manifest = build_manifest(artifact)
    return manifest, build_fire_object_dependency_lock(manifest)


def test_fire_object_dependency_lock_round_trip_and_verify() -> None:
    manifest, lock = _sample_lock()

    restored = type(lock).from_dict(lock.to_dict())

    assert restored == lock
    assert verify_fire_object_dependency_lock(restored, object_manifest=manifest) == (True, None)


def test_fire_object_dependency_lock_detects_hash_tamper() -> None:
    manifest, lock = _sample_lock()
    tampered = replace(lock, lock_hash="sha256:" + "0" * 64)

    assert verify_fire_object_dependency_lock(tampered, object_manifest=manifest) == (False, "lock_hash_mismatch")


def test_fire_object_dependency_lock_write_and_load_round_trip(tmp_path) -> None:
    _, lock = _sample_lock()
    lock_path = tmp_path / "object_lock.json"

    written_sha256 = write_fire_object_dependency_lock(lock_path, lock)
    loaded_lock, loaded_sha256 = load_fire_object_dependency_lock(lock_path)

    assert loaded_lock == lock
    assert written_sha256 == loaded_sha256 == fire_object_lock_file_sha256(lock)
