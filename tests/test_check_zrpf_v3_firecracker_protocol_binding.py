from __future__ import annotations

from pathlib import Path

from tools import check_zrpf_v3_firecracker_protocol_binding as checker


def test_committed_profile_hash_is_bound_across_all_abi_mirrors() -> None:
    report = checker.build_report()

    assert report["ok"] is True
    assert report["errors"] == []
    assert len(set(report["observed_bindings"].values())) == 1
    assert all(value is False for value in report["authority"].values())


def test_rust_constant_mutation_rejects(tmp_path: Path) -> None:
    raw = checker.RUST_PROTOCOL_PATH.read_bytes()
    first_byte = checker.protocol.CANDIDATE_PROFILE_CANONICAL_SHA256_V1[0]
    replacement = first_byte ^ 1
    changed = raw.replace(
        f"0x{first_byte:02x}".encode("ascii"),
        f"0x{replacement:02x}".encode("ascii"),
        1,
    )
    assert changed != raw
    rust_path = tmp_path / "firecracker_protocol.rs"
    rust_path.write_bytes(changed)

    report = checker.build_report(rust_protocol_path=rust_path)

    assert report["ok"] is False
    assert report["errors"] == ["profile_hash_binding_mismatch"]
