from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

import pytest

import tools.build_fcis_b1b1_implementation_review_packet as packet_builder
from tools.build_fcis_b1b1_implementation_review_packet import (
    CHANGE_INVENTORY_PATH,
    MANIFEST_PATH,
    OUTPUT_PATHS,
    PACKET_SIBLINGS_IN_MANIFEST,
    ChangeEntry,
    _change_inventory_document,
    _changed_entries,
    _expected_outputs,
    _parse_name_status_z,
    _verify_packet_relation,
)

REPO = Path(__file__).resolve().parents[2]


def _git(repo: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ["git", *arguments],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.strip()


def _repository(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init")
    _git(repo, "config", "user.email", "b1b1@example.invalid")
    _git(repo, "config", "user.name", "B1B1 Packet Test")
    return repo


def _commit_all(repo: Path, message: str) -> str:
    _git(repo, "add", "-A")
    _git(repo, "commit", "-m", message)
    return _git(repo, "rev-parse", "HEAD")


def test_name_status_parser_covers_every_declared_status() -> None:
    payload = (
        b"A\0added\0"
        b"C75\0copy-source\0copy-target\0"
        b"D\0deleted\0"
        b"M\0modified\0"
        b"R100\0rename-source\0rename-target\0"
        b"T\0type-change\0"
        b"U\0unmerged\0"
        b"X\0unknown\0"
        b"B\0broken-pair\0"
    )
    entries = _parse_name_status_z(payload)
    assert {entry.status[0] for entry in entries} == set("ACDMRTUXB")
    added = next(entry for entry in entries if entry.status == "A")
    assert added.source_path is None
    assert added.target_path == Path("added")
    deleted = next(entry for entry in entries if entry.status == "D")
    assert deleted.source_path == Path("deleted")
    assert deleted.target_path is None
    renamed = next(entry for entry in entries if entry.status == "R100")
    assert renamed == ChangeEntry(
        "R100",
        Path("rename-source"),
        Path("rename-target"),
    )


@pytest.mark.parametrize(
    "payload",
    (
        b"A\0unterminated",
        b"Q\0path\0",
        b"A\0/absolute\0",
        b"A\0../escape\0",
        b"A\0double//separator\0",
        b"A\0trailing/\0",
        b"A\0back\\slash\0",
        b"A\0line\nbreak\0",
        b"A\0\xff\0",
        b"R100\0only-source\0",
    ),
)
def test_name_status_parser_fails_closed(payload: bytes) -> None:
    with pytest.raises(ValueError):
        _parse_name_status_z(payload)


def test_deleted_path_has_a_hashed_tombstone(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repo = _repository(tmp_path)
    guard = repo / "src/core/required_guard.py"
    guard.parent.mkdir(parents=True)
    guard.write_text("GUARD = True\n", encoding="utf-8")
    base = _commit_all(repo, "base")
    base_sha256 = hashlib.sha256(guard.read_bytes()).hexdigest()

    guard.unlink()
    (repo / "src/core/replacement.py").write_text("VALUE = 1\n", encoding="utf-8")
    target = _commit_all(repo, "target")
    monkeypatch.chdir(repo)

    entries = _changed_entries(target, base_commit=base)
    deleted = next(entry for entry in entries if entry.status == "D")
    assert deleted.source_path == Path("src/core/required_guard.py")
    assert deleted.target_path is None
    document = _change_inventory_document(target, entries, base_commit=base)
    raw_entries = document["entries"]
    assert type(raw_entries) is list
    tombstone = next(
        entry
        for entry in raw_entries
        if entry["source_path"] == "src/core/required_guard.py"
    )
    assert tombstone["base_blob"]["sha256"] == base_sha256
    assert tombstone["target_blob"] is None
    assert tombstone["target_path"] is None


def test_source_manifest_hashes_all_packet_siblings_and_rust_closure() -> None:
    target = _git(REPO, "rev-parse", "HEAD")
    outputs = _expected_outputs(target)
    manifest = outputs[MANIFEST_PATH].decode("utf-8")
    for path in PACKET_SIBLINGS_IN_MANIFEST:
        assert f"  {path.as_posix()}\n" in manifest
    assert f"  {MANIFEST_PATH.as_posix()}\n" not in manifest
    assert "  rust-runtime/Cargo.toml\n" in manifest
    assert "  rust-runtime/rust-toolchain.toml\n" in manifest
    assert "  rust-runtime/crates/zenodex-runtime-core/Cargo.toml\n" in manifest
    assert "  rust-runtime/crates/zenodex-runtime-core/src/lib.rs\n" in manifest

    inventory = json.loads(outputs[CHANGE_INVENTORY_PATH])
    assert inventory["schema"] == "zenodex/fcis/b1b1-change-inventory/v2"
    assert inventory["base_tree"]
    assert inventory["target_tree"]


def test_packet_relation_accepts_only_one_parent_and_exact_outputs(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repo = _repository(tmp_path)
    (repo / "source.txt").write_text("target\n", encoding="utf-8")
    target = _commit_all(repo, "target")
    for path in OUTPUT_PATHS:
        destination = repo / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(f"{path.name}\n", encoding="utf-8")
    packet = _commit_all(repo, "packet")
    monkeypatch.chdir(repo)
    assert _verify_packet_relation(target) == (
        packet,
        _git(repo, "rev-parse", f"{packet}^{{tree}}"),
    )


def test_packet_relation_rejects_an_extra_path(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repo = _repository(tmp_path)
    (repo / "source.txt").write_text("target\n", encoding="utf-8")
    target = _commit_all(repo, "target")
    for path in OUTPUT_PATHS:
        destination = repo / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(f"{path.name}\n", encoding="utf-8")
    (repo / "unexpected.txt").write_text("unexpected\n", encoding="utf-8")
    _commit_all(repo, "bad packet")
    monkeypatch.chdir(repo)
    with pytest.raises(ValueError, match="unexpected entries"):
        _verify_packet_relation(target)


def test_delivery_export_round_trips_exact_packet_head(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repo = _repository(tmp_path)
    (repo / "source.txt").write_text("base\n", encoding="utf-8")
    base = _commit_all(repo, "base")
    (repo / "source.txt").write_text("target\n", encoding="utf-8")
    target = _commit_all(repo, "target")

    for path in OUTPUT_PATHS:
        destination = repo / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        if path == packet_builder.METADATA_PATH:
            destination.write_text(
                json.dumps({"target_commit": target}) + "\n",
                encoding="utf-8",
            )
        else:
            destination.write_text(f"{path.name}\n", encoding="utf-8")
    packet = _commit_all(repo, "packet")

    monkeypatch.chdir(repo)
    monkeypatch.setattr(packet_builder, "BASE_PACKET_COMMIT", base)
    delivery = tmp_path / "delivery"
    packet_builder._export_delivery(delivery)
    packet_builder._check_delivery(delivery)

    advertised = _git(
        repo,
        "bundle",
        "list-heads",
        str(delivery / packet_builder.DELIVERY_BUNDLE_NAME),
    )
    assert advertised == f"{packet} HEAD"
