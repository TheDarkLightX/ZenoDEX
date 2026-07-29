#!/usr/bin/env python3
"""Build, verify, and export the exact-head FCIS B1B-1 review packet."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

BASE_PACKET_COMMIT = "1665e788a4c4daf43982262c307d0c04b914d89b"
REPORT_PATH = Path("docs/research/FCIS_M5_P4B5A_B1B1_IMPLEMENTATION_REPORT_20260729.md")
PACKET_DIR = Path("docs/research/prompts/fcis_m5_p4b5a_b1b1_implementation_review_v1")
README_PATH = PACKET_DIR / "README.md"
REVIEW_PROMPT_PATH = PACKET_DIR / "REVIEW_PROMPT.md"
MANIFEST_PATH = PACKET_DIR / "SOURCE_MANIFEST.sha256"
METADATA_PATH = PACKET_DIR / "PACKET_METADATA.json"
CHANGE_INVENTORY_PATH = PACKET_DIR / "CHANGE_INVENTORY.json"
OUTPUT_PATHS = (
    README_PATH,
    REVIEW_PROMPT_PATH,
    MANIFEST_PATH,
    METADATA_PATH,
    CHANGE_INVENTORY_PATH,
)
PACKET_SIBLINGS_IN_MANIFEST = (
    README_PATH,
    REVIEW_PROMPT_PATH,
    METADATA_PATH,
    CHANGE_INVENTORY_PATH,
)

CONTEXT_PATHS = (
    Path(
        "docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md"
    ),
    Path(
        "docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_1_20260729.md"
    ),
    Path("docs/research/FCIS_M5_P4B5A_CONFIGURATION_CLAIM_VALIDATION_CONTRACT_20260728.md"),
    Path(
        "docs/research/prompts/"
        "fcis_m5_p4b5a_dynamic_apportionment_architecture_v1/SRGD_V1_AMENDMENT.md"
    ),
    Path("docs/research/prompts/fcis_m5_p4b5a_b1b_revision34_review_v1/README.md"),
    Path("docs/research/prompts/fcis_m5_p4b5a_b1b_revision34_review_v1/REVIEW_PROMPT.md"),
    Path("docs/research/prompts/fcis_m5_p4b5a_b1b_revision34_review_v1/SOURCE_MANIFEST.sha256"),
    Path("src/core/fcis_fee_distribution_configuration_values.py"),
    Path("src/core/fcis_fee_distribution_configuration_schema.py"),
    Path("src/core/fcis_fee_distribution_configuration_admission.py"),
    Path("src/core/fcis_fee_distribution_configuration_codec.py"),
    Path("src/core/fcis_fee_distribution_configuration_verification.py"),
    Path("src/state/canonical.py"),
    Path("pyproject.toml"),
    Path("requirements-core.lock.txt"),
)
RUST_WORKSPACE_STATIC_PATHS = (
    Path("rust-runtime/Cargo.toml"),
    Path("rust-runtime/Cargo.lock"),
    Path("rust-runtime/rust-toolchain.toml"),
    Path("rust-runtime/fuzz/Cargo.toml"),
    Path("rust-runtime/crates/zenodex-launcher/Cargo.toml"),
    Path("rust-runtime/crates/zenodex-runtime-core/Cargo.toml"),
    Path("rust-runtime/crates/zenodex-runtime-cli/Cargo.toml"),
    Path("rust-runtime/crates/zenodex-governance-gate/Cargo.toml"),
)
RUST_CORE_PREFIX = "rust-runtime/crates/zenodex-runtime-core/"
DELIVERY_BUNDLE_NAME = "FCIS_B1B1_EXACT_HEAD.bundle"
DELIVERY_RECEIPT_NAME = "DELIVERY_RECEIPT.json"
DELIVERY_PACKET_DIR = Path("packet")


@dataclass(frozen=True, slots=True)
class ChangeEntry:
    status: str
    source_path: Path | None
    target_path: Path | None


def _git_bytes(*arguments: str) -> bytes:
    completed = subprocess.run(
        ["git", *arguments],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return completed.stdout


def _git_text(*arguments: str) -> str:
    return _git_bytes(*arguments).decode("utf-8").strip()


def _commit_blob(commit: str, path: Path) -> bytes:
    return _git_bytes("show", f"{commit}:{path.as_posix()}")


def _safe_git_path(raw: bytes) -> Path:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError("changed path is not UTF-8") from exc
    pure = PurePosixPath(text)
    if (
        not text
        or text.startswith("/")
        or "\\" in text
        or "//" in text
        or text.endswith("/")
        or "\n" in text
        or "\r" in text
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise ValueError(f"unsafe changed path: {text!r}")
    return Path(*pure.parts)


def _change_sort_key(entry: ChangeEntry) -> tuple[bytes, bytes, bytes]:
    path = entry.target_path or entry.source_path
    if path is None:
        raise ValueError("change entry has neither source nor target path")
    source = (
        b""
        if entry.source_path is None
        else entry.source_path.as_posix().encode("utf-8")
    )
    return (
        path.as_posix().encode("utf-8"),
        entry.status.encode("ascii"),
        source,
    )


def _parse_name_status_z(payload: bytes) -> tuple[ChangeEntry, ...]:
    if not payload:
        return ()
    tokens = payload.split(b"\0")
    if tokens[-1] != b"":
        raise ValueError("name-status stream is not NUL terminated")
    tokens.pop()
    entries: list[ChangeEntry] = []
    index = 0
    while index < len(tokens):
        try:
            status = tokens[index].decode("ascii")
        except UnicodeDecodeError as exc:
            raise ValueError("change status is not ASCII") from exc
        index += 1
        if not status or status[0] not in "ACDMRTUXB":
            raise ValueError(f"unsupported change status: {status!r}")
        kind = status[0]
        source: Path | None
        target: Path | None
        if kind in {"R", "C"}:
            if index + 1 >= len(tokens):
                raise ValueError(f"truncated {kind} change entry")
            source = _safe_git_path(tokens[index])
            target = _safe_git_path(tokens[index + 1])
            index += 2
        else:
            if index >= len(tokens):
                raise ValueError(f"truncated {kind} change entry")
            path = _safe_git_path(tokens[index])
            index += 1
            source = None if kind == "A" else path
            target = None if kind == "D" else path
        entries.append(ChangeEntry(status, source, target))
    return tuple(sorted(entries, key=_change_sort_key))


def _changed_entries(
    target_commit: str,
    *,
    base_commit: str = BASE_PACKET_COMMIT,
) -> tuple[ChangeEntry, ...]:
    output = _git_bytes(
        "diff",
        "--name-status",
        "-z",
        "-M",
        "-C",
        "--find-copies-harder",
        f"{base_commit}..{target_commit}",
    )
    return _parse_name_status_z(output)


def _rust_closure_paths(target_commit: str) -> tuple[Path, ...]:
    output = _git_bytes(
        "ls-tree",
        "-r",
        "--name-only",
        "-z",
        target_commit,
        "--",
        RUST_CORE_PREFIX,
    )
    paths = {
        _safe_git_path(raw)
        for raw in output.split(b"\0")
        if raw
    }
    paths.update(RUST_WORKSPACE_STATIC_PATHS)
    return tuple(sorted(paths, key=lambda path: path.as_posix().encode("utf-8")))


def _target_inventory(
    target_commit: str,
    entries: tuple[ChangeEntry, ...],
) -> tuple[Path, ...]:
    paths = {
        entry.target_path
        for entry in entries
        if entry.target_path is not None
    }
    paths.update(CONTEXT_PATHS)
    paths.update(_rust_closure_paths(target_commit))
    paths.difference_update(OUTPUT_PATHS)
    return tuple(
        sorted(
            (path for path in paths if path is not None),
            key=lambda path: path.as_posix().encode("utf-8"),
        )
    )


def _blob_document(commit: str, path: Path) -> dict[str, str]:
    blob = _commit_blob(commit, path)
    return {
        "git_blob_oid": _git_text("rev-parse", f"{commit}:{path.as_posix()}"),
        "sha256": hashlib.sha256(blob).hexdigest(),
    }


def _change_inventory_document(
    target_commit: str,
    entries: tuple[ChangeEntry, ...],
    *,
    base_commit: str = BASE_PACKET_COMMIT,
) -> dict[str, object]:
    return {
        "base_commit": base_commit,
        "base_tree": _git_text("rev-parse", f"{base_commit}^{{tree}}"),
        "entries": [
            {
                "base_blob": (
                    None
                    if entry.source_path is None
                    else _blob_document(base_commit, entry.source_path)
                ),
                "source_path": (
                    None
                    if entry.source_path is None
                    else entry.source_path.as_posix()
                ),
                "status": entry.status,
                "target_blob": (
                    None
                    if entry.target_path is None
                    else _blob_document(target_commit, entry.target_path)
                ),
                "target_path": (
                    None
                    if entry.target_path is None
                    else entry.target_path.as_posix()
                ),
            }
            for entry in entries
        ],
        "schema": "zenodex/fcis/b1b1-change-inventory/v2",
        "target_commit": target_commit,
        "target_tree": _git_text("rev-parse", f"{target_commit}^{{tree}}"),
    }


def _json_bytes(document: Mapping[str, object]) -> bytes:
    return (json.dumps(document, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _status_counts(entries: tuple[ChangeEntry, ...]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for entry in entries:
        kind = entry.status[0]
        counts[kind] = counts.get(kind, 0) + 1
    return dict(sorted(counts.items()))


def _metadata_bytes(
    target_commit: str,
    entries: tuple[ChangeEntry, ...],
    inventory: tuple[Path, ...],
    rust_closure: tuple[Path, ...],
) -> bytes:
    document = {
        "base_packet_commit": BASE_PACKET_COMMIT,
        "base_packet_tree": _git_text(
            "rev-parse", f"{BASE_PACKET_COMMIT}^{{tree}}"
        ),
        "change_status_counts": _status_counts(entries),
        "changed_path_count": len(entries),
        "delivery_receipt_rule": (
            "packet commit SHA, tree, parent, bundle hash, and packet hashes are "
            "recorded after commit in external DELIVERY_RECEIPT.json"
        ),
        "inventory_rule": (
            "every deletion-aware committed change from approved base through "
            "target, every target-present changed blob, bounded immutable "
            "context, and standalone-runnable Rust core workspace closure"
        ),
        "manifest_entry_count": len(inventory) + len(PACKET_SIBLINGS_IN_MANIFEST),
        "packet_output_paths": [path.as_posix() for path in OUTPUT_PATHS],
        "packet_relation": "documentation-only commit exactly one child of target",
        "rust_closure_entry_count": len(rust_closure),
        "schema": "zenodex/fcis/b1b1-implementation-review-packet/v2",
        "target_commit": target_commit,
        "target_tree": _git_text("rev-parse", f"{target_commit}^{{tree}}"),
    }
    return _json_bytes(document)


def _readme_bytes(
    target_commit: str,
    entries: tuple[ChangeEntry, ...],
    inventory: tuple[Path, ...],
) -> bytes:
    text = f"""# FCIS M5-P4B5A B1B-1 exact-head repair review packet

```text
exact implementation target: {target_commit}
approved Revision 3.4 packet:  {BASE_PACKET_COMMIT}
changed entries:              {len(entries)}
manifest entries:             {len(inventory) + len(PACKET_SIBLINGS_IN_MANIFEST)}
packet relation:              documentation-only commit exactly one child of target
```

This packet authorizes read-only, falsification-first review of the exact
unmounted B1B-1 implementation target. It authorizes no repair, migration,
publication, runtime mount, or B1B-2 implementation.

`CHANGE_INVENTORY.json` records additions, copies, deletions, modifications,
renames, type changes, and every other supported Git status with base and
target blob evidence. Deleted paths are tombstones and therefore do not appear
as target blobs in `SOURCE_MANIFEST.sha256`.

Reproduce from a repository containing the approved base and imported bundle:

```bash
python3 -m tools.build_fcis_b1b1_implementation_review_packet --check
sha256sum -c {MANIFEST_PATH.as_posix()}
python3 -m tools.check_fcis_b1b_revision34_contract --json
cargo test --locked --manifest-path rust-runtime/Cargo.toml \
  -p zenodex-runtime-core fcis_b1b_authority
```

After the packet commit, export a bounded Git bundle plus receipt:

```bash
python3 -m tools.build_fcis_b1b1_implementation_review_packet \
  --export-delivery /path/to/delivery
python3 -m tools.build_fcis_b1b1_implementation_review_packet \
  --check-delivery /path/to/delivery
```

The external delivery receipt records the exact packet commit SHA. A commit
cannot contain its own SHA without a circular self-reference.
"""
    return text.encode("utf-8")


def _review_prompt_bytes(target_commit: str) -> bytes:
    text = f"""# B1B-1 repaired exact-head independent review

Review target:

```text
implementation commit: {target_commit}
approved design packet: {BASE_PACKET_COMMIT}
required verdict: APPROVE_B1B1_EXACT_HEAD_UNMOUNTED
               or REVISE_B1B1_EXACT_HEAD
               or REJECT_B1B1_SCOPE_VIOLATION
```

Verify the bundle, external delivery receipt, packet parent relation, base and
target trees, deletion-aware change inventory, metadata, and every source
manifest hash before reviewing claims.

Falsify at least:

1. recursion, depth, node, collection, byte, and UTF-8 escape from admission;
2. Python/Rust resource-bound rejection disagreement;
3. extra or omitted Python/Rust carrier fields and non-injective encoding;
4. aliased, qualified, or novel-path carrier consumers;
5. Rust `lib.rs` authority helpers and hidden public surfaces;
6. premature verifier, migration, state, transition, receipt, bundle, proof,
   publication, or mount symbols;
7. deleted guard or test paths omitted from packet evidence;
8. incomplete Cargo workspace closure;
9. stale, incomplete, or self-inconsistent packet evidence.

Do not repair the target during review. Report exact commands, minimized
witnesses, unrun gates, residual risk, and one permitted verdict.
"""
    return text.encode("utf-8")


def _manifest_bytes(
    target_commit: str,
    inventory: tuple[Path, ...],
    packet_siblings: dict[Path, bytes],
) -> bytes:
    lines: list[str] = []
    for path in inventory:
        digest = hashlib.sha256(_commit_blob(target_commit, path)).hexdigest()
        lines.append(f"{digest}  {path.as_posix()}\n")
    for path in PACKET_SIBLINGS_IN_MANIFEST:
        digest = hashlib.sha256(packet_siblings[path]).hexdigest()
        lines.append(f"{digest}  {path.as_posix()}\n")
    return "".join(
        sorted(lines, key=lambda line: line.split("  ", 1)[1].encode("utf-8"))
    ).encode("utf-8")


def _expected_outputs(target_commit: str) -> dict[Path, bytes]:
    entries = _changed_entries(target_commit)
    inventory = _target_inventory(target_commit, entries)
    rust_closure = _rust_closure_paths(target_commit)
    siblings = {
        README_PATH: _readme_bytes(target_commit, entries, inventory),
        REVIEW_PROMPT_PATH: _review_prompt_bytes(target_commit),
        METADATA_PATH: _metadata_bytes(
            target_commit, entries, inventory, rust_closure
        ),
        CHANGE_INVENTORY_PATH: _json_bytes(
            _change_inventory_document(target_commit, entries)
        ),
    }
    return {
        README_PATH: siblings[README_PATH],
        REVIEW_PROMPT_PATH: siblings[REVIEW_PROMPT_PATH],
        MANIFEST_PATH: _manifest_bytes(target_commit, inventory, siblings),
        METADATA_PATH: siblings[METADATA_PATH],
        CHANGE_INVENTORY_PATH: siblings[CHANGE_INVENTORY_PATH],
    }


def _packet_target_from_metadata() -> str:
    document = json.loads(METADATA_PATH.read_text(encoding="utf-8"))
    target = document.get("target_commit")
    if type(target) is not str or not re_full_hex(target):
        raise ValueError("packet metadata has no exact target commit")
    return target


def re_full_hex(value: str) -> bool:
    return len(value) == 40 and all(character in "0123456789abcdef" for character in value)


def _verify_packet_relation(target_commit: str) -> tuple[str, str]:
    head = _git_text("rev-parse", "HEAD")
    parent_line = _git_text("rev-list", "--parents", "-n", "1", head).split()
    if len(parent_line) != 2 or parent_line[1] != target_commit:
        raise ValueError("packet commit must have exactly target as its one parent")
    entries = _changed_entries(head, base_commit=target_commit)
    actual_paths = {
        entry.target_path or entry.source_path
        for entry in entries
    }
    if (
        actual_paths != set(OUTPUT_PATHS)
        or any(entry.status[0] not in {"A", "M"} for entry in entries)
    ):
        raise ValueError(f"packet commit changed unexpected entries: {entries!r}")
    return head, _git_text("rev-parse", f"{head}^{{tree}}")


def _check() -> None:
    target_commit = _packet_target_from_metadata()
    _verify_packet_relation(target_commit)
    for path, expected in _expected_outputs(target_commit).items():
        actual = path.read_bytes()
        if actual != expected:
            raise ValueError(f"stale packet output: {path}")


def _build() -> None:
    if _git_text("status", "--porcelain"):
        raise ValueError("generate packet from a clean implementation target")
    target_commit = _git_text("rev-parse", "HEAD")
    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", BASE_PACKET_COMMIT, target_commit],
        check=False,
    )
    if ancestor.returncode != 0:
        raise ValueError("implementation target does not descend from approved packet")
    outputs = _expected_outputs(target_commit)
    PACKET_DIR.mkdir(parents=True, exist_ok=True)
    for path, payload in outputs.items():
        path.write_bytes(payload)


def _delivery_packet_path(delivery: Path, path: Path) -> Path:
    return delivery / DELIVERY_PACKET_DIR / path


def _export_delivery(destination: Path) -> None:
    destination = destination.resolve()
    destination.mkdir(parents=True, exist_ok=False)
    target_commit = _packet_target_from_metadata()
    packet_commit, packet_tree = _verify_packet_relation(target_commit)
    bundle_path = destination / DELIVERY_BUNDLE_NAME
    subprocess.run(
        [
            "git",
            "bundle",
            "create",
            str(bundle_path),
            f"{BASE_PACKET_COMMIT}..{packet_commit}",
        ],
        check=True,
    )
    subprocess.run(["git", "bundle", "verify", str(bundle_path)], check=True)

    packet_hashes: dict[str, str] = {}
    for path in OUTPUT_PATHS:
        payload = _commit_blob(packet_commit, path)
        output = _delivery_packet_path(destination, path)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(payload)
        packet_hashes[path.as_posix()] = hashlib.sha256(payload).hexdigest()

    receipt = {
        "base_commit": BASE_PACKET_COMMIT,
        "base_tree": _git_text("rev-parse", f"{BASE_PACKET_COMMIT}^{{tree}}"),
        "bundle_file": DELIVERY_BUNDLE_NAME,
        "bundle_sha256": hashlib.sha256(bundle_path.read_bytes()).hexdigest(),
        "packet_commit": packet_commit,
        "packet_files": packet_hashes,
        "packet_parent": target_commit,
        "packet_tree": packet_tree,
        "schema": "zenodex/fcis/b1b1-exact-head-delivery/v1",
        "target_commit": target_commit,
        "target_tree": _git_text("rev-parse", f"{target_commit}^{{tree}}"),
    }
    (destination / DELIVERY_RECEIPT_NAME).write_bytes(_json_bytes(receipt))


def _check_delivery(destination: Path) -> None:
    destination = destination.resolve()
    receipt_path = destination / DELIVERY_RECEIPT_NAME
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    if receipt.get("schema") != "zenodex/fcis/b1b1-exact-head-delivery/v1":
        raise ValueError("unknown delivery receipt schema")
    packet_commit = receipt.get("packet_commit")
    target_commit = receipt.get("target_commit")
    if type(packet_commit) is not str or not re_full_hex(packet_commit):
        raise ValueError("delivery has no exact packet commit")
    if type(target_commit) is not str or not re_full_hex(target_commit):
        raise ValueError("delivery has no exact target commit")
    bundle_path = destination / DELIVERY_BUNDLE_NAME
    if hashlib.sha256(bundle_path.read_bytes()).hexdigest() != receipt.get(
        "bundle_sha256"
    ):
        raise ValueError("delivery bundle hash mismatch")
    subprocess.run(["git", "bundle", "verify", str(bundle_path)], check=True)
    heads = _git_text("bundle", "list-heads", str(bundle_path))
    if packet_commit not in heads:
        raise ValueError("delivery bundle omits packet commit")
    if receipt.get("packet_parent") != target_commit:
        raise ValueError("delivery packet parent mismatch")
    packet_files = receipt.get("packet_files")
    if type(packet_files) is not dict or set(packet_files) != {
        path.as_posix() for path in OUTPUT_PATHS
    }:
        raise ValueError("delivery packet file set mismatch")
    for path in OUTPUT_PATHS:
        payload = _delivery_packet_path(destination, path).read_bytes()
        if hashlib.sha256(payload).hexdigest() != packet_files[path.as_posix()]:
            raise ValueError(f"delivery packet hash mismatch: {path}")
        if payload != _commit_blob(packet_commit, path):
            raise ValueError(f"delivery packet blob mismatch: {path}")
    expected_files = {
        Path(DELIVERY_BUNDLE_NAME),
        Path(DELIVERY_RECEIPT_NAME),
        *(
            DELIVERY_PACKET_DIR / path
            for path in OUTPUT_PATHS
        ),
    }
    actual_files = {
        path.relative_to(destination)
        for path in destination.rglob("*")
        if path.is_file()
    }
    if actual_files != expected_files:
        raise ValueError("delivery contains undeclared files")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--export-delivery", type=Path)
    mode.add_argument("--check-delivery", type=Path)
    args = parser.parse_args()
    try:
        if args.check:
            _check()
        elif args.export_delivery is not None:
            _export_delivery(args.export_delivery)
        elif args.check_delivery is not None:
            _check_delivery(args.check_delivery)
        else:
            _build()
    except (
        OSError,
        ValueError,
        TypeError,
        json.JSONDecodeError,
        subprocess.CalledProcessError,
    ) as exc:
        print(f"error: {exc}")
        return 1
    print("ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
