"""Create one byte-checked temporary ABI proof subject; never edit source inputs."""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SUBJECT = "zk/global_settlement_abi_v1/src/asset_transfer.rs"
EXPECTED_SUBJECT = "78d28167d5360c22b3749812bdab224fe1a2b7888899db363b5dbc5d981dbcb0"
MUTANTS = {
    "wrapping_debit": (
        "current\n            .checked_sub(delta.unsigned_abs())\n            .ok_or(AssetTransferRejectCodeV1::INSUFFICIENT_BALANCE)",
        "Ok(current.wrapping_sub(delta.unsigned_abs()))",
    ),
    "wrapping_credit": (
        "current\n            .checked_add(delta.unsigned_abs())\n            .ok_or(AssetTransferRejectCodeV1::BALANCE_OVERFLOW)",
        "Ok(current.wrapping_add(delta.unsigned_abs()))",
    ),
    "omitted_minimum": (
        "    if magnitude == I128_MIN_MAGNITUDE {\n        return Ok(i128::MIN);\n    }\n",
        "",
    ),
}


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def prepare(repo: Path, output: Path, mutant: str | None) -> None:
    manifest_bytes = (HERE / "source_manifest.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    if manifest[SUBJECT] != EXPECTED_SUBJECT:
        raise ValueError("unreviewed arithmetic subject pin")
    originals = {}
    for name, digest in manifest.items():
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("nonlocal source path")
        raw = (repo / relative).read_bytes()
        if sha256(raw) != digest:
            raise ValueError(f"original source drift: {name}")
        originals[name] = raw
    harness = (HERE / "harnesses.rs").read_bytes()
    if b"kani::assume" in harness or b"kani::unwind" in harness:
        raise ValueError("unreviewed restriction on universal inputs")
    changed = originals[SUBJECT]
    if mutant:
        before, after = (value.encode() for value in MUTANTS[mutant])
        if changed.count(before) != 1:
            raise ValueError("mutant no longer targets exactly one original expression")
        changed = changed.replace(before, after)
    instrumented = changed + harness
    output.mkdir(parents=True, exist_ok=False)
    for name, raw in originals.items():
        target = output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(instrumented if name == SUBJECT else raw)
    for name, raw in originals.items():
        expected = instrumented if name == SUBJECT else raw
        if (output / name).read_bytes() != expected:
            raise ValueError("prepared subject byte verification failed")
    if mutant is None and not instrumented.startswith(originals[SUBJECT]):
        raise ValueError("baseline instrumentation changed an original byte")
    diff = "".join(difflib.unified_diff(
        originals[SUBJECT].decode().splitlines(keepends=True),
        instrumented.decode().splitlines(keepends=True),
        fromfile=SUBJECT, tofile=SUBJECT + ".instrumented"))
    (output / "instrumentation.diff").write_text(diff)
    receipt = {
        "schema": "zenodex/kani-asset-arithmetic-instrumentation/v1",
        "original_manifest_sha256": sha256(manifest_bytes), "original_files": len(originals),
        "original_subject_sha256": EXPECTED_SUBJECT, "harness_sha256": sha256(harness),
        "instrumented_subject_sha256": sha256(instrumented),
        "instrumentation_diff_sha256": sha256(diff.encode()), "mutant": mutant,
        "all_original_files_verified": True, "baseline_original_prefix_unchanged": mutant is None,
        "proof_executed": False, "production_authority": False,
    }
    (output / "instrumentation.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--mutant", choices=tuple(MUTANTS))
    args = parser.parse_args()
    prepare(args.repo, args.output, args.mutant)
