from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
from pathlib import Path
from typing import Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.pathing_v1 import (  # noqa: E402
    fire_stdlib_dir,
    fire_stdlib_objects_dir,
    fire_zpl_dir,
    legacy_fire_spec_dir,
    legacy_fire_zpl_dir,
)
from src.fire.compiler.fmos_file_v1 import load_fire_math_object_spec_file  # noqa: E402


REPORT_SCHEMA = "zenodex/fire-source-tree-sync-report/v1"
MANIFEST_SCHEMA = "zenodex/fire-stdlib-manifest/v1"


def _sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def _copy_tree_files(src_dir: Path, dst_dir: Path, suffix: str) -> list[Path]:
    dst_dir.mkdir(parents=True, exist_ok=True)
    copied: list[Path] = []
    for src_path in sorted(src_dir.glob(f"*{suffix}")):
        dst_path = dst_dir / src_path.name
        shutil.copy2(src_path, dst_path)
        copied.append(dst_path)
    return copied


def _build_stdlib_manifest(object_dir: Path, zpl_dir: Path) -> dict[str, object]:
    entries: list[dict[str, object]] = []
    for spec_path in sorted(object_dir.glob("*.json")):
        spec = load_fire_math_object_spec_file(spec_path)
        zpl_path = zpl_dir / f"{spec.object_id}.zpl"
        entries.append(
            {
                "object_id": spec.object_id,
                "object_name": spec.object_name,
                "object_family": spec.object_family,
                "object_version": spec.object_version,
                "spec_path": str(spec_path.relative_to(object_dir.parent.parent)),
                "spec_sha256": _sha256_file(spec_path),
                "zpl_path": None if not zpl_path.exists() else str(zpl_path.relative_to(object_dir.parent.parent)),
                "zpl_sha256": None if not zpl_path.exists() else _sha256_file(zpl_path),
            }
        )
    return {
        "schema": MANIFEST_SCHEMA,
        "entry_count": len(entries),
        "entries": entries,
    }


def sync_fire_source_tree(
    *,
    legacy_spec_dir: Path,
    legacy_zpl_dir: Path,
    stdlib_object_dir: Path,
    target_zpl_dir: Path,
    manifest_path: Path,
) -> dict[str, object]:
    copied_specs = _copy_tree_files(legacy_spec_dir, stdlib_object_dir, ".json")
    copied_zpl = _copy_tree_files(legacy_zpl_dir, target_zpl_dir, ".zpl")
    manifest = _build_stdlib_manifest(stdlib_object_dir, target_zpl_dir)
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "legacy_spec_dir": str(legacy_spec_dir.resolve()),
        "legacy_zpl_dir": str(legacy_zpl_dir.resolve()),
        "stdlib_object_dir": str(stdlib_object_dir.resolve()),
        "zpl_dir": str(target_zpl_dir.resolve()),
        "manifest_path": str(manifest_path.resolve()),
        "spec_count": len(copied_specs),
        "zpl_count": len(copied_zpl),
    }


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Sync the current FIRE bridge specs into src/fire/.")
    parser.add_argument("--legacy-spec-dir", type=Path, default=legacy_fire_spec_dir())
    parser.add_argument("--legacy-zpl-dir", type=Path, default=legacy_fire_zpl_dir())
    parser.add_argument("--stdlib-object-dir", type=Path, default=fire_stdlib_objects_dir())
    parser.add_argument("--zpl-dir", type=Path, default=fire_zpl_dir())
    parser.add_argument("--manifest-path", type=Path, default=fire_stdlib_dir() / "manifest.json")
    parser.add_argument("--pretty", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    try:
        report = sync_fire_source_tree(
            legacy_spec_dir=args.legacy_spec_dir,
            legacy_zpl_dir=args.legacy_zpl_dir,
            stdlib_object_dir=args.stdlib_object_dir,
            target_zpl_dir=args.zpl_dir,
            manifest_path=args.manifest_path,
        )
    except (OSError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
