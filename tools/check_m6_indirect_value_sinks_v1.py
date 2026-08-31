#!/usr/bin/env python3
"""Check or render the bounded O-007C indirect value-sink registry."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.build_m6_normative_requirements_v1 import (  # noqa: E402
    _atomic_replace_regular_file_v1,
    _require_inert_path_v1,
)
from tools.m6_indirect_value_sinks.inventory import (  # noqa: E402
    REGISTRY_PATH,
    collect_inventory_facts,
    render_registry,
)
from tools.m6_indirect_value_sinks.model import (  # noqa: E402
    IndirectSinkRejectV1,
    pretty_json_bytes,
)
from tools.m6_indirect_value_sinks.report import (  # noqa: E402
    build_indirect_value_sink_report,
)

REPO_ROOT = Path(__file__).resolve().parents[1]


def _registry_bytes(root: Path) -> bytes:
    facts = collect_inventory_facts(root)
    return pretty_json_bytes(render_registry(root, facts, reviewed=False))


def _write_registry(root: Path) -> str:
    destination = root / REGISTRY_PATH
    if destination.exists():
        raise IndirectSinkRejectV1(
            "REGISTRY_EXISTS", REGISTRY_PATH, "refusing to overwrite an existing registry"
        )
    payload = _registry_bytes(root)
    _atomic_replace_regular_file_v1(destination, payload)
    return hashlib.sha256(payload).hexdigest()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--emit-registry", action="store_true")
    parser.add_argument("--write-registry", action="store_true")
    args = parser.parse_args(argv)
    if args.emit_registry and args.write_registry:
        parser.error("choose only one registry output mode")
    root = _require_inert_path_v1(args.root, "O007C registry root")
    try:
        if args.emit_registry:
            sys.stdout.buffer.write(_registry_bytes(root))
            return 0
        if args.write_registry:
            print(_write_registry(root))
            return 0
        report = build_indirect_value_sink_report(root)
        print(json.dumps(report, sort_keys=True))
        return 0 if report["ok"] is True else 1
    except IndirectSinkRejectV1 as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
