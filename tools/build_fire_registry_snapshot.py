from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.registry.snapshot_v1 import (  # noqa: E402
    DEMO_SIGNER_PRIVKEY,
    build_fire_registry_snapshot,
)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build the canonical FIRE registry snapshot from the current admitted object slice.")
    parser.add_argument("--output-dir", type=Path, required=True, help="Directory that will contain the bundle subdirs and signed registry index")
    parser.add_argument("--snapshot-name", default="devnet_v1", help="Logical snapshot name recorded in release metadata")
    parser.add_argument("--signer-privkey", default=DEMO_SIGNER_PRIVKEY, help="BLS private key used to sign the registry index")
    parser.add_argument(
        "--emit-proof-tree-cert",
        action="store_true",
        help="Emit non-authoritative draft proof-tree cert sidecars in every bundle",
    )
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    try:
        payload = build_fire_registry_snapshot(
            output_dir=args.output_dir,
            snapshot_name=args.snapshot_name,
            signer_privkey=args.signer_privkey,
            emit_proof_tree_cert=args.emit_proof_tree_cert,
        )
    except (OSError, RuntimeError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    if args.pretty:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
