#!/usr/bin/env python3
"""Write one create-new frozen ZRPF V3 source-closure snapshot."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

if __package__:
    from tools import zrpf_v3_source_closure as closure
else:
    import zrpf_v3_source_closure as closure  # type: ignore[no-redef]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository-root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    try:
        report = closure.build_source_closure(args.repository_root)
        raw = closure.canonical_json_bytes(report)
        closure.write_create_new(args.out, raw)
    except (closure.SourceClosureError, OSError) as exc:
        print(
            json.dumps(
                {
                    "errors": [str(exc)],
                    "ok": False,
                    "schema": closure.SCHEMA,
                    "status": "rejected",
                },
                sort_keys=True,
                separators=(",", ":"),
            )
        )
        return 1
    print(
        json.dumps(
            {
                "file_count": report["file_count"],
                "git_commit": report["git_commit"],
                "ok": True,
                "schema": closure.SCHEMA,
                "sha256": report["sha256"],
                "status": "frozen_source_closure_written",
            },
            sort_keys=True,
            separators=(",", ":"),
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
