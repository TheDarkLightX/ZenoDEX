#!/usr/bin/env python3
"""Build the deterministic active reproof V3 reference from governed inputs."""

from __future__ import annotations

import json

import check_risc0_recursive_active_reproof_v3 as checker


def main() -> int:
    sources = []
    for workspace_id, (path, count, root_hash) in checker.SOURCE_ROOTS.items():
        sources.append(
            {
                "file_count": count,
                "inventory_root": root_hash,
                "path": path,
                "workspace_id": workspace_id,
            }
        )
    evidence_files = checker.inventory(checker.EVIDENCE)
    promotion_files = checker.explicit_inventory(checker.PROMOTION_SOURCE_PATHS)
    document = {
        "claims": checker.CLAIMS,
        "evidence": {
            "file_count": checker.EVIDENCE_COUNT,
            "files": evidence_files,
            "inventory_root": checker.EVIDENCE_ROOT,
        },
        "host_binaries": checker.HOST_BINARIES,
        "promotion_source_inventory": {
            "file_count": len(promotion_files),
            "files": promotion_files,
            "inventory_root": checker.inventory_root(promotion_files),
        },
        "programs": checker.PROGRAMS,
        "receipt_security": checker.SECURITY,
        "schema": checker.SCHEMA,
        "sdk_version": "3.0.5",
        "source_inventories": sources,
        "source_base_revision": checker.BASE_REVISION,
        "toolchain": checker.TOOLCHAIN,
    }
    checker.REFERENCE.write_bytes(
        json.dumps(document, separators=(",", ":"), sort_keys=True).encode()
    )
    checker.validate(document)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
