"""Deterministic K03 static no-bypass checker and structural mutants."""

from __future__ import annotations

import sys
from pathlib import Path

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from tools.check_fcis_m6_k03_static_no_bypass import (  # noqa: E402
    load_policy,
    run_static_scan,
    scan_python_source,
    scan_rust_source,
)


def _kinds(issues: list[dict[str, object]]) -> set[str]:
    return {str(issue["kind"]) for issue in issues}


def run_checks() -> None:
    policy = load_policy()
    report = run_static_scan(policy=policy)
    if report["ok"] is not True:
        raise AssertionError(f"K03 protected source scan failed: {report}")
    if report["python_checked_file_count"] != 4:
        raise AssertionError("K03 did not scan all four protected Python files")
    if report["rust_checked_file_count"] != 0:
        raise AssertionError("K03 unexpectedly claims an M6 Rust publisher")
    if report["rust_scope_status"] != "unmounted_no_m6_rust_publisher":
        raise AssertionError("K03 Rust unmounted boundary is not explicit")

    forbidden_import = scan_python_source(
        "import sqlite3\n\ndef bypass():\n    return sqlite3.connect(':memory:')\n",
        "src/core/mutant_forbidden_import.py",
        policy,
    )
    if "forbidden_core_import" not in _kinds(forbidden_import):
        raise AssertionError("K03 did not kill the forbidden-import mutant")

    direct_write = scan_python_source(
        "def bypass(connection):\n    connection.execute('INSERT INTO balances VALUES (?)')\n",
        "src/core/mutant_direct_write.py",
        policy,
    )
    if not {"forbidden_direct_effect_call", "protected_table_write_literal"}.issubset(
        _kinds(direct_write)
    ):
        raise AssertionError("K03 did not kill the direct-write mutant")

    legacy = scan_python_source(
        "def bypass(source):\n    return evaluate_refinement_v1(source)\n",
        "src/core/mutant_legacy_publisher.py",
        policy,
    )
    if "legacy_publisher_call" not in _kinds(legacy):
        raise AssertionError("K03 did not kill the legacy-publisher mutant")

    authoritative = scan_python_source(
        "def bypass(root):\n    return D08CombinedANFAcceptV1(root)\n",
        "src/core/mutant_authoritative_constructor.py",
        policy,
    )
    if "direct_authoritative_constructor" not in _kinds(authoritative):
        raise AssertionError("K03 did not kill the authoritative-constructor mutant")

    port_bypass = scan_python_source(
        "def bypass(port, state, request):\n    return publish_v1(port, state, request)\n",
        "src/integration/mutant_port_bypass.py",
        policy,
    )
    if "direct_publication_port_bypass" not in _kinds(port_bypass):
        raise AssertionError("K03 did not kill the direct-port bypass mutant")

    rust = scan_rust_source(
        "use std::fs::File;\nfn bypass(connection: Conn) { connection.execute(); }\n",
        "rust-runtime/src/mutant.rs",
        policy,
    )
    if not {"forbidden_rust_import", "forbidden_rust_effect_call"}.issubset(_kinds(rust)):
        raise AssertionError("K03 did not kill the Rust structural mutant")

    clean = scan_python_source(
        "from dataclasses import dataclass\n\n@dataclass(frozen=True)\nclass Value:\n    root: str\n",
        "src/core/clean_value.py",
        policy,
    )
    if clean:
        raise AssertionError(f"K03 rejected a clean pure-core witness: {clean}")


if __name__ == "__main__":
    run_checks()
    print("K03_STATIC_NO_BYPASS_MATCH")
