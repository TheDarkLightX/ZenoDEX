#!/usr/bin/env python3
"""Build or verify the exact-head FCIS B1B-1 implementation review packet."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

BASE_PACKET_COMMIT = "1665e788a4c4daf43982262c307d0c04b914d89b"
REPORT_PATH = Path("docs/research/FCIS_M5_P4B5A_B1B1_IMPLEMENTATION_REPORT_20260729.md")
PACKET_DIR = Path("docs/research/prompts/fcis_m5_p4b5a_b1b1_implementation_review_v1")
README_PATH = PACKET_DIR / "README.md"
REVIEW_PROMPT_PATH = PACKET_DIR / "REVIEW_PROMPT.md"
MANIFEST_PATH = PACKET_DIR / "SOURCE_MANIFEST.sha256"
METADATA_PATH = PACKET_DIR / "PACKET_METADATA.json"
OUTPUT_PATHS = (
    README_PATH,
    REVIEW_PROMPT_PATH,
    MANIFEST_PATH,
    METADATA_PATH,
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
    Path("rust-runtime/crates/zenodex-runtime-core/src/canonical.rs"),
    Path("rust-runtime/Cargo.toml"),
    Path("rust-runtime/Cargo.lock"),
    Path("pyproject.toml"),
    Path("requirements-core.lock.txt"),
)


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


def _changed_paths(target_commit: str) -> tuple[Path, ...]:
    output = _git_text(
        "diff",
        "--name-only",
        "--diff-filter=ACMRT",
        f"{BASE_PACKET_COMMIT}..{target_commit}",
    )
    return tuple(Path(line) for line in output.splitlines() if line)


def _inventory(target_commit: str) -> tuple[Path, ...]:
    paths = set(_changed_paths(target_commit))
    paths.update(CONTEXT_PATHS)
    return tuple(sorted(paths, key=lambda path: path.as_posix()))


def _manifest_bytes(target_commit: str, inventory: tuple[Path, ...]) -> bytes:
    lines = []
    for path in inventory:
        digest = hashlib.sha256(_commit_blob(target_commit, path)).hexdigest()
        lines.append(f"{digest}  {path.as_posix()}\n")
    return "".join(lines).encode("utf-8")


def _metadata_bytes(target_commit: str, inventory: tuple[Path, ...]) -> bytes:
    target_tree = _git_text("rev-parse", f"{target_commit}^{{tree}}")
    document = {
        "base_packet_commit": BASE_PACKET_COMMIT,
        "changed_path_count": len(_changed_paths(target_commit)),
        "inventory_rule": (
            "all committed paths changed from the approved Revision 3.4 packet "
            "through the implementation target, plus bounded immutable context"
        ),
        "manifest_entry_count": len(inventory),
        "packet_relation": "documentation-only commit exactly one child of target",
        "schema": "zenodex/fcis/b1b1-implementation-review-packet/v1",
        "target_commit": target_commit,
        "target_tree": target_tree,
    }
    return (json.dumps(document, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _readme_bytes(target_commit: str, inventory: tuple[Path, ...]) -> bytes:
    text = f"""# FCIS M5-P4B5A B1B-1 implementation review packet

```text
exact implementation target: {target_commit}
approved Revision 3.4 packet:  {BASE_PACKET_COMMIT}
manifest entries:              {len(inventory)}
packet relation:               documentation-only commit exactly one child of target
```

This packet authorizes read-only, falsification-first review of the exact
unmounted B1B-1 implementation target. It authorizes no repair, push, pull
request mutation, migration, publication, runtime mount, or B1B-2
implementation.

Reproduce from the repository root:

```bash
python3 -m tools.build_fcis_b1b1_implementation_review_packet --check
sha256sum -c {MANIFEST_PATH.as_posix()}
python3 -B tools/check_fcis_m5_p4b5a_atdd_contract.py \\
  --assigned-id ATDD-B1B1-009 \\
  --diff-base {BASE_PACKET_COMMIT}
python3 -m tools.check_fcis_b1b_revision34_contract --json
```

The manifest contains every committed path changed from the approved packet
through the target, plus bounded immutable design, B1A, canonical-codec, and
toolchain context. The manifest excludes packet outputs and therefore has no
self-hash.
"""
    return text.encode("utf-8")


def _review_prompt_bytes(target_commit: str) -> bytes:
    text = f"""# B1B-1 exact-head independent review

Review target:

```text
implementation commit: {target_commit}
approved design packet: {BASE_PACKET_COMMIT}
required verdict: APPROVE_B1B1_EXACT_HEAD_UNMOUNTED
               or REVISE_B1B1_EXACT_HEAD
               or REJECT_B1B1_SCOPE_VIOLATION
```

Use the complete review contract in:

```text
docs/research/prompts/fcis_m5_p4b5a_atdd_subagents_v1/B1B1_REVIEW_PROMPT.md
```

Verify the packet builder, parent relation, metadata, and every manifest hash
before reviewing claims. Review only the bounded repository paths in the
manifest and the exact implementation diff from `{BASE_PACKET_COMMIT}`.

Falsify at least:

1. approved-source drift;
2. hidden environment setup;
3. open, ambiguous, or non-canonical carrier decoding;
4. U256, Boolean, Unicode, identifier, and digest boundary disagreement;
5. Python/Rust byte, root, or rejection disagreement;
6. carrier-to-authority promotion;
7. bare-header transition or anchor-to-pin conversion;
8. premature state, transition, receipt, bundle, proof, publication, or mount;
9. runtime reachability outside the declared carrier surface;
10. stale, incomplete, or self-inconsistent packet evidence.

Do not repair the target during review. Report exact commands, minimized
witnesses, unrun gates, residual risk, and one permitted verdict.
"""
    return text.encode("utf-8")


def _expected_outputs(target_commit: str) -> dict[Path, bytes]:
    inventory = _inventory(target_commit)
    return {
        README_PATH: _readme_bytes(target_commit, inventory),
        REVIEW_PROMPT_PATH: _review_prompt_bytes(target_commit),
        MANIFEST_PATH: _manifest_bytes(target_commit, inventory),
        METADATA_PATH: _metadata_bytes(target_commit, inventory),
    }


def _packet_target_from_metadata() -> str:
    document = json.loads(METADATA_PATH.read_text(encoding="utf-8"))
    target = document.get("target_commit")
    if type(target) is not str or len(target) != 40:
        raise ValueError("packet metadata has no exact target commit")
    return target


def _verify_packet_relation(target_commit: str) -> None:
    head = _git_text("rev-parse", "HEAD")
    parent = _git_text("rev-parse", "HEAD^")
    if head == target_commit or parent != target_commit:
        raise ValueError("packet commit must be exactly one child of target")
    output = _git_text("diff", "--name-only", f"{target_commit}..{head}")
    actual = {Path(line) for line in output.splitlines() if line}
    if actual != set(OUTPUT_PATHS):
        raise ValueError(f"packet commit changed unexpected paths: {sorted(actual)}")


def _check() -> None:
    target_commit = _packet_target_from_metadata()
    _verify_packet_relation(target_commit)
    for path, expected in _expected_outputs(target_commit).items():
        actual = path.read_bytes()
        if actual != expected:
            raise ValueError(f"stale packet output: {path}")


def _build() -> None:
    status = _git_text("status", "--porcelain")
    if status:
        raise ValueError("generate the packet from a clean implementation target")
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        if args.check:
            _check()
        else:
            _build()
    except (OSError, ValueError, TypeError, subprocess.CalledProcessError) as exc:
        print(f"error: {exc}")
        return 1
    print("ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
