#!/usr/bin/env python3
"""Build the source-pinned M6/ZRPF donor-candidate inventory.

The inventory records candidates for later obligation-sized review. Inclusion
does not authorize a cherry-pick, merge, mount, deployment, or promotion.
Output is deterministic for a fixed Git ref set and object database.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPO_ROOT / "docs/research/PRODUCTION_READINESS_DONOR_INVENTORY_V1.json"
DEFAULT_BASE_COMMIT = "b6842cd26aadf32b7ee774f58665570479cacfe6"
SCHEMA = "zenodex/production-readiness-donor-inventory/v1"
MATCH_PATTERN = re.compile(r"(?:m6|zrpf)", re.IGNORECASE)


def _run_git(repo_root: Path, arguments: Sequence[str]) -> bytes:
    result = subprocess.run(
        ["git", *arguments],
        cwd=repo_root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", "replace").strip()
        raise ValueError(f"git {' '.join(arguments)} failed: {detail}")
    return result.stdout


def _git_succeeds(repo_root: Path, *arguments: str) -> bool:
    result = subprocess.run(
        ["git", *arguments],
        cwd=repo_root,
        check=False,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return result.returncode == 0


def _matched_ref_tips(repo_root: Path) -> list[dict[str, str]]:
    raw = _run_git(
        repo_root,
        ["for-each-ref", "--format=%(refname)%09%(objectname)", "refs/heads", "refs/remotes"],
    ).decode("utf-8", "surrogateescape")
    rows: list[dict[str, str]] = []
    for line in raw.splitlines():
        ref_name, object_id = line.split("\t", 1)
        if MATCH_PATTERN.search(ref_name):
            rows.append({"ref": ref_name, "tip": object_id})
    return sorted(rows, key=lambda row: row["ref"])


def _subject_candidates(repo_root: Path) -> dict[str, str]:
    raw = _run_git(
        repo_root,
        [
            "log",
            "--all",
            "--regexp-ignore-case",
            "--grep=m6",
            "--grep=zrpf",
            "--format=%H%x00%s%x00",
        ],
    )
    fields = raw.split(b"\0")
    if fields and fields[-1] == b"\n":
        fields.pop()
    candidates: dict[str, str] = {}
    for index in range(0, len(fields) - 1, 2):
        commit = fields[index].decode("ascii").strip()
        subject = fields[index + 1].decode("utf-8", "surrogateescape")
        if commit and MATCH_PATTERN.search(subject):
            candidates[commit] = subject
    return candidates


def _commit_metadata(repo_root: Path, commit: str) -> dict[str, Any]:
    raw = _run_git(
        repo_root,
        ["show", "-s", "--format=%H%x00%T%x00%P%x00%cI%x00%s", commit],
    )
    fields = raw.decode("utf-8", "surrogateescape").rstrip("\n").split("\0", 4)
    if len(fields) != 5 or fields[0] != commit:
        raise ValueError(f"unexpected metadata for donor candidate {commit}")
    return {
        "commit": fields[0],
        "tree": fields[1],
        "parents": fields[2].split() if fields[2] else [],
        "committed_at": fields[3],
        "subject": fields[4],
    }


def _relation_to_base(repo_root: Path, base_commit: str, candidate: str) -> str:
    if candidate == base_commit:
        return "BASELINE"
    if _git_succeeds(repo_root, "merge-base", "--is-ancestor", candidate, base_commit):
        return "ANCESTOR_INCLUDED"
    if _git_succeeds(repo_root, "merge-base", "--is-ancestor", base_commit, candidate):
        return "DESCENDANT_UNVERIFIED"
    return "DIVERGED_UNREVIEWED"


def _candidate_rows(
    repo_root: Path,
    base_commit: str,
    matched_refs: list[dict[str, str]],
    subject_candidates: Mapping[str, str],
) -> list[dict[str, Any]]:
    refs_by_tip: dict[str, list[str]] = defaultdict(list)
    for row in matched_refs:
        refs_by_tip[row["tip"]].append(row["ref"])
    candidate_ids = sorted(set(subject_candidates) | set(refs_by_tip))
    candidates: list[dict[str, Any]] = []
    for candidate_id in candidate_ids:
        metadata = _commit_metadata(repo_root, candidate_id)
        relation = _relation_to_base(repo_root, base_commit, candidate_id)
        matched_by = []
        if candidate_id in subject_candidates:
            matched_by.append("SUBJECT")
        if candidate_id in refs_by_tip:
            matched_by.append("REF_TIP")
        candidates.append(
            {
                **metadata,
                "matched_by": matched_by,
                "matching_refs": sorted(refs_by_tip.get(candidate_id, [])),
                "relation_to_base": relation,
                "review_status": (
                    "BASELINE_INCLUDED"
                    if relation in {"BASELINE", "ANCESTOR_INCLUDED"}
                    else "UNREVIEWED"
                ),
                "imported_into_g0": False,
                "obligation_ids": [],
            }
        )
    return candidates


def _relation_counts(candidates: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    return {
        relation: sum(row["relation_to_base"] == relation for row in candidates)
        for relation in (
            "BASELINE",
            "ANCESTOR_INCLUDED",
            "DESCENDANT_UNVERIFIED",
            "DIVERGED_UNREVIEWED",
        )
    }


def build_inventory(repo_root: Path, base_commit: str) -> dict[str, Any]:
    """Return the exact candidate inventory for the available Git refs."""

    if not re.fullmatch(r"[0-9a-f]{40}", base_commit):
        raise ValueError("base_commit must be a lowercase 40-character Git object id")
    resolved_base = _run_git(repo_root, ["rev-parse", f"{base_commit}^{{commit}}"])
    if resolved_base.decode("ascii").strip() != base_commit:
        raise ValueError("base_commit does not resolve to itself")

    matched_refs = _matched_ref_tips(repo_root)
    candidates = _candidate_rows(
        repo_root,
        base_commit,
        matched_refs,
        _subject_candidates(repo_root),
    )

    canonical_ref_snapshot = "".join(
        f"{row['tip']}\t{row['ref']}\n" for row in matched_refs
    ).encode("utf-8", "surrogateescape")
    return {
        "schema": SCHEMA,
        "version": 1,
        "status": "FROZEN_UNREVIEWED",
        "production_promotion": False,
        "base_commit": base_commit,
        "discovery_rule": {
            "ref_name_regex": "(?i)(m6|zrpf)",
            "commit_subject_regex": "(?i)(m6|zrpf)",
            "scope": "available refs/heads and refs/remotes at G0 freeze",
            "candidate_union": ["matching ref tips", "matching commit subjects reachable from --all"],
        },
        "matched_ref_snapshot_sha256": hashlib.sha256(canonical_ref_snapshot).hexdigest(),
        "matched_ref_tips": matched_refs,
        "counts": {
            "matched_refs": len(matched_refs),
            "unique_candidates": len(candidates),
            **_relation_counts(candidates),
            "imports": 0,
        },
        "candidates": candidates,
        "nonclaims": [
            "A candidate is an untrusted patch source until an obligation-sized review accepts exact hunks.",
            "Historical or diverged receipts do not establish same-subject evidence for the G0 base.",
            "This local ref snapshot may name commits that a shallow or differently fetched clone does not contain.",
            "No candidate was imported into G0.",
        ],
    }


def _encoded(inventory: dict[str, Any]) -> str:
    return json.dumps(inventory, indent=2, sort_keys=True, ensure_ascii=True) + "\n"


def _write_atomic(output: Path, encoded: str) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        dir=output.parent,
        prefix=f".{output.name}.",
        suffix=".tmp",
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as destination:
            destination.write(encoded)
            destination.flush()
            os.fsync(destination.fileno())
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--base-commit", default=DEFAULT_BASE_COMMIT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)

    try:
        inventory = build_inventory(args.repo_root.resolve(), args.base_commit)
        encoded = _encoded(inventory)
        if args.check:
            if not args.output.is_file() or args.output.read_text(encoding="utf-8") != encoded:
                print("donor inventory drift", file=sys.stderr)
                return 1
        else:
            _write_atomic(args.output, encoded)
    except (OSError, ValueError) as exc:
        print(f"donor inventory error: {exc}", file=sys.stderr)
        return 2

    print(
        json.dumps(
            {
                "schema": SCHEMA,
                "status": "PASS",
                "check_mode": args.check,
                "candidate_count": inventory["counts"]["unique_candidates"],
                "import_count": inventory["counts"]["imports"],
                "output": str(args.output),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
