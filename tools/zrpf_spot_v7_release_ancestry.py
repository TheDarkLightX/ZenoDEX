"""Raw Git ancestry and governed V7 child-pin checks for release planning."""

from __future__ import annotations

import hashlib
import re
from pathlib import Path, PurePosixPath
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as v6_planner
from tools import zrpf_v6_identity_materialization_git as git_boundary
from tools import zrpf_v6_v7_child_policy_materialization as child_materializer
from tools import zrpf_v6_v7_post_pin_governance as governance
from tools.zrpf_spot_v7_release_schema import (
    V7_CHILD_POLICY_PATH,
    V7_CHILD_POLICY_SYMBOL,
    ReleaseClosureError,
    canonical_sha256,
    require_equal,
    require_exact_fields,
    require_nonzero_hex,
)

MAX_COMMITTED_FILE_BYTES = v6_planner.MAX_TRACKED_SOURCE_BYTES

_GOVERNANCE_FIELDS = {
    "schema",
    "status",
    "c0_commit",
    "c1_commit",
    "c2_commit",
    "governance_commit",
    "plan_sha256",
    "observations_sha256",
    "candidate_report_sha256",
    "materialization_manifest_sha256",
    "v6_settlement_image_id",
    "v6_settlement_image_id_words",
    "v7_child_policy_tree",
    "v7_child_policy_sha256",
    "validated_facts",
    "authority",
    "non_claims",
}
_GOVERNANCE_FACTS = {
    "governance_checkout_is_clean_and_exact": True,
    "c1_is_literal_direct_child_of_c0": True,
    "c1_matches_exact_v6_materialization": True,
    "c2_is_literal_direct_child_of_c1": True,
    "c2_contains_only_exact_v7_child_pin": True,
    "governance_commit_is_literal_direct_child_of_c2": True,
    "governance_commit_adds_only_fixed_canonical_evidence": True,
    "manifest_recomposes_from_committed_evidence": True,
    "v6_settlement_image_id_is_nonzero_and_exact": True,
    "committed_v7_policy_matches_manifest_and_c2_tree": True,
}
_CHILD_POLICY_PATTERN = re.compile(
    rb"pub const "
    + re.escape(V7_CHILD_POLICY_SYMBOL.encode("ascii"))
    + rb"\s*:\s*\[u32;\s*8\]\s*=\s*\[([^\]]*)\]\s*;",
    re.MULTILINE | re.DOTALL,
)


def require_clean_root(repo_root: Path) -> Path:
    """Require the exact clean worktree root and unmodified Git object graph."""

    try:
        root = git_boundary.require_clean_checkout(repo_root)
        child_materializer._require_no_git_grafts(root)
    except (OSError, git_boundary.MaterializationError) as exc:
        raise ReleaseClosureError("release closure requires a clean exact checkout") from exc
    if root != repo_root:
        raise ReleaseClosureError("repository root must be an exact canonical path")
    return root


def validate_governed_ancestry(root: Path, value: Any) -> dict[str, Any]:
    """Validate the governance result and independently read literal parents."""

    require_exact_fields(value, _GOVERNANCE_FIELDS, "post-pin governance result")
    require_equal(value["schema"], governance.CHECK_SCHEMA, "governance schema")
    require_equal(
        value["status"],
        "committed_post_pin_governance_binding_checked",
        "governance status",
    )
    for field in (
        "plan_sha256",
        "observations_sha256",
        "candidate_report_sha256",
        "materialization_manifest_sha256",
        "v6_settlement_image_id",
        "v7_child_policy_sha256",
    ):
        require_nonzero_hex(value[field], 64, f"governance {field}")
    require_equal(
        value["authority"],
        {field: False for field in governance.AUTHORITY_FIELDS},
        "governance authority",
    )
    require_equal(value["non_claims"], list(governance.NON_CLAIMS), "governance nonclaims")
    require_equal(value["validated_facts"], _GOVERNANCE_FACTS, "governance facts")

    c0 = _commit_id(value["c0_commit"], "C0")
    c1 = _commit_id(value["c1_commit"], "C1")
    c2 = _commit_id(value["c2_commit"], "C2")
    g = _commit_id(value["governance_commit"], "G")
    if head_commit(root) != g:
        raise ReleaseClosureError("checkout HEAD differs from governance commit G")
    _require_parent(root, c1, c0, "C1")
    _require_parent(root, c2, c1, "C2")
    _require_parent(root, g, c2, "G")
    c2_tree = commit_tree(root, c2)
    require_equal(value["v7_child_policy_tree"], c2_tree, "governed C2 tree")
    return {
        "c0_commit": c0,
        "c1_commit": c1,
        "c2_commit": c2,
        "governance_commit": g,
        "ordered_commits": [c0, c1, c2, g],
        "c0_tree": commit_tree(root, c0),
        "c1_tree": commit_tree(root, c1),
        "c2_tree": c2_tree,
        "governance_tree": commit_tree(root, g),
        "post_pin_governance_check_sha256": canonical_sha256(value),
        "literal_direct_parent_chain_verified": True,
    }


def validate_child_pin(
    root: Path,
    ancestry: dict[str, Any],
    governed: dict[str, Any],
) -> dict[str, Any]:
    """Bind the exact nonzero child identity at C2 and unchanged at G."""

    c2_raw = commit_file(root, ancestry["c2_commit"], V7_CHILD_POLICY_PATH)
    g_raw = commit_file(root, ancestry["governance_commit"], V7_CHILD_POLICY_PATH)
    if c2_raw != g_raw:
        raise ReleaseClosureError("V7 child policy changed between C2 and G")
    sha256 = hashlib.sha256(g_raw).hexdigest()
    require_equal(sha256, governed["v7_child_policy_sha256"], "child policy SHA-256")
    words = _parse_child_policy_words(g_raw)
    require_equal(words, governed["v6_settlement_image_id_words"], "child image words")
    if all(word == 0 for word in words):
        raise ReleaseClosureError("V7 child image pin must be nonzero")
    image_id = b"".join(word.to_bytes(4, "little") for word in words).hex()
    require_equal(image_id, governed["v6_settlement_image_id"], "child image ID")
    return {
        "path": V7_CHILD_POLICY_PATH,
        "symbol": V7_CHILD_POLICY_SYMBOL,
        "source_sha256": sha256,
        "image_id": image_id,
        "image_id_words": words,
        "nonzero": True,
        "unchanged_between_c2_and_governance_commit": True,
    }


def commit_file(
    root: Path,
    commit: str,
    path: str,
    *,
    maximum: int = MAX_COMMITTED_FILE_BYTES,
) -> bytes:
    """Read one bounded regular Git blob from a named commit."""

    require_repo_relative(path, "committed path")
    try:
        raw = git_boundary.git_stdout(root, ["show", f"{commit}:{path}"], maximum)
    except git_boundary.MaterializationError as exc:
        raise ReleaseClosureError("required committed source file is unavailable") from exc
    if not raw:
        raise ReleaseClosureError("required committed source file is empty")
    return raw


def head_commit(root: Path) -> str:
    try:
        raw = git_boundary.git_stdout(root, ["rev-parse", "HEAD"], 128)
        return _commit_id(raw.decode("ascii", errors="strict").strip(), "HEAD")
    except (UnicodeDecodeError, git_boundary.MaterializationError) as exc:
        raise ReleaseClosureError("checkout HEAD is unavailable") from exc


def commit_tree(root: Path, commit: str) -> str:
    try:
        raw = git_boundary.git_stdout(root, ["rev-parse", f"{commit}^{{tree}}"], 128)
        value = raw.decode("ascii", errors="strict").strip()
    except (UnicodeDecodeError, git_boundary.MaterializationError) as exc:
        raise ReleaseClosureError("commit tree identity is unavailable") from exc
    if re.fullmatch(r"[0-9a-f]{40,64}", value) is None:
        raise ReleaseClosureError("commit tree identity is malformed")
    return value


def require_repo_relative(value: str, label: str) -> None:
    pure = PurePosixPath(value)
    if (
        not value
        or pure.is_absolute()
        or pure.as_posix() != value
        or value == "."
        or value.startswith("../")
        or "/../" in value
        or any(ord(character) < 32 or ord(character) == 127 for character in value)
    ):
        raise ReleaseClosureError(f"{label} escapes or is noncanonical")


def _literal_parent(root: Path, commit: str, label: str) -> str:
    try:
        raw = git_boundary.git_stdout(root, ["cat-file", "commit", commit], 64 * 1024)
    except git_boundary.MaterializationError as exc:
        raise ReleaseClosureError(f"{label} commit object is unavailable") from exc
    headers, separator, _message = raw.partition(b"\n\n")
    if not separator:
        raise ReleaseClosureError(f"{label} commit object is malformed")
    parents = [line[7:] for line in headers.splitlines() if line.startswith(b"parent ")]
    if len(parents) != 1:
        raise ReleaseClosureError(f"{label} must have exactly one literal parent")
    try:
        return _commit_id(parents[0].decode("ascii", errors="strict"), f"{label} parent")
    except UnicodeDecodeError as exc:
        raise ReleaseClosureError(f"{label} literal parent is not ASCII") from exc


def _require_parent(root: Path, child: str, parent: str, label: str) -> None:
    if _literal_parent(root, child, label) != parent:
        raise ReleaseClosureError(f"{label} literal parent differs from governed chain")


def _commit_id(value: Any, label: str) -> str:
    if type(value) is not str or re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise ReleaseClosureError(f"{label} must be one exact SHA-1 commit ID")
    return value


def _parse_child_policy_words(raw: bytes) -> list[int]:
    matches = list(_CHILD_POLICY_PATTERN.finditer(raw))
    if len(matches) != 1:
        raise ReleaseClosureError("V7 child image policy declaration is not unique")
    try:
        tokens = [token.strip() for token in matches[0].group(1).decode("ascii").split(",")]
    except UnicodeDecodeError as exc:
        raise ReleaseClosureError("V7 child image policy is not ASCII") from exc
    values = [token for token in tokens if token]
    if len(values) != 8 or any(re.fullmatch(r"[0-9]+", token) is None for token in values):
        raise ReleaseClosureError("V7 child image policy must contain eight decimal u32 values")
    words = [int(token, 10) for token in values]
    if any(word > 0xFFFFFFFF for word in words):
        raise ReleaseClosureError("V7 child image policy word exceeds u32")
    return words
