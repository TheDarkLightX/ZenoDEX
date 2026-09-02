"""Tau ADT logical ABI V1 - offline evidence gates.

Two tests, both runnable without a Tau binary:

* ``test_tau_adt_logical_abi_source_contract`` pins the research lock, the two
  ADT specs, the reject-code map against ``AssetTransferRejectCodeV1``
  declaration order, and the ``min()`` definition shape that replays (PR #534
  review F1).
* ``test_tau_adt_logical_abi_replay_receipt_v1`` verifies the committed replay
  receipt produced by ``experiments/tau_adt_abi/render_tau_adt_abi_v2.py``
  against the exact pinned Tau binary: the receipt must be hash-bound to the
  current spec, lock and renderer bytes, every vector-bound program must have
  answered T, every falsification probe F (or FAIL_CLOSED), and the vectors
  must cover every reject code that is reachable from a well-formed state.

* ``test_tau_adt_logical_abi_rust_leg_v1`` checks the committed Rust-leg
  output (the real Rust transition replayed on the identical vector set) agrees
  vector-for-vector with the Python codes recorded in the receipt, which makes
  the three-way statement Python == Rust == Tau direct on these vectors.

Live execution against the pinned binary is ``test_tau_adt_logical_abi_live_v1``
(opt-in; it never counts as evidence by itself). Research-only; authority NONE.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.asset_transfer_types_v1 import (  # noqa: E402
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferRejectCodeV1,
)

LOCK = ROOT / "config" / "tau_lang_adt_research.lock"
ASSET_SPEC = ROOT / "src" / "tau_specs" / "recommended" / "asset_transfer_adt_contract_v1.tau"
JOURNAL_SPEC = ROOT / "src" / "tau_specs" / "recommended" / "lane_transition_journal_adt_contract_v1.tau"
RENDERER = ROOT / "experiments" / "tau_adt_abi" / "render_tau_adt_abi_v2.py"
RECEIPT = ROOT / "tests" / "data" / "tau_adt_logical_abi_replay_receipt_v1.json"
RUST_LEG = ROOT / "tests" / "data" / "tau_adt_logical_abi_rust_leg_v1.json"
RECEIPT_SCHEMA = "zenodex/tau-adt-abi-parity/v3"
RUST_LEG_SCHEMA = "zenodex/tau-adt-abi-rust-leg/v2"
_COMMIT_RE = re.compile(r"[0-9a-f]{40}")
_SHA_RE = re.compile(r"[0-9a-f]{64}")

EXPECTED_SELFTEST = {
    "wrong_expectation_universal": "F",
    "weakened_chain_universal": "F",
    "contract_wrong_code": "F",
    "contract_mutated_effects": "F",
}
EXPECTED_PROBES = {
    "false_whole_adt_statement": "F",
    "asset_always_theorem": "T",
    "journal_always_theorem": "T",
    "fee_cap_min_equivalence": "T",
    "fee_cap_min_strict_falsification": "F",
}
UNREACHABLE_BY_CONSTRUCTION = {"BALANCE_OVERFLOW"}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_lock() -> dict[str, str]:
    rows: dict[str, str] = {}
    for raw in LOCK.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        key, sep, value = line.partition("=")
        assert sep, f"malformed lock row: {raw!r}"
        assert key and key not in rows, f"duplicate/empty lock key: {key!r}"
        rows[key] = value
    return rows


def _executable(path: Path) -> str:
    return "\n".join(
        line for line in path.read_text(encoding="utf-8").splitlines() if not line.lstrip().startswith("#")
    )


def test_tau_adt_logical_abi_source_contract() -> None:
    lock = _read_lock()
    assert set(lock) == {"schema", "repo", "commit", "profile", "purpose", "nonclaim"}
    assert lock["schema"] == "zenodex.tau_lang_adt_research_lock.v1"
    assert lock["repo"] == "https://github.com/IDNI/tau-lang.git"
    assert lock["profile"] == "research"
    assert _COMMIT_RE.fullmatch(lock["commit"]), f"invalid exact Tau commit pin: {lock['commit']!r}"

    asset = _executable(ASSET_SPEC)
    journal = _executable(JOURNAL_SPEC)
    for needle in (
        "type AssetTransferCommandADT1", "type AssetTransferContextADT1",
        "type AssetTransferResultADT1", "type AssetTransferEnvelopeADT1",
        "asset_transfer_result_ok(e.result)", "set charvar off",
    ):
        assert needle in asset, needle
    for needle in (
        "type LaneJournalEdgeADT1", "lane_module_journal_ok(edge.previous)",
        "replay_cursor[n](x):bv[16]", "min({1}:bv[16], replay_cursor[n-1](x)')", "set charvar off",
    ):
        assert needle in journal, needle
    assert "table" not in asset.lower() and "table" not in journal.lower()

    # PR #534 review F1: min() must be applied directly with typed arguments; a
    # return-annotated wrapper is echoed without its annotation and leaves min
    # unresolved (the engine then answers T with an error).
    assert "bounded_fee" not in asset
    assert "fee_within_cap(required, cap) := (min(required:bv[16], cap:bv[16]) = required:bv[16])." in asset

    # Reject-code map pinned to the enum: 0 = accepted, 1..N declaration order,
    # the spec's closed ceiling literal equals N, and N's name is the last member.
    members = list(AssetTransferRejectCodeV1)
    ceiling = re.search(r"\(code <= \{(\d+)\}:bv\[8\]\)", asset)
    assert ceiling and int(ceiling.group(1)) == len(members) == 12
    assert members[-1].name == "POST_STATE_RESOURCE_BOUND_EXCEEDED"
    assert f"#   {len(members)} = POST_STATE_RESOURCE_BOUND_EXCEEDED" in ASSET_SPEC.read_text(encoding="utf-8")
    assert ASSET_TRANSFER_COMMAND_KIND_V1 == "asset_transfer"
    assert "(kind:bv[4] = {1}:bv[4])" in asset  # command_kind token 1 == ASSET_TRANSFER_COMMAND_KIND_V1


def test_tau_adt_logical_abi_replay_receipt_v1() -> None:
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    lock = _read_lock()
    assert receipt["schema"] == RECEIPT_SCHEMA
    assert receipt["ok"] is True
    assert receipt["tau_commit"] == lock["commit"]
    assert lock["commit"][:8] in receipt["tau_version"], receipt["tau_version"]
    assert _SHA_RE.fullmatch(receipt["tau_binary_sha256"])
    assert _SHA_RE.fullmatch(receipt["transcript_sha256"])

    # Hash binding: the receipt is evidence only for these exact bytes.
    assert receipt["spec_path"] == "src/tau_specs/recommended/asset_transfer_adt_contract_v1.tau"
    assert receipt["spec_sha256"] == _sha256(ASSET_SPEC)
    assert receipt["journal_spec_sha256"] == _sha256(JOURNAL_SPEC)
    assert receipt["lock_sha256"] == _sha256(LOCK)
    assert receipt["renderer_sha256"] == _sha256(RENDERER)

    members = list(AssetTransferRejectCodeV1)
    expected_map = {"ACCEPT": 0, **{member.name: index + 1 for index, member in enumerate(members)}}
    assert receipt["code_map"] == expected_map

    for name, verdict in EXPECTED_SELFTEST.items():
        assert receipt["selftest"][name] == verdict, (name, receipt["selftest"][name])
    assert receipt["selftest"]["broken_program"].startswith("FAIL_CLOSED")

    probes = receipt["capability_probes"]
    for name, verdict in EXPECTED_PROBES.items():
        assert probes[name]["expected"] == verdict
        assert probes[name]["verdict"] == verdict, (name, probes[name]["verdict"])
    assert all(entry["verdict"] == entry["expected"] for entry in probes.values())

    vectors = receipt["vectors"]
    assert len(vectors) >= 26
    seen: set[str] = set()
    for row in vectors:
        assert row["parity"] is True, row["vector"]
        assert row["tier"] in {"recompute", "contract"}
        expected_programs = {"universal", "nonvacuity"} if row["tier"] == "recompute" else {"contract"}
        assert set(row["programs"]) == expected_programs, row["vector"]
        for program in row["programs"].values():
            assert program["verdict"] == "T", (row["vector"], program)
            assert _SHA_RE.fullmatch(program["sha256"])
        if row["python_code"] != "ACCEPT":
            assert row["python_noop"] is True and row["python_effects_empty"] is True, row["vector"]
        seen.add(row["python_code"])
    all_codes = {member.name for member in members}
    assert receipt["unreachable_codes"].keys() == UNREACHABLE_BY_CONSTRUCTION
    assert seen == (all_codes - UNREACHABLE_BY_CONSTRUCTION) | {"ACCEPT"}, sorted(all_codes - seen)
    assert set(receipt["recompute_codes"]) <= seen and set(receipt["contract_codes"]) <= seen
    assert {"EFFECT_DELTA_OVERFLOW", "POST_STATE_RESOURCE_BOUND_EXCEEDED"} == set(receipt["contract_codes"])


def test_tau_adt_logical_abi_rust_leg_v1() -> None:
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    leg = json.loads(RUST_LEG.read_text(encoding="utf-8"))
    assert leg["schema"] == RUST_LEG_SCHEMA
    assert leg["ok"] is True
    python_rows = [(row["vector"], row["tier"], row["python_code"]) for row in receipt["vectors"]]
    rust_rows = [(row["vector"], row["tier"], row["rust"]) for row in leg["vectors"]]
    assert rust_rows == python_rows
    assert all(row["parity"] is True and row["rust"] == row["expected"] for row in leg["vectors"])
