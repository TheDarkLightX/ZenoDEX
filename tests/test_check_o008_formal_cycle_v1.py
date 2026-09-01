"""Mutation-killer matrix for the O-008 formal-cycle admission checker (schema v3).

Two fixture layers:

* an in-process ``SubjectSnapshotV1`` built from the worktree bytes of every pinned
  path (Git blob ids computed locally), so the pure core can be exercised against
  named mutations without Git or subprocesses;
* a shared ``git clone`` in a temporary directory for the shell and CLI, where an
  S commit and its packet-only child P are created and then mutated.

Every negative test asserts the exact structured error code. The report's claim
ceiling is asserted constant under every mutation. Authority: NONE.
"""

from __future__ import annotations

import ast
import copy
import json
import shutil
import subprocess
import sys
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest

from tools import build_o008_formal_cycle_v1 as builder
from tools import check_o008_formal_cycle_v1 as cli
from tools import o008_formal_cycle_admission_v1 as core
from tools import o008_formal_cycle_shell_v1 as shell

ROOT = Path(__file__).resolve().parents[1]
S_FAKE = "1" * 40
S_PARENT_FAKE = "2" * 40
S_TREE_FAKE = "3" * 40
P_FAKE = "4" * 40
CREATED = "2026-09-01"
NOT_RUN = {"status": "NOT_RUN"}

CORE_IMPORT_ALLOWLIST = frozenset(
    {
        "__future__",
        "ast",
        "functools",
        "hashlib",
        "json",
        "re",
        "collections.abc",
        "dataclasses",
        "typing",
        "tomllib",
        "unicodedata",
        "yaml",
        "tools.scan_lean_proof_placeholders_v1",
    }
)


# ---------------------------------------------------------------------------
# In-process fixtures
# ---------------------------------------------------------------------------


def _blob(path: str, data: bytes) -> core.SourceBlobV1:
    return core.SourceBlobV1(
        path=path,
        mode=core.GIT_BLOB_MODE_V1,
        git_blob=core.git_blob_oid_v1(data),
        sha256=core.sha256_hex_v1(data),
        size=len(data),
        data=data,
    )


def _with_blob(snapshot: core.SubjectSnapshotV1, path: str, data: bytes | None) -> core.SubjectSnapshotV1:
    blobs = dict(snapshot.blobs)
    if data is None:
        blobs.pop(path, None)
    else:
        blobs[path] = _blob(path, data)
    return replace(snapshot, blobs=blobs)


def _edit(snapshot: core.SubjectSnapshotV1, path: str, old: str, new: str) -> core.SubjectSnapshotV1:
    text = snapshot.blobs[path].data.decode("utf-8")
    assert old in text, f"{old!r} not found in {path}"
    return _with_blob(snapshot, path, text.replace(old, new, 1).encode("utf-8"))


@pytest.fixture(scope="module")
def snapshot() -> core.SubjectSnapshotV1:
    blobs = {
        path: _blob(path, (ROOT / path).read_bytes())
        for path in core.SOURCE_PIN_PATHS_V1
        if (ROOT / path).is_file()
    }
    packets = {
        f"{core.HYGIENE_EVIDENCE_DIR_V1}/{entry.name}": _blob(f"{core.HYGIENE_EVIDENCE_DIR_V1}/{entry.name}", entry.read_bytes())
        for entry in sorted((ROOT / core.HYGIENE_EVIDENCE_DIR_V1).glob("*.json"))
    }
    return core.SubjectSnapshotV1(S_FAKE, S_PARENT_FAKE, S_TREE_FAKE, blobs, packets)


@pytest.fixture(scope="module")
def packet(snapshot: core.SubjectSnapshotV1) -> dict[str, Any]:
    return core.project_packet_v1(snapshot, created_date=CREATED, author_replay_record=NOT_RUN)


def _topology(packet: dict[str, Any], **overrides: Any) -> core.PacketTopologyV1:
    raw = core.canonical_packet_bytes_v1(packet)
    md = core.render_markdown_v1(packet).encode("utf-8")
    fields: dict[str, Any] = {
        "packet_commit": P_FAKE,
        "packet_parents": (S_FAKE,),
        "write_set": tuple(sorted(core.PACKET_WRITE_SET_V1, key=lambda row: row[1])),
        "head_commit": P_FAKE,
        "packet_in_head_history": True,
        "packet_blob_at_p": raw,
        "markdown_blob_at_p": md,
        "packet_blob_at_head": raw,
        "markdown_blob_at_head": md,
        "worktree_packet": raw,
        "worktree_markdown": md,
    }
    fields.update(overrides)
    return core.PacketTopologyV1(**fields)


def _context(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any], **overrides: Any) -> core.AdmissionContextV1:
    pinned = {**snapshot.hygiene_packets, **snapshot.blobs}
    current = core.CurrentSourceStateV1(
        {path: blob.git_blob for path, blob in pinned.items()},
        {path: blob.sha256 for path, blob in pinned.items()},
    )
    executing = core.ExecutingToolsV1(
        {path: snapshot.blobs[path].sha256 for path in core.EXECUTING_TOOL_PATHS_V1}
    )
    fields: dict[str, Any] = {
        "snapshot": snapshot,
        "topology": _topology(packet),
        "current": current,
        "executing": executing,
    }
    fields.update(overrides)
    return core.AdmissionContextV1(**fields)


def _codes(outcome: core.AdmissionOutcomeV1) -> list[str]:
    return [error.code for error in outcome.errors]


def _mutated(packet: dict[str, Any], mutation: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    value = copy.deepcopy(packet)
    mutation(value)
    return value


def _project_code(snapshot: core.SubjectSnapshotV1) -> str:
    with pytest.raises(core.AdmissionRejectV1) as captured:
        core.project_packet_v1(snapshot, created_date=CREATED, author_replay_record=NOT_RUN)
    return captured.value.code


# ---------------------------------------------------------------------------
# Positive path and constant claim ceiling
# ---------------------------------------------------------------------------


def test_projection_of_worktree_subject_is_admitted(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any]) -> None:
    outcome = core.admit_packet_v1(packet, _context(snapshot, packet))
    assert outcome.errors == ()
    assert outcome.current_source_drift == ()
    assert outcome.packet_admitted and outcome.current_applicable
    assert packet["claim_ceiling"] == core.CLAIM_CEILING_V1
    assert packet["source_pins"][0]["path"] == core.PYTHON_REFINEMENT_PATH_V1
    assert len(packet["source_pins"]) == len(core.SOURCE_PIN_ROLES_V1)
    assert packet["lean_evidence"]["theorem_count"] == len(core.THEOREM_INVENTORY_V1)
    assert packet["esso_evidence"]["invariants"] == list(core.ESSO_INVARIANTS_V1)
    assert packet["proof_replay"]["author_record"] == NOT_RUN


def test_canonical_bytes_round_trip(packet: dict[str, Any]) -> None:
    raw = core.canonical_packet_bytes_v1(packet)
    assert core.decode_packet_v1(raw) == packet
    assert core.canonical_packet_bytes_v1(core.decode_packet_v1(raw)) == raw


def test_report_claim_ceiling_is_constant_under_promotion(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any]) -> None:
    promoted = _mutated(packet, lambda v: v["claim_ceiling"].__setitem__("formal_core_complete", True))
    outcome = core.admit_packet_v1(promoted, _context(snapshot, packet))
    report = core.render_report_v1(
        core.ReportInputsV1(P_FAKE, S_FAKE, P_FAKE, outcome, core.ReplayEvaluationV1("NOT_RUN", (), ()), {})
    )
    assert report["claim_ceiling"] == core.CLAIM_CEILING_V1
    assert report["ok"] is False and report["exit_code"] == 1
    assert report["errors"][0]["code"] == "FORMAL_CORE_PROMOTION"


@pytest.mark.parametrize(
    ("mutation", "code"),
    [
        pytest.param(lambda v: v["claim_ceiling"].__setitem__("formal_core_complete", True), "FORMAL_CORE_PROMOTION", id="promote_formal_core"),
        pytest.param(lambda v: v["claim_ceiling"].__setitem__("settlement_authority", "ACTIVE"), "AUTHORITY_PROMOTION", id="promote_settlement_authority"),
        pytest.param(lambda v: v["claim_ceiling"].__setitem__("value_movement_gates_closed", 1), "VALUE_MOVEMENT_PROMOTION", id="promote_value_movement_gate"),
        pytest.param(lambda v: v["claim_ceiling"].__setitem__("o008_status", "CLOSED"), "CLAIM_STATUS_DRIFT", id="promote_o008_status"),
        pytest.param(lambda v: v["claim_ceiling"].__setitem__("formal_core_complete", 0), "FORMAL_CORE_PROMOTION", id="type_confusion_zero_is_not_false"),
        pytest.param(lambda v: v.__setitem__("subject_tree", "0" * 40), "SUBJECT_TREE_DRIFT", id="subject_tree_forged"),
        pytest.param(lambda v: v.__setitem__("packet_commit_parent", "0" * 40), "PACKET_PARENT_DECLARATION_DRIFT", id="packet_parent_declaration"),
        pytest.param(lambda v: v["packet_write_set"].append({"status": "M", "path": core.CHECKER_PATH_V1}), "PACKET_WRITE_SET_DECLARATION_DRIFT", id="write_set_declaration_widened"),
        pytest.param(lambda v: v["source_pins"].pop(3), "SOURCE_PIN_SET_DRIFT", id="drop_pin"),
        pytest.param(lambda v: v["source_pins"][1].__setitem__("role", "python_visible_necessary_checks"), "SOURCE_PIN_ROLE_DRIFT", id="change_role"),
        pytest.param(lambda v: v["source_pins"][0].__setitem__("sha256", "0" * 64), "SOURCE_PIN_SHA256_DRIFT", id="forge_sha256"),
        pytest.param(lambda v: v["source_pins"][0].__setitem__("git_blob", "0" * 40), "SOURCE_PIN_BLOB_DRIFT", id="forge_git_blob"),
        pytest.param(lambda v: v["source_pins"][0].__setitem__("mode", "100755"), "SOURCE_PIN_MODE_DRIFT", id="executable_mode"),
        pytest.param(lambda v: v["source_pins"][0].__setitem__("size", 1), "SOURCE_PIN_SIZE_DRIFT", id="forge_size"),
        pytest.param(lambda v: v["source_pins"][0].__setitem__("path", "../x.py"), "SOURCE_PIN_PATH_UNSAFE", id="path_traversal"),
        pytest.param(lambda v: v["source_pins"][0].__setitem__("path", "/abs.py"), "SOURCE_PIN_PATH_UNSAFE", id="absolute_path"),
        pytest.param(lambda v: v["source_pins"][0].pop("size"), "SOURCE_PIN_SHAPE", id="pin_shape"),
        pytest.param(lambda v: v["nonclaims"].__setitem__(0, "The completed formal cycle completes O-008."), "NONCLAIM_DRIFT", id="contradictory_nonclaim"),
        pytest.param(lambda v: v["nonclaims"].reverse(), "NONCLAIM_DRIFT", id="reorder_nonclaims"),
        pytest.param(lambda v: v["completion_scope"].__setitem__(0, v["completion_scope"][0] + " O-008 complete"), "PROMOTION_TOKEN_PRESENT", id="promotion_token_in_scope"),
        pytest.param(lambda v: v["esso_evidence"].__setitem__("claim_boundary", "Formal   Core  Complete"), "PROMOTION_TOKEN_PRESENT", id="promotion_token_whitespace_folded"),
        pytest.param(lambda v: v["lane_source_data"][0].__setitem__("status", "COMPLETE"), "LANE_STATUS_NOT_IN_VOCABULARY", id="promote_lane_status"),
        pytest.param(lambda v: v["lane_source_data"].pop(), "LANE_MAP_DRIFT", id="drop_lane"),
        pytest.param(lambda v: v["lane_source_data"].reverse(), "LANE_MAP_DRIFT", id="reorder_lanes"),
        pytest.param(lambda v: v["required_sidecar"]["required_checks"].pop(), "SIDECAR_DRIFT", id="drop_sidecar_check"),
        pytest.param(lambda v: v["required_sidecar"].__setitem__("host_only_authority", "VERIFIER"), "SIDECAR_DRIFT", id="promote_sidecar_authority"),
        pytest.param(lambda v: v["required_sidecar"].__setitem__("reserve_interpretation", "CLAIMANT_BEARING"), "SIDECAR_DRIFT", id="reserve_interpretation_drift"),
        pytest.param(lambda v: v["esso_evidence"].__setitem__("fingerprint_role", "MODEL_BINDING"), "PACKET_PROJECTION_DRIFT", id="fingerprint_role_tamper"),
        pytest.param(lambda v: v["esso_evidence"].__setitem__("ir_hash", "sha256:" + "0" * 64), "PACKET_PROJECTION_DRIFT", id="ir_hash_tamper"),
        pytest.param(lambda v: v["esso_evidence"].__setitem__("esso_code_commit", "0" * 40), "PACKET_PROJECTION_DRIFT", id="esso_code_commit_tamper"),
        pytest.param(lambda v: v["lean_evidence"]["theorems"][0].__setitem__("statement_sha256", "0" * 64), "PACKET_PROJECTION_DRIFT", id="statement_hash_tamper"),
        pytest.param(lambda v: v["lean_evidence"]["theorems"].reverse(), "PACKET_PROJECTION_DRIFT", id="reorder_theorem_inventory_in_packet"),
        pytest.param(lambda v: v["v1_information_loss"]["terminal_projection"]["absent_fields"].clear(), "PACKET_PROJECTION_DRIFT", id="absent_fields_cleared"),
        pytest.param(lambda v: v["required_sidecar"].__setitem__("type_name", "globalaccountingallocationcertificatev1"), "SIDECAR_DRIFT", id="sidecar_type_case"),
        pytest.param(lambda v: v["proof_replay"]["commands"].pop(), "REPLAY_COMMANDS_DRIFT", id="replay_commands_tamper"),
        pytest.param(lambda v: v["proof_replay"].__setitem__("author_record", {"status": "EXECUTED", "runs": []}), "REPLAY_RECORD_SHAPE", id="author_record_fake_executed"),
        pytest.param(lambda v: v["proof_replay"].__setitem__("author_record", {"status": "VERIFIED"}), "REPLAY_RECORD_STATUS_INVALID", id="author_record_status_verified"),
        pytest.param(lambda v: v["proof_replay"].__setitem__("admission_semantics", "AUTHOR_RECORD_IS_TRUSTED"), "REPLAY_SEMANTICS_DRIFT", id="admission_semantics_tamper"),
    ],
)
def test_packet_mutations_fail_closed(
    snapshot: core.SubjectSnapshotV1,
    packet: dict[str, Any],
    mutation: Callable[[dict[str, Any]], None],
    code: str,
) -> None:
    outcome = core.admit_packet_v1(_mutated(packet, mutation), _context(snapshot, packet))
    assert code in _codes(outcome), _codes(outcome)
    assert not outcome.packet_admitted


def test_projection_catch_all_names_the_drifted_section(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any]) -> None:
    mutated = _mutated(packet, lambda v: v["lean_evidence"].__setitem__("claim_boundary", "bounded"))
    outcome = core.admit_packet_v1(mutated, _context(snapshot, packet))
    drift = [error for error in outcome.errors if error.code == "PACKET_PROJECTION_DRIFT"]
    assert drift and drift[0].path == "lean_evidence"


# ---------------------------------------------------------------------------
# Raw packet bytes
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("transform", "code"),
    [
        pytest.param(lambda raw: raw.replace(b'"schema":', b'"schema":"forged","schema":', 1), "PACKET_JSON_DUPLICATE_KEY", id="duplicate_key"),
        pytest.param(lambda raw: raw.replace(b'"solver_timeout_ms":10000', b'"solver_timeout_ms":NaN', 1), "PACKET_JSON_FLOAT", id="nan_number"),
        pytest.param(lambda raw: raw.replace(b'"solver_timeout_ms":10000', b'"solver_timeout_ms":10000.0', 1), "PACKET_JSON_FLOAT", id="float_number"),
        pytest.param(lambda raw: json.dumps(json.loads(raw), indent=2).encode(), "PACKET_JSON_NONCANONICAL", id="pretty_printed"),
        pytest.param(lambda raw: raw.replace(b"/v3", b"/v2", 1), "PACKET_SCHEMA_DRIFT", id="old_schema_v2"),
        pytest.param(lambda raw: raw.replace(b'"created_date":"2026-09-01"', b'"created_date":"2026\\u201109-01"', 1), "PACKET_NON_ASCII", id="non_ascii_string"),
        pytest.param(lambda raw: raw.replace(b'{"claim_ceiling"', b'{"authority":"NONE","claim_ceiling"', 1), "PACKET_KEY_SET_DRIFT", id="unknown_top_key"),
        pytest.param(lambda raw: b"[]\n", "PACKET_NOT_OBJECT", id="not_an_object"),
        pytest.param(lambda raw: b"{", "PACKET_JSON_MALFORMED", id="malformed"),
        pytest.param(lambda raw: b"{}" + b" " * core.MAX_PACKET_BYTES_V1, "PACKET_BYTE_CEILING", id="byte_ceiling"),
    ],
)
def test_raw_packet_mutations_fail_closed(packet: dict[str, Any], transform: Callable[[bytes], bytes], code: str) -> None:
    raw = transform(core.canonical_packet_bytes_v1(packet))
    with pytest.raises(core.AdmissionRejectV1) as captured:
        core.decode_packet_v1(raw)
    assert captured.value.code == code


# ---------------------------------------------------------------------------
# Subject (source commit) mutations through the projection
# ---------------------------------------------------------------------------


def _lean_theorem_names(snapshot: core.SubjectSnapshotV1) -> list[str]:
    text = snapshot.blobs[core.LEAN_PROOF_PATH_V1].data.decode("utf-8")
    return [entry.name for entry in core.lean_theorem_inventory_v1(text)]


def test_lean_inventory_matches_closed_constant(snapshot: core.SubjectSnapshotV1) -> None:
    assert _lean_theorem_names(snapshot) == [name for _, name in core.THEOREM_INVENTORY_V1]


def test_rename_theorem_is_inventory_drift(snapshot: core.SubjectSnapshotV1) -> None:
    mutated = _edit(snapshot, core.LEAN_PROOF_PATH_V1, "theorem necessaryRelation_nonvacuous", "theorem necessaryRelation_nonvacuous2")
    assert _project_code(mutated) == "LEAN_THEOREM_INVENTORY_DRIFT"


def test_reorder_theorems_is_inventory_drift(snapshot: core.SubjectSnapshotV1) -> None:
    text = snapshot.blobs[core.LEAN_PROOF_PATH_V1].data.decode("utf-8")
    first, second = (name for _, name in core.THEOREM_INVENTORY_V1[-2:])
    swapped = text.replace(f"theorem {first}", "theorem __swap__").replace(f"theorem {second}", f"theorem {first}").replace("theorem __swap__", f"theorem {second}")
    assert _project_code(_with_blob(snapshot, core.LEAN_PROOF_PATH_V1, swapped.encode())) == "LEAN_THEOREM_INVENTORY_DRIFT"


def test_weakened_statement_changes_statement_hash(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any]) -> None:
    mutated = _edit(
        snapshot,
        core.LEAN_PROOF_PATH_V1,
        "(backed : SameDomainLiabilitiesBacked state) :\n    AggregateLiabilitiesBacked state := by",
        "(backed : SameDomainLiabilitiesBacked state) :\n    ReserveInclusiveBacking state := by",
    )
    inventory = core.lean_theorem_inventory_v1(mutated.blobs[core.LEAN_PROOF_PATH_V1].data.decode("utf-8"))
    original = {t["name"]: t["statement_sha256"] for t in packet["lean_evidence"]["theorems"]}
    changed = {entry.name: entry.statement_sha256 for entry in inventory}
    assert set(original) == set(changed)
    assert [name for name in original if original[name] != changed[name]] == ["sameDomainBacked_implies_aggregateBacked"]
    outcome = core.admit_packet_v1(packet, _context(mutated, packet))
    assert _codes(outcome)[0] == "SOURCE_PIN_BLOB_DRIFT"
    assert "LEAN_GATE_PIN_DRIFT" in _codes(outcome)


@pytest.mark.parametrize(
    ("path", "old", "new", "code"),
    [
        pytest.param(core.LEAN_PROOF_PATH_V1, "end GlobalClaimantCustodyRelationV1", "theorem sneaky : True := by sorry\nend GlobalClaimantCustodyRelationV1", "LEAN_PLACEHOLDER_PRESENT", id="insert_sorry"),
        pytest.param(core.LEAN_PROOF_PATH_V1, "end GlobalClaimantCustodyRelationV1", "axiom bad : False\nend GlobalClaimantCustodyRelationV1", "LEAN_PLACEHOLDER_PRESENT", id="insert_axiom"),
        pytest.param(core.LEAN_PROOF_PATH_V1, "theorem necessaryRelation_nonvacuous", "private theorem necessaryRelation_nonvacuous", "LEAN_PRIVATE_THEOREM_FORBIDDEN", id="private_theorem"),
        pytest.param(core.LEAN_PROOF_PATH_V1, "namespace GlobalClaimantCustodyRelationV1", "namespace GlobalClaimantCustodyRelationV2", "LEAN_NAMESPACE_DRIFT", id="namespace_drift"),
        pytest.param(core.LEAN_ROOT_PATH_V1, core.LEAN_IMPORT_LINE_V1, "import Proofs.ExternalCustodyDisabledLaneV1", "LEAN_IMPORT_ROOT_MISSING", id="drop_import_root"),
        pytest.param(core.LEAN_TOOLCHAIN_PATH_V1, "v4.27.0", "v4.28.0", "LEAN_TOOLCHAIN_DRIFT", id="bump_toolchain"),
        pytest.param(core.LEAN_GATE_PATH_V1, '    "necessaryRelation_nonvacuous",', '    "necessaryRelation_nonvacuous",\n    "extra_theorem",', "LEAN_GATE_THEOREMS_DRIFT", id="stale_lean_gate_theorems"),
        pytest.param(core.LEAN_GATE_PATH_V1, "ALLOWED_STANDARD_AXIOMS = frozenset({", 'ALLOWED_STANDARD_AXIOMS = frozenset({"sorryAx", ', "LEAN_GATE_AXIOMS_DRIFT", id="stale_lean_gate_axioms"),
        pytest.param(core.ESSO_MODEL_PATH_V1, '  - id: "inv_accept_requires_exact_bound_evidence"', '  - id: "inv_accept_requires_bound_evidence"', "ESSO_INVARIANTS_DRIFT", id="rename_esso_invariant"),
        pytest.param(core.ESSO_MODEL_PATH_V1, '  model_id: "global_claimant_custody_certificate_v1"', '  model_id: "global_claimant_custody_certificate_v2"', "ESSO_MODEL_ID_DRIFT", id="esso_model_id_drift"),
        pytest.param(core.ESSO_GATE_PATH_V1, 'RECORDED_ESSO_CODE_HASH = "', 'RECORDED_ESSO_CODE_HASH = "0', "ESSO_CODE_COMMIT_DRIFT", id="esso_code_commit_drift"),
        pytest.param(core.ESSO_GATE_PATH_V1, 'RECORDED_IR_HASH = "sha256:', 'RECORDED_IR_HASH = "md5:', "ESSO_IR_HASH_DRIFT", id="esso_ir_hash_malformed"),
        pytest.param(core.ESSO_GATE_PATH_V1, 'id="drain_cross_domain_custody_substitution"', 'id="drain_cross_domain_custody_substitution_x"', "ESSO_GATE_MUTANTS_DRIFT", id="drop_drain_mutant"),
        pytest.param(core.PYTHON_TYPES_PATH_V1, "class TerminalObligationV1:\n    obligation_id: str\n", "class TerminalObligationV1:\n    obligation_id: str\n    liability_domain: str\n", "TERMINAL_FORBIDDEN_FIELD_PRESENT", id="insert_liability_domain_python"),
        pytest.param(core.PYTHON_TYPES_PATH_V1, "class TerminalObligationV1:\n    obligation_id: str\n    lane_id: LaneIdV1\n", "class TerminalObligationV1:\n    lane_id: LaneIdV1\n    obligation_id: str\n", "PYTHON_TERMINAL_FIELD_ORDER_DRIFT", id="reorder_python_fields"),
        pytest.param(core.PYTHON_TYPES_PATH_V1, '            "obligation_id": self.obligation_id,\n            "lane_id": self.lane_id,\n            "claimant": self.claimant,', '            "obligation_id": self.obligation_id,\n            "lane_id": self.lane_id,\n            "claimant_id": self.claimant,', "PYTHON_TERMINAL_CANONICAL_KEYS_DRIFT", id="python_canonical_key_drift"),
        pytest.param(core.PYTHON_TYPES_PATH_V1, "class OutboxStateV1:\n    effect_id: str\n", "class OutboxStateV1:\n    effect_id: str\n    amount_atoms: int\n", "OUTBOX_FORBIDDEN_FIELD_PRESENT", id="add_outbox_amount_python"),
        pytest.param(core.RUST_STATE_PATH_V1, "pub struct TerminalObligationV1 {\n    pub obligation_id: String,\n", "pub struct TerminalObligationV1 {\n    pub obligation_id: String,\n    pub liability_domain: String,\n", "TERMINAL_FORBIDDEN_FIELD_PRESENT", id="insert_liability_domain_rust"),
        pytest.param(core.RUST_STATE_PATH_V1, "    pub claimant: String,\n    pub asset: String,\n    pub amount_atoms: u128,\n    pub status: TerminalObligationStatusV1,", "    pub asset: String,\n    pub claimant: String,\n    pub amount_atoms: u128,\n    pub status: TerminalObligationStatusV1,", "RUST_TERMINAL_FIELD_ORDER_DRIFT", id="reorder_rust_fields"),
        pytest.param(core.RUST_STATE_PATH_V1, "#[serde(deny_unknown_fields)]\npub struct TerminalObligationV1", "pub struct TerminalObligationV1", "RUST_DENY_UNKNOWN_FIELDS_MISSING", id="drop_deny_unknown_fields"),
    ],
)
def test_subject_mutations_reject_projection(snapshot: core.SubjectSnapshotV1, path: str, old: str, new: str, code: str) -> None:
    assert _project_code(_edit(snapshot, path, old, new)) == code


def _append(snapshot: core.SubjectSnapshotV1, path: str, tail: str) -> core.SubjectSnapshotV1:
    return _with_blob(snapshot, path, snapshot.blobs[path].data + tail.encode("utf-8"))


TERMINAL_ATTRS = "#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]\n#[serde(deny_unknown_fields)]\npub struct TerminalObligationV1 {"
LIVE_MACRO = (
    "\nmacro_rules! define_live_terminal_obligation_v1 {\n    ($name:ident) => {\n"
    "        #[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]\n        pub struct $name {\n"
    "            pub obligation_id: String,\n            pub lane_id: LaneIdV1,\n            pub claimant: String,\n"
    "            pub asset: String,\n            pub amount_atoms: u128,\n            pub status: TerminalObligationStatusV1,\n"
    "        }\n    };\n}\ndefine_live_terminal_obligation_v1!(TerminalObligationV1);\n"
)


@pytest.mark.parametrize(
    ("path", "old", "new", "tail", "code"),
    [
        # Codex C1 P1: cfg(any()) decoy plus a macro-generated live struct without deny_unknown_fields.
        pytest.param(core.RUST_STATE_PATH_V1, TERMINAL_ATTRS, "#[cfg(any())]\n" + TERMINAL_ATTRS, LIVE_MACRO, "RUST_CFG_FORBIDDEN", id="cfg_decoy_macro_live"),
        pytest.param(core.RUST_STATE_PATH_V1, "", "", LIVE_MACRO, "RUST_MACRO_DEFINES_ITEM", id="item_defining_macro"),
        pytest.param(core.RUST_STATE_PATH_V1, "", "", "\nmacro_rules! passthrough { ($($t:tt)*) => { $($t)* }; }\npassthrough!(pub struct TerminalObligationV2 { pub extra: String });\n", "RUST_MACRO_DEFINES_ITEM", id="passthrough_macro_item_tokens"),
        pytest.param(core.RUST_STATE_PATH_V1, "", "", "\ndefine_live!(TerminalObligationV1);\n", "RUST_FOREIGN_ITEM_MACRO", id="foreign_item_macro"),
        pytest.param(core.RUST_STATE_PATH_V1, "            deserialize_bounded_vec_v1::<D, $row, $maximum>(deserializer, $label)", "            let _ = vec![0u8];\n            deserialize_bounded_vec_v1::<D, $row, $maximum>(deserializer, $label)", "", "RUST_MACRO_NESTED_INVOCATION", id="nested_invocation_in_macro"),
        pytest.param(core.RUST_STATE_PATH_V1, "", "", "\ninclude!(\"extra.rs\");\n", "RUST_INCLUDE_FORBIDDEN", id="include_macro"),
        pytest.param(core.RUST_STATE_PATH_V1, "", "", "\n#[path = \"other.rs\"]\nmod other;\n", "RUST_PATH_ATTRIBUTE_FORBIDDEN", id="path_attribute"),
        pytest.param(core.RUST_STATE_PATH_V1, "", "", "\nmod dup { pub struct TerminalObligationV1 { pub extra: String } }\n", "RUST_STRUCT_AMBIGUOUS", id="duplicate_rust_struct"),
        pytest.param(core.RUST_STATE_PATH_V1, "pub struct TerminalObligationV1 {", "mod inner { pub struct TerminalObligationV1 {", "\n}\n", "RUST_STRUCT_NOT_TOP_LEVEL", id="nested_module_struct"),
        pytest.param(core.RUST_STATE_PATH_V1, "    pub obligation_id: String,\n    pub lane_id: LaneIdV1,", "    pub obligation_id: String,\n    #[serde(rename = \"liability_domain\")]\n    pub lane_id: LaneIdV1,", "", "RUST_FIELD_ATTRIBUTE_FORBIDDEN", id="serde_field_rename"),
        pytest.param(core.RUST_STATE_PATH_V1, "#[serde(deny_unknown_fields)]\npub struct TerminalObligationV1 {", "#[serde(deny_unknown_fields)]\n#[serde(rename_all = \"camelCase\")]\npub struct TerminalObligationV1 {", "", "RUST_STRUCT_ATTRIBUTES_DRIFT", id="serde_struct_rename_all"),
        pytest.param(core.RUST_STATE_PATH_V1, "#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]\n#[serde(deny_unknown_fields)]\npub struct TerminalObligationV1 {", "#[derive(Clone, Debug, Eq, PartialEq, Serialize)]\n#[serde(deny_unknown_fields)]\npub struct TerminalObligationV1 {", "", "RUST_STRUCT_ATTRIBUTES_DRIFT", id="derive_without_deserialize"),
        pytest.param(core.RUST_STATE_PATH_V1, "use serde::{Deserialize, Deserializer, Serialize};", "use serde::{Deserializer, Serialize};\nuse crate::shadow::Deserialize;", "", "RUST_SERDE_IMPORT_DRIFT", id="foreign_deserialize_import"),
        pytest.param(core.RUST_STATE_PATH_V1, "    pub terminal_obligations: Vec<TerminalObligationV1>,", "    pub terminal_obligations: Vec<TerminalObligationV2>,", "", "RUST_STATE_FIELD_TYPE_DRIFT", id="state_container_type"),
        pytest.param(core.RUST_LIB_PATH_V1, "mod state;", "#[cfg(any())]\nmod state;", "", "RUST_CFG_FORBIDDEN", id="lib_cfg_mod_state"),
        pytest.param(core.RUST_LIB_PATH_V1, "mod state;", "mod state2;", "", "RUST_STATE_MODULE_DECLARATION_DRIFT", id="lib_drops_mod_state"),
        pytest.param(core.RUST_LIB_PATH_V1, "mod state;", "mod state { pub struct TerminalObligationV1 { pub extra: String } }", "", "RUST_STATE_MODULE_DECLARATION_DRIFT", id="lib_inline_mod_state"),
        pytest.param(core.RUST_MANIFEST_PATH_V1, "", "", "\n[lib]\npath = \"src/other.rs\"\n", "CARGO_LIB_TARGET_OVERRIDE", id="cargo_lib_path"),
        pytest.param(core.RUST_MANIFEST_PATH_V1, "", "", "\n[[test]]\nname = \"v1_projection_gate\"\npath = \"tests/other.rs\"\n", "CARGO_TARGET_OVERRIDE_FORBIDDEN", id="cargo_test_target"),
        pytest.param(core.RUST_MANIFEST_PATH_V1, "", "", "\n[patch.crates-io]\nserde = { path = \"../serde\" }\n", "CARGO_TARGET_OVERRIDE_FORBIDDEN", id="cargo_patch"),
        pytest.param(core.RUST_MANIFEST_PATH_V1, 'serde = { version = "=1.0.228", features = ["derive"] }', 'serde = { path = "../serde", features = ["derive"] }', "", "CARGO_DEPENDENCY_SOURCE_OVERRIDE", id="cargo_serde_path"),
        pytest.param(core.RUST_MANIFEST_PATH_V1, 'name = "zenodex-global-settlement-abi-v1"', 'name = "zenodex-global-settlement-abi-v2"', "", "CARGO_PACKAGE_NAME_DRIFT", id="cargo_package_name"),
        pytest.param(core.RUST_MANIFEST_PATH_V1, "", "", "\n[workspace]\nmembers = []\n", "CARGO_TARGET_OVERRIDE_FORBIDDEN", id="cargo_workspace"),
        pytest.param(core.RUST_MANIFEST_PATH_V1, 'name = "zenodex-global-settlement-abi-v1"', 'name = "zenodex-global-settlement-abi-v1"\nautotests = false', "", "CARGO_TARGET_OVERRIDE_FORBIDDEN", id="cargo_autotests"),
        pytest.param(core.RUST_MANIFEST_PATH_V1, 'serde = { version = "=1.0.228", features = ["derive"] }', 'serde = { version = "1", features = ["derive"] }', "", "CARGO_DEPENDENCY_VERSION_NOT_EXACT", id="cargo_loose_serde_version"),
        # Opus C1' P1-A: a plain-fn deserialize_with hook replacing the local bounded-vec macro.
        pytest.param(core.RUST_STATE_PATH_V1, "bounded_state_vec_deserializer_v1!(\n    deserialize_terminal_obligations_v1,\n    TerminalObligationV1,\n    MAX_GLOBAL_TERMINAL_ROWS_V1,\n    \"global state terminal obligations\"\n);", "fn deserialize_terminal_obligations_v1<'de, D>(deserializer: D) -> Result<Vec<TerminalObligationV1>, D::Error>\nwhere\n    D: Deserializer<'de>,\n{\n    let rows: Vec<serde_json::Value> = Vec::deserialize(deserializer)?;\n    Ok(rows.into_iter().filter_map(|row| serde_json::from_value(row).ok()).collect())\n}", "", "RUST_CONTAINER_DESERIALIZER_DRIFT", id="terminal_deserialize_with_plain_fn"),
        pytest.param(core.RUST_STATE_PATH_V1, "bounded_state_vec_deserializer_v1!(\n    deserialize_outbox_v1,\n    OutboxStateV1,\n    MAX_GLOBAL_OUTBOX_ROWS_V1,\n    \"global state outbox\"\n);", "fn deserialize_outbox_v1<'de, D>(deserializer: D) -> Result<Vec<OutboxStateV1>, D::Error>\nwhere\n    D: Deserializer<'de>,\n{\n    Vec::deserialize(deserializer)\n}", "", "RUST_CONTAINER_DESERIALIZER_DRIFT", id="outbox_deserialize_with_plain_fn"),
        pytest.param(core.RUST_STATE_PATH_V1, '    #[serde(deserialize_with = "deserialize_terminal_obligations_v1")]\n    pub terminal_obligations:', '    #[serde(deserialize_with = "deserialize_terminal_obligations_v1")]\n    #[serde(default)]\n    pub terminal_obligations:', "", "RUST_CONTAINER_ATTRIBUTE_DRIFT", id="container_extra_attribute"),
        pytest.param(core.RUST_STATE_PATH_V1, '    #[serde(deserialize_with = "deserialize_terminal_obligations_v1")]\n    pub terminal_obligations:', '    #[serde(deserialize_with = "deserialize_lenient_terminal_v1")]\n    pub terminal_obligations:', "", "RUST_CONTAINER_ATTRIBUTE_DRIFT", id="container_deserializer_renamed"),
        pytest.param(core.RUST_STATE_PATH_V1, "            deserialize_bounded_vec_v1::<D, $row, $maximum>(deserializer, $label)", "            deserialize_bounded_vec_v1::<D, $row, { $maximum * 2 }>(deserializer, $label)", "", "RUST_BOUNDED_VEC_MACRO_DRIFT", id="bounded_vec_macro_body_drift"),
        pytest.param(core.RUST_STATE_PATH_V1, "", "", "\ncrate::late_items!();\nmacro_rules! late_items { () => {}; }\n", "RUST_FOREIGN_ITEM_MACRO", id="path_qualified_item_macro"),
        pytest.param(core.RUST_STATE_PATH_V1, "", "", "\nlate_items!();\nmacro_rules! late_items { () => {}; }\n", "RUST_FOREIGN_ITEM_MACRO", id="macro_defined_after_invocation"),
        pytest.param(core.RUST_STATE_PATH_V1, "", "", "\nextern crate hex as serde;\n", "RUST_EXTERN_CRATE_FORBIDDEN", id="extern_crate_alias"),
        pytest.param(core.RUST_STATE_PATH_V1, "use serde::{Deserialize, Deserializer, Serialize};", "use serde::{Deserializer, Serialize}; const _X: u8 = 0; use crate::shadow::Deserialize as _E;", "", "RUST_SERDE_IMPORT_DRIFT", id="same_line_foreign_import"),
        pytest.param(core.RUST_STATE_PATH_V1, "use crate::bounded_vec::deserialize_bounded_vec_v1;", "use crate::lenient_vec::deserialize_bounded_vec_v1;", "", "RUST_BOUNDED_VEC_IMPORT_DRIFT", id="bounded_vec_import_redirected"),
        pytest.param(core.RUST_BOUNDED_VEC_PATH_V1, "", "", "\nimpl<'de> Deserialize<'de> for u8 {}\n", "RUST_BOUNDED_VEC_DRIFT", id="bounded_vec_manual_deserialize"),
        pytest.param(core.RUST_BOUNDED_VEC_PATH_V1, "                Some(value) => values.push(value),", "                Some(value) => values.push(value.clone()),", "", "RUST_BOUNDED_VEC_DRIFT", id="bounded_vec_visitor_drift"),
        pytest.param(core.RUST_BOUNDED_VEC_PATH_V1, "#[cfg(test)]\nmod tests {", "#[cfg(feature = \"lenient\")]\nmod tests {", "", "RUST_CFG_FORBIDDEN", id="bounded_vec_non_test_cfg"),
        pytest.param(core.RUST_GATE_PATH_V1, "", "", "\n#[test]\nfn extra_vacuous() {\n    assert!(true);\n}\n", "RUST_GATE_CONTENT_DRIFT", id="rust_gate_extra_test"),
        pytest.param(core.RUST_GATE_PATH_V1, '    "custody_principal",\n', '', "", "RUST_GATE_CONTENT_DRIFT", id="rust_gate_forbidden_shrunk"),
        pytest.param(core.RUST_GATE_PATH_V1, '    "obligation_id",\n    "lane_id",\n', '    "lane_id",\n    "obligation_id",\n', "", "RUST_GATE_CONTENT_DRIFT", id="rust_gate_fields_reordered"),
        pytest.param(core.RUST_GATE_PATH_V1, 'include_str!("../../../tests/data/global_claimant_backing_guard_v1_golden.json")', 'include_str!("../../../tests/data/other.json")', "", "RUST_INCLUDE_FORBIDDEN", id="rust_gate_other_include"),
    ],
)
def test_rust_lexical_closure_rejects_decoys(
    snapshot: core.SubjectSnapshotV1, path: str, old: str, new: str, tail: str, code: str
) -> None:
    mutated = _edit(snapshot, path, old, new) if old else snapshot
    if tail:
        mutated = _append(mutated, path, tail)
    assert _project_code(mutated) == code


def test_vacuous_gate_files_are_rejected(snapshot: core.SubjectSnapshotV1) -> None:
    vacuous_rust = "".join(f"#[test]\nfn t{i}() {{\n    assert!(true);\n}}\n" for i in range(core.RUST_GATE_EXPECTED_PASSED_V1))
    assert _project_code(_with_blob(snapshot, core.RUST_GATE_PATH_V1, vacuous_rust.encode())) == "RUST_GATE_CONTENT_DRIFT"
    vacuous_python = "".join(f"def test_t{i}() -> None:\n    assert True\n\n\n" for i in range(core.PYTHON_GATE_EXPECTED_PASSED_V1))
    assert _project_code(_with_blob(snapshot, core.PYTHON_GATE_PATH_V1, vacuous_python.encode())) == "PYTHON_GATE_CONTENT_DRIFT"


def test_cargo_config_present_at_subject_is_rejected(snapshot: core.SubjectSnapshotV1) -> None:
    mutated = replace(snapshot, forbidden_paths_present=(core.CARGO_CONFIG_FORBIDDEN_PATHS_V1[0],))
    assert _project_code(mutated) == "CARGO_CONFIG_PRESENT"


def test_cargo_config_in_worktree_blocks_applicability(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any]) -> None:
    context = _context(snapshot, packet)
    current = replace(context.current, forbidden_paths_present=(core.CARGO_CONFIG_FORBIDDEN_PATHS_V1[-1],))
    outcome = core.admit_packet_v1(packet, replace(context, current=current))
    assert outcome.packet_admitted and not outcome.current_applicable
    assert outcome.current_source_drift == (core.CARGO_CONFIG_FORBIDDEN_PATHS_V1[-1],)


def test_arrow_in_a_field_type_does_not_swallow_fields() -> None:
    body = "pub a: u8,\n    pub cb: fn(u8) -> u8,\n    pub c: u8"
    fields = core._rust_fields(body, core.RUST_STATE_PATH_V1, allow_attributes=False)
    assert fields == (("a", "u8"), ("cb", "fn(u8) -> u8"), ("c", "u8"))


@pytest.mark.parametrize(
    ("stdout", "expected"),
    [
        pytest.param(b"cargo 1.87.0 (99624be96 2025-05-06)\n", "1.87.0", id="cargo_banner"),
        pytest.param(b"rustc 1.87.0\n", None, id="rustc_banner"),
        pytest.param(b"", None, id="empty"),
    ],
)
def test_cargo_version_parser(stdout: bytes, expected: str | None) -> None:
    assert core.parse_cargo_version_v1(stdout) == expected


@pytest.mark.parametrize(
    ("old", "new", "tail", "code"),
    [
        pytest.param("", "", "\nTerminalObligationV1 = OutboxStateV1\n", "PYTHON_CLASS_REBOUND", id="rebound_class_name"),
        pytest.param("", "", "\nfrom typing import Any as TerminalObligationV1\n", "PYTHON_CLASS_REBOUND", id="import_rebinds_class_name"),
        pytest.param("class TerminalObligationV1:", "class TerminalObligationV1(object):", "", "PYTHON_CLASS_BASES_FORBIDDEN", id="base_class"),
        pytest.param("@dataclass(frozen=True, slots=True, order=True)\nclass TerminalObligationV1:", "@functools.total_ordering\n@dataclass(frozen=True, slots=True, order=True)\nclass TerminalObligationV1:", "", "PYTHON_CLASS_DECORATORS_DRIFT", id="extra_decorator"),
        pytest.param("@dataclass(frozen=True, slots=True, order=True)\nclass TerminalObligationV1:", "@dataclass(frozen=FROZEN, slots=True, order=True)\nclass TerminalObligationV1:", "", "PYTHON_CLASS_DECORATORS_DRIFT", id="non_literal_dataclass_keyword"),
        pytest.param('    def to_canonical(self) -> dict[str, object]:\n        return {\n            "obligation_id": self.obligation_id,', '    def to_canonical(self) -> dict[str, object]:\n        if self.amount_atoms:\n            return {"obligation_id": self.obligation_id}\n        return {\n            "obligation_id": self.obligation_id,', "", "PYTHON_CANONICAL_SHAPE", id="canonical_early_return"),
        pytest.param("    terminal_obligations: tuple[TerminalObligationV1, ...] = ()", "    terminal_obligations: tuple[object, ...] = ()", "", "PYTHON_STATE_FIELD_TYPE_DRIFT", id="state_container_annotation"),
        pytest.param("", "", "\nclass _Other:\n    pass\n\n\nGlobalEconomicStateV1 = _Other\n", "PYTHON_CLASS_REBOUND", id="container_class_rebound"),
        pytest.param("", "", "\nexec('TerminalObligation' + 'V1 = int')\n", "PYTHON_DYNAMIC_BINDING_FORBIDDEN", id="exec_rebinding"),
        pytest.param("", "", "\nglobals()['TerminalObligationV1'] = int\n", "PYTHON_DYNAMIC_BINDING_FORBIDDEN", id="globals_subscript_rebinding"),
        pytest.param("", "", "\nimport sys as _sys\n_sys.modules[__name__] = None\n", "PYTHON_DYNAMIC_BINDING_FORBIDDEN", id="sys_modules_rebinding"),
    ],
)
def test_python_closure_rejects_decoys(snapshot: core.SubjectSnapshotV1, old: str, new: str, tail: str, code: str) -> None:
    mutated = _edit(snapshot, core.PYTHON_TYPES_PATH_V1, old, new) if old else snapshot
    if tail:
        mutated = _append(mutated, core.PYTHON_TYPES_PATH_V1, tail)
    assert _project_code(mutated) == code


def test_deleted_lean_file_is_missing_pin(snapshot: core.SubjectSnapshotV1) -> None:
    assert _project_code(_with_blob(snapshot, core.LEAN_PROOF_PATH_V1, None)) == "SOURCE_PIN_MISSING_IN_SUBJECT"


def test_stale_lean_gate_pin_is_drift(snapshot: core.SubjectSnapshotV1) -> None:
    gate = snapshot.blobs[core.LEAN_GATE_PATH_V1].data.decode("utf-8")
    lean_sha = snapshot.blobs[core.LEAN_PROOF_PATH_V1].sha256
    assert lean_sha in gate
    mutated = _with_blob(snapshot, core.LEAN_GATE_PATH_V1, gate.replace(lean_sha, "0" * 64).encode())
    assert _project_code(mutated) == "LEAN_GATE_PIN_DRIFT"


def test_rust_brace_inside_string_is_ignored(snapshot: core.SubjectSnapshotV1) -> None:
    attributes = "#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]\n#[serde(deny_unknown_fields)]\npub struct TerminalObligationV1 {"
    noise = 'const BRACE_STR: &str = "{"; const BRACE_CHAR: char = \'{\'; const RAW: &str = r#"{"#; /* { /* { */ */ // {\n'
    mutated = _edit(snapshot, core.RUST_STATE_PATH_V1, attributes, noise + attributes)
    shape = core.rust_struct_shape_v1(mutated.blobs[core.RUST_STATE_PATH_V1].data, core.TERMINAL_CLASS_NAME_V1, core.RUST_STATE_PATH_V1)
    assert shape.fields == core.TERMINAL_FIELDS_RUST_V1
    assert shape.deny_unknown_fields is True


def test_rust_lifetime_tick_is_not_a_char_literal() -> None:
    stripped = core.strip_rust_noncode_v1("fn f<'a>(x: &'a str) -> &'a str { x } // done\nstruct S { a: u8 }")
    assert "struct S { a: u8 }" in stripped and "fn f<'a>" in stripped


def _with_packet(snapshot: core.SubjectSnapshotV1, path: str, data: bytes | None) -> core.SubjectSnapshotV1:
    packets = dict(snapshot.hygiene_packets)
    if data is None:
        packets.pop(path, None)
    else:
        packets[path] = _blob(path, data)
    return replace(snapshot, hygiene_packets=packets)


def _selected_packet(packet: dict[str, Any], path: str) -> str:
    return next(str(row["packet_path"]) for row in packet["hygiene_selection"] if row["path"] == path)


def test_hygiene_selection_covers_every_required_path_from_committed_packets(
    snapshot: core.SubjectSnapshotV1, packet: dict[str, Any]
) -> None:
    rows = packet["hygiene_selection"]
    assert [row["path"] for row in rows] == list(core.THV1_REQUIRED_PIN_PATHS_V1)
    for row in rows:
        blob = snapshot.hygiene_packets[row["packet_path"]]
        assert row["packet_sha256"] == blob.sha256 and row["packet_git_blob"] == blob.git_blob
        assert row["pin_sha256"] == snapshot.blobs[row["path"]].sha256
        assert core.PACKET_JSON_PATH_V1 not in blob.data.decode("utf-8")


def test_hygiene_selection_selected_packet_pinning_the_packet_is_circular(
    snapshot: core.SubjectSnapshotV1, packet: dict[str, Any]
) -> None:
    chosen = _selected_packet(packet, core.CHECKER_PATH_V1)
    thv1 = json.loads(snapshot.hygiene_packets[chosen].data)
    thv1["source_pins"].append({"path": core.PACKET_JSON_PATH_V1, "sha256": "0" * 64})
    assert _project_code(_with_packet(snapshot, chosen, json.dumps(thv1).encode())) == "THV1_PINS_PACKET_CIRCULAR"


def test_hygiene_selection_requires_a_matching_packet(snapshot: core.SubjectSnapshotV1) -> None:
    mutated = snapshot
    for path, blob in snapshot.hygiene_packets.items():
        thv1 = json.loads(blob.data)
        for key in ("source_pins", "test_pins"):
            for pin in thv1.get(key, ()):
                if pin["path"] == core.CHECKER_PATH_V1:
                    pin["sha256"] = "0" * 64
        mutated = _with_packet(mutated, path, json.dumps(thv1).encode())
    assert _project_code(mutated) == "THV1_PIN_DRIFT"


def test_hygiene_selection_skips_a_stale_newer_packet(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any]) -> None:
    newest = f"{core.HYGIENE_EVIDENCE_DIR_V1}/THV1-99999999-zzz-stale.json"
    stale = {
        "schema": core.HYGIENE_SCHEMA_V1,
        "evidence_id": "THV1-99999999-zzz-stale",
        "source_pins": [{"path": core.CHECKER_PATH_V1, "sha256": "0" * 64}],
        "test_pins": [],
    }
    projected = core.project_packet_v1(
        _with_packet(snapshot, newest, json.dumps(stale).encode()), created_date=CREATED, author_replay_record=NOT_RUN
    )
    assert _selected_packet(projected, core.CHECKER_PATH_V1) == _selected_packet(packet, core.CHECKER_PATH_V1)
    matching = dict(stale, source_pins=[{"path": core.CHECKER_PATH_V1, "sha256": snapshot.blobs[core.CHECKER_PATH_V1].sha256}])
    projected = core.project_packet_v1(
        _with_packet(snapshot, newest, json.dumps(matching).encode()), created_date=CREATED, author_replay_record=NOT_RUN
    )
    assert _selected_packet(projected, core.CHECKER_PATH_V1) == newest


@pytest.mark.parametrize(
    ("mutation", "code"),
    [
        pytest.param(lambda t: t.__setitem__("evidence_id", "THV1-other"), "THV1_SHAPE", id="evidence_id_mismatch"),
        pytest.param(lambda t: t.__setitem__("schema", "zenodex/test-hygiene-evidence/v2"), "THV1_SHAPE", id="schema_drift"),
        pytest.param(lambda t: t.__setitem__("source_pins", "none"), "THV1_SHAPE", id="pins_not_a_list"),
    ],
)
def test_hygiene_packet_shape_is_closed(
    snapshot: core.SubjectSnapshotV1, packet: dict[str, Any], mutation: Callable[[dict[str, Any]], None], code: str
) -> None:
    chosen = _selected_packet(packet, core.CHECKER_PATH_V1)
    thv1 = json.loads(snapshot.hygiene_packets[chosen].data)
    mutation(thv1)
    assert _project_code(_with_packet(snapshot, chosen, json.dumps(thv1).encode())) == code


def test_applicability_paths_include_selected_packets(packet: dict[str, Any]) -> None:
    paths = core.applicability_paths_v1(packet)
    assert paths[: len(core.SOURCE_PIN_PATHS_V1)] == core.SOURCE_PIN_PATHS_V1
    assert set(paths[len(core.SOURCE_PIN_PATHS_V1):]) == {row["packet_path"] for row in packet["hygiene_selection"]}


def test_created_date_is_validated(snapshot: core.SubjectSnapshotV1) -> None:
    with pytest.raises(core.AdmissionRejectV1) as captured:
        core.project_packet_v1(snapshot, created_date="today", author_replay_record=NOT_RUN)
    assert captured.value.code == "CREATED_DATE_INVALID"


# ---------------------------------------------------------------------------
# Topology, current state, executing tools
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("overrides", "code"),
    [
        pytest.param({"packet_parents": (S_PARENT_FAKE,)}, "PACKET_PARENT_NOT_SUBJECT", id="wrong_parent"),
        pytest.param({"packet_parents": (S_FAKE, S_PARENT_FAKE)}, "PACKET_PARENT_NOT_SUBJECT", id="merge_packet"),
        pytest.param({"write_set": tuple(sorted(core.PACKET_WRITE_SET_V1 + (("M", core.CHECKER_PATH_V1),), key=lambda r: r[1]))}, "PACKET_ENVELOPE_DRIFT", id="envelope_extra_path"),
        pytest.param({"write_set": (("M", core.PACKET_JSON_PATH_V1),)}, "PACKET_ENVELOPE_DRIFT", id="envelope_missing_markdown"),
        pytest.param({"packet_in_head_history": False}, "PACKET_NOT_IN_HEAD_HISTORY", id="packet_not_in_history"),
        pytest.param({"markdown_blob_at_p": b"# edited\n"}, "MARKDOWN_PROJECTION_DRIFT", id="hand_edited_markdown"),
        pytest.param({"packet_blob_at_head": b"{}\n"}, "CURRENT_PACKET_DRIFT", id="head_packet_drift"),
        pytest.param({"worktree_packet": None}, "WORKTREE_PACKET_DRIFT", id="worktree_packet_missing_or_symlink"),
        pytest.param({"worktree_markdown": b"# edited\n"}, "WORKTREE_PACKET_DRIFT", id="worktree_markdown_edit"),
    ],
)
def test_topology_mutations_fail_closed(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any], overrides: dict[str, Any], code: str) -> None:
    outcome = core.admit_packet_v1(packet, _context(snapshot, packet, topology=_topology(packet, **overrides)))
    assert code in _codes(outcome), _codes(outcome)


def test_head_source_drift_keeps_admission_but_blocks_applicability(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any]) -> None:
    context = _context(snapshot, packet)
    head = dict(context.current.head_blob_ids)
    head[core.LEAN_PROOF_PATH_V1] = "0" * 40
    outcome = core.admit_packet_v1(packet, replace(context, current=core.CurrentSourceStateV1(head, context.current.worktree_sha256)))
    assert outcome.errors == () and outcome.packet_admitted
    assert outcome.current_source_drift == (core.LEAN_PROOF_PATH_V1,)
    assert not outcome.current_applicable
    report = core.render_report_v1(core.ReportInputsV1(P_FAKE, S_FAKE, P_FAKE, outcome, core.ReplayEvaluationV1("NOT_RUN", (), ()), {}))
    assert report["ok"] is False and report["packet_admitted"] is True and report["exit_code"] == 1


def test_worktree_source_drift_blocks_applicability(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any]) -> None:
    context = _context(snapshot, packet)
    worktree = dict(context.current.worktree_sha256)
    worktree[core.ESSO_MODEL_PATH_V1] = None
    outcome = core.admit_packet_v1(packet, replace(context, current=core.CurrentSourceStateV1(context.current.head_blob_ids, worktree)))
    assert outcome.current_source_drift == (core.ESSO_MODEL_PATH_V1,)


@pytest.mark.parametrize(
    ("path", "code"),
    [
        pytest.param(core.CHECKER_PATH_V1, "EXECUTING_CHECKER_DRIFT", id="checker_blob_ne_subject"),
        pytest.param(core.CORE_PATH_V1, "EXECUTING_CORE_DRIFT", id="core_blob_ne_subject"),
        pytest.param(core.SHELL_PATH_V1, "EXECUTING_SHELL_DRIFT", id="shell_blob_ne_subject"),
        pytest.param(core.SCANNER_PATH_V1, "EXECUTING_SCANNER_DRIFT", id="scanner_blob_ne_subject"),
    ],
)
def test_executing_tool_drift_fails_closed(snapshot: core.SubjectSnapshotV1, packet: dict[str, Any], path: str, code: str) -> None:
    context = _context(snapshot, packet)
    hashes = dict(context.executing.sha256_by_path)
    hashes[path] = "0" * 64
    outcome = core.admit_packet_v1(packet, replace(context, executing=core.ExecutingToolsV1(hashes)))
    assert code in _codes(outcome)


# ---------------------------------------------------------------------------
# Proof replay evaluation (pure)
# ---------------------------------------------------------------------------


def _cargo_summary(passed: int) -> bytes:
    return (
        f"running {passed} tests\ntest result: ok. {passed} passed; 0 failed; 0 ignored; 0 measured;"
        " 0 filtered out; finished in 0.01s\n"
    ).encode()


def _passing_observations(packet: dict[str, Any]) -> dict[str, core.ReplayObservationV1]:
    esso = packet["esso_evidence"]
    namespace = ".".join(core.LEAN_NAMESPACE_V1)
    axioms = "\n".join(
        f"'{namespace}.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        for _, name in core.THEOREM_INVENTORY_V1
    )
    verify = {
        "ok": True,
        "determinism": True,
        "fingerprints": [esso["fingerprint"], esso["fingerprint"]],
        "queries": {query: {"final_result": "unsat"} for query in core.ESSO_QUERIES_V1},
        "report": {
            "verdict": "VERIFIED",
            "solvers_agreed": True,
            "failed_queries": 0,
            "inconclusive_queries": 0,
            "total_queries": len(core.ESSO_QUERIES_V1),
            "passed_queries": len(core.ESSO_QUERIES_V1),
            "tool_versions": {
                "esso_code_hash": esso["esso_code_commit"],
                "solvers": {"z3": "4.15.4", "cvc5": "This is cvc5 version 1.1.2"},
            },
        },
    }
    outputs = {
        "lean_version": b"Lean (version 4.27.0, x86_64-unknown-linux-gnu, commit abc, Release)\n",
        "lean_direct_check": b"",
        "lean_axioms_probe": axioms.encode(),
        "lean_binding_gate": f"...\n{core.LEAN_GATE_EXPECTED_PASSED_V1} passed in 3.00s\n".encode(),
        "esso_validate": json.dumps({"ok": True, "ir_hash": esso["ir_hash"]}).encode(),
        "esso_verify_multi": json.dumps(verify).encode(),
        "esso_gate": f"{core.ESSO_GATE_EXPECTED_PASSED_V1} passed in 17.00s\n".encode(),
        "prior_restage_gate": f"{core.PRIOR_ESSO_GATE_EXPECTED_PASSED_V1} passed in 1.00s\n".encode(),
        "python_version": b"3.12.3\n",
        "python_projection_gate": f"{core.PYTHON_GATE_EXPECTED_PASSED_V1} passed in 0.30s\n".encode(),
        "rust_projection_gate": _cargo_summary(core.RUST_GATE_EXPECTED_PASSED_V1),
        "rust_version": b"cargo 1.87.0 (99624be96 2025-05-06)\n",
        "rust_refinement_gate": _cargo_summary(core.RUST_REFINEMENT_GATE_EXPECTED_PASSED_V1),
        "python_golden_gate": f"{core.PYTHON_GOLDEN_GATE_EXPECTED_PASSED_V1} passed in 1.00s\n".encode(),
        "rust_golden_gate": _cargo_summary(core.RUST_GOLDEN_GATE_EXPECTED_PASSED_V1),
    }
    return {
        command_id: core.ReplayObservationV1(command_id, 0, stdout, b"", False, "ab" * 32 if command_id == "lean_axioms_probe" else None)
        for command_id, stdout in outputs.items()
    }


def test_no_observations_is_not_run(packet: dict[str, Any]) -> None:
    evaluation = core.evaluate_proof_replay_v1(packet, [])
    assert evaluation.status == "NOT_RUN" and evaluation.errors == () and evaluation.runs == ()


def test_passing_observations_are_executed_pass(packet: dict[str, Any]) -> None:
    evaluation = core.evaluate_proof_replay_v1(packet, list(_passing_observations(packet).values()))
    assert evaluation.status == "EXECUTED_PASS", evaluation.errors
    assert [run["command_id"] for run in evaluation.runs] == list(core.REPLAY_COMMAND_IDS_V1)
    assert core.compare_author_record_v1(packet, evaluation) == ()


@pytest.mark.parametrize(
    ("command_id", "patch", "code"),
    [
        pytest.param("lean_direct_check", lambda o: replace(o, exit_code=1), "REPLAY_EXIT_CODE", id="nonzero_exit"),
        pytest.param("lean_direct_check", lambda o: replace(o, timed_out=True), "REPLAY_EXIT_CODE", id="timed_out"),
        pytest.param("lean_direct_check", lambda o: replace(o, stdout=b"warning: x\n"), "REPLAY_LEAN_OUTPUT_NONEMPTY", id="lean_output_nonempty"),
        pytest.param("lean_version", lambda o: replace(o, stdout=b"Lean (version 4.28.0, ...)\n"), "REPLAY_LEAN_VERSION_DRIFT", id="lean_version_drift"),
        pytest.param("lean_axioms_probe", lambda o: replace(o, stdout=o.stdout.replace(b"Quot.sound", b"sorryAx")), "REPLAY_AXIOM_DRIFT", id="sorry_axiom"),
        pytest.param("lean_axioms_probe", lambda o: replace(o, stdout=b"\n".join(o.stdout.splitlines()[1:])), "REPLAY_AXIOM_DRIFT", id="missing_theorem_probe"),
        pytest.param("lean_binding_gate", lambda o: replace(o, stdout=b"5 passed in 1s\n"), "REPLAY_PASSED_COUNT_DRIFT", id="binding_gate_count"),
        pytest.param("esso_gate", lambda o: replace(o, stdout=b"17 passed, 1 failed in 1s\n"), "REPLAY_PYTEST_SUMMARY_UNPARSEABLE", id="esso_gate_failed_line"),
        pytest.param("esso_validate", lambda o: replace(o, stdout=json.dumps({"ok": True, "ir_hash": "sha256:" + "0" * 64}).encode()), "REPLAY_ESSO_IR_HASH_DRIFT", id="esso_ir_hash_drift"),
        pytest.param("esso_verify_multi", lambda o: replace(o, stdout=o.stdout.replace(b"VERIFIED", b"FAILED")), "REPLAY_ESSO_VERDICT", id="esso_verdict"),
        pytest.param("esso_verify_multi", lambda o: replace(o, stdout=o.stdout.replace(b'"fingerprints": ["', b'"fingerprints": ["0', 1)), "REPLAY_FINGERPRINT_NONDETERMINISTIC", id="esso_fingerprint_nondeterministic"),
        pytest.param("esso_verify_multi", lambda o: replace(o, stdout=o.stdout.replace(b"4.15.4", b"4.15.5")), "REPLAY_SOLVER_VERSION_DRIFT", id="esso_solver_version"),
        pytest.param("esso_verify_multi", lambda o: replace(o, stdout=b"not json"), "REPLAY_ESSO_OUTPUT_UNPARSEABLE", id="esso_not_json"),
    ],
)
def test_replay_observation_mutations_are_executed_fail(
    packet: dict[str, Any], command_id: str, patch: Callable[[core.ReplayObservationV1], core.ReplayObservationV1], code: str
) -> None:
    observations = _passing_observations(packet)
    observations[command_id] = patch(observations[command_id])
    evaluation = core.evaluate_proof_replay_v1(packet, list(observations.values()))
    assert evaluation.status == "EXECUTED_FAIL"
    assert code in [error.code for error in evaluation.errors]


def test_missing_replay_command_is_executed_fail(packet: dict[str, Any]) -> None:
    observations = _passing_observations(packet)
    observations.pop("esso_verify_multi")
    evaluation = core.evaluate_proof_replay_v1(packet, list(observations.values()))
    assert evaluation.status == "EXECUTED_FAIL"
    assert ("REPLAY_COMMAND_MISSING", "esso_verify_multi") in [(e.code, e.path) for e in evaluation.errors]


def test_author_record_drift_is_reported(packet: dict[str, Any]) -> None:
    evaluation = core.evaluate_proof_replay_v1(packet, list(_passing_observations(packet).values()))
    recorded = copy.deepcopy(packet)
    runs = [dict(run) for run in evaluation.runs]
    runs[0]["comparable"] = {"lean_version": "4.26.0"}
    recorded["proof_replay"]["author_record"] = {"status": "EXECUTED", "runs": runs, "toolchain": {}}
    drift = core.compare_author_record_v1(recorded, evaluation)
    assert [(e.code, e.path) for e in drift] == [
        ("REPLAY_AUTHOR_RECORD_DRIFT", "lean_version"),
        ("REPLAY_AUTHOR_TOOLCHAIN_DRIFT", "proof_replay.author_record.toolchain"),
    ]


def _executed_record(packet: dict[str, Any]) -> dict[str, Any]:
    evaluation = core.evaluate_proof_replay_v1(packet, list(_passing_observations(packet).values()))
    assert evaluation.status == "EXECUTED_PASS", evaluation.errors
    runs = [{k: run[k] for k in ("command_id", "exit_code", "comparable")} for run in evaluation.runs]
    return {"status": "EXECUTED", "runs": copy.deepcopy(runs), "toolchain": dict(evaluation.toolchain)}


def test_executed_record_round_trips_through_validation(packet: dict[str, Any]) -> None:
    record = _executed_record(packet)
    assert core.validate_author_replay_record_v1(record, packet["esso_evidence"]) == record
    assert record["toolchain"] == {
        "esso_code_hash": core.ESSO_CODE_COMMIT_V1,
        "lean": core.LEAN_VERSION_V1,
        "python": "3.12.3",
        "rust": "1.87.0",
        "solvers": dict(core.ESSO_SOLVERS_V1),
    }


def _run(record: dict[str, Any], command_id: str) -> dict[str, Any]:
    return next(run for run in record["runs"] if run["command_id"] == command_id)


@pytest.mark.parametrize(
    ("mutation", "code"),
    [
        pytest.param(lambda r: r["toolchain"].__setitem__("lean", "999.0"), "REPLAY_RECORD_TOOLCHAIN_DRIFT", id="toolchain_lean_forged"),
        pytest.param(lambda r: r["toolchain"].__setitem__("solvers", {"z3": "9.9.9", "cvc5": "9.9.9"}), "REPLAY_RECORD_TOOLCHAIN_DRIFT", id="toolchain_solvers_forged"),
        pytest.param(lambda r: r["toolchain"].__setitem__("esso_code_hash", "0" * 40), "REPLAY_RECORD_TOOLCHAIN_DRIFT", id="toolchain_code_hash_forged"),
        pytest.param(lambda r: r["toolchain"].__setitem__("python", "3.12.3-authority"), "REPLAY_RECORD_TOOLCHAIN_DRIFT", id="toolchain_python_malformed"),
        pytest.param(lambda r: r["toolchain"].__setitem__("python", "3.11.0"), "REPLAY_RECORD_TOOLCHAIN_DRIFT", id="toolchain_python_differs_from_run"),
        pytest.param(lambda r: r["toolchain"].__setitem__("rust", "9.9.9"), "REPLAY_RECORD_TOOLCHAIN_DRIFT", id="toolchain_rust_differs_from_run"),
        pytest.param(lambda r: r["toolchain"].pop("rust"), "REPLAY_RECORD_SHAPE", id="toolchain_rust_missing"),
        pytest.param(lambda r: r["toolchain"].__setitem__("authority", "GRANTED"), "REPLAY_RECORD_SHAPE", id="toolchain_authority_key"),
        pytest.param(lambda r: r["toolchain"]["solvers"].__setitem__("authority", "GRANTED"), "REPLAY_RECORD_TOOLCHAIN_DRIFT", id="toolchain_nested_authority_key"),
        pytest.param(lambda r: r.__setitem__("formal_core_complete", True), "REPLAY_RECORD_SHAPE", id="record_extra_key"),
        pytest.param(lambda r: _run(r, "esso_gate")["comparable"].__setitem__("passed", 17), "REPLAY_RECORD_COMPARABLE_DRIFT", id="comparable_passed_tampered"),
        pytest.param(lambda r: _run(r, "esso_gate")["comparable"].__setitem__("authority", "GRANTED"), "REPLAY_RECORD_COMPARABLE_SHAPE", id="comparable_unknown_key"),
        pytest.param(lambda r: _run(r, "esso_validate")["comparable"].__setitem__("ir_hash", "sha256:" + "0" * 64), "REPLAY_RECORD_COMPARABLE_DRIFT", id="comparable_ir_hash_forged"),
        pytest.param(lambda r: _run(r, "esso_verify_multi")["comparable"].__setitem__("verdict", "FAILED"), "REPLAY_RECORD_COMPARABLE_DRIFT", id="comparable_verdict_forged"),
        pytest.param(lambda r: _run(r, "lean_direct_check")["comparable"].__setitem__("stdout_sha256", "1" * 64), "REPLAY_RECORD_COMPARABLE_DRIFT", id="comparable_nonempty_direct_check"),
        pytest.param(lambda r: _run(r, "lean_axioms_probe")["comparable"].__setitem__("theorems_probed", 1), "REPLAY_RECORD_COMPARABLE_DRIFT", id="comparable_theorems_probed"),
        pytest.param(lambda r: _run(r, "lean_axioms_probe")["comparable"].__setitem__("probe_sha256", "/tmp/probe"), "REPLAY_RECORD_COMPARABLE_DRIFT", id="comparable_machine_path"),
        pytest.param(lambda r: _run(r, "rust_projection_gate")["comparable"].__setitem__("passed", True), "REPLAY_RECORD_COMPARABLE_DRIFT", id="comparable_bool_is_not_int"),
        pytest.param(lambda r: r["runs"].pop(), "REPLAY_RECORD_SHAPE", id="missing_last_run"),
    ],
)
def test_forged_author_records_are_rejected_statically(
    packet: dict[str, Any], mutation: Callable[[dict[str, Any]], None], code: str
) -> None:
    record = _executed_record(packet)
    mutation(record)
    with pytest.raises(core.AdmissionRejectV1) as captured:
        core.validate_author_replay_record_v1(record, packet["esso_evidence"])
    assert captured.value.code == code


def test_forged_probe_hash_is_refuted_by_fresh_replay(packet: dict[str, Any]) -> None:
    record = _executed_record(packet)
    _run(record, "lean_axioms_probe")["comparable"]["probe_sha256"] = "cd" * 32
    assert core.validate_author_replay_record_v1(record, packet["esso_evidence"]) == record
    recorded = copy.deepcopy(packet)
    recorded["proof_replay"]["author_record"] = record
    evaluation = core.evaluate_proof_replay_v1(packet, list(_passing_observations(packet).values()))
    assert [(e.code, e.path) for e in core.compare_author_record_v1(recorded, evaluation)] == [
        ("REPLAY_AUTHOR_RECORD_DRIFT", "lean_axioms_probe")
    ]


@pytest.mark.parametrize(
    ("stdout", "expected"),
    [
        pytest.param(b"running 5 tests\ntest result: ok. 5 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n", 5, id="one_green_line"),
        pytest.param(b"test result: FAILED. 4 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n", None, id="failed_line"),
        pytest.param(b"test result: ok. 5 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n", None, id="two_summary_lines"),
        pytest.param(b"5 passed in 0.1s\n", None, id="pytest_summary_is_not_cargo"),
    ],
)
def test_cargo_summary_parser_accepts_exactly_one_green_line(stdout: bytes, expected: int | None) -> None:
    assert core.parse_cargo_test_summary_v1(stdout) == expected


@pytest.mark.parametrize(
    ("stdout", "expected"),
    [
        pytest.param(b"3.12.3\n", "3.12.3", id="semver"),
        pytest.param(b"Python 3.12.3\n", None, id="banner"),
        pytest.param(b"3.12\n", None, id="two_components"),
        pytest.param(b"", None, id="empty"),
    ],
)
def test_python_version_parser_requires_one_semver_line(stdout: bytes, expected: str | None) -> None:
    assert core.parse_python_version_v1(stdout) == expected


@pytest.mark.parametrize(
    ("command_id", "patch", "code"),
    [
        pytest.param("rust_projection_gate", lambda o: replace(o, stdout=b"test result: FAILED. 4 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n"), "REPLAY_CARGO_SUMMARY_UNPARSEABLE", id="cargo_failed_line"),
        pytest.param("rust_projection_gate", lambda o: replace(o, stdout=b"test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n"), "REPLAY_PASSED_COUNT_DRIFT", id="cargo_count_drift"),
        pytest.param("python_projection_gate", lambda o: replace(o, stdout=b"7 passed in 0.1s\n"), "REPLAY_PASSED_COUNT_DRIFT", id="python_gate_count_drift"),
        pytest.param("python_version", lambda o: replace(o, stdout=b"Python 3.12.3\n"), "REPLAY_PYTHON_VERSION_UNPARSEABLE", id="python_version_banner"),
        pytest.param("rust_version", lambda o: replace(o, stdout=b"rustc 1.87.0\n"), "REPLAY_RUST_VERSION_UNPARSEABLE", id="rust_version_banner"),
        pytest.param("rust_refinement_gate", lambda o: replace(o, stdout=_cargo_summary(40)), "REPLAY_PASSED_COUNT_DRIFT", id="rust_refinement_count"),
        pytest.param("rust_golden_gate", lambda o: replace(o, stdout=_cargo_summary(2)), "REPLAY_PASSED_COUNT_DRIFT", id="rust_golden_count"),
        pytest.param("esso_verify_multi", lambda o: replace(o, stdout=o.stdout.replace(b'"total_queries": 3', b'"total_queries": 0').replace(b'"passed_queries": 3', b'"passed_queries": 0')), "REPLAY_ESSO_QUERY_COUNT_DRIFT", id="esso_zero_queries"),
        pytest.param("esso_verify_multi", lambda o: replace(o, stdout=o.stdout.replace(b'"inductive_drain_claim"', b'"inductive_other_claim"')), "REPLAY_ESSO_QUERY_SET_DRIFT", id="esso_query_set_drift"),
    ],
)
def test_new_gate_observation_mutations_are_executed_fail(
    packet: dict[str, Any], command_id: str, patch: Callable[[core.ReplayObservationV1], core.ReplayObservationV1], code: str
) -> None:
    observations = _passing_observations(packet)
    observations[command_id] = patch(observations[command_id])
    evaluation = core.evaluate_proof_replay_v1(packet, list(observations.values()))
    assert evaluation.status == "EXECUTED_FAIL"
    assert code in [error.code for error in evaluation.errors]


@pytest.mark.parametrize(
    ("record", "code"),
    [
        pytest.param({"status": "EXECUTED", "runs": []}, "REPLAY_RECORD_SHAPE", id="executed_without_toolchain"),
        pytest.param({"status": "EXECUTED", "runs": [], "toolchain": {}}, "REPLAY_RECORD_SHAPE", id="executed_without_runs"),
        pytest.param({"status": "NOT_RUN", "runs": []}, "REPLAY_RECORD_SHAPE", id="not_run_with_runs"),
        pytest.param({"status": "PASS"}, "REPLAY_RECORD_STATUS_INVALID", id="status_pass"),
        pytest.param({"status": "EXECUTED", "runs": [{"command_id": "lean_version", "exit_code": 1, "comparable": {}}], "toolchain": {}}, "REPLAY_RECORD_EXIT_NONZERO", id="nonzero_exit"),
        pytest.param({"status": "EXECUTED", "runs": [{"command_id": "lean_version", "exit_code": 0, "comparable": "/home/user/repo"}], "toolchain": {}}, "REPLAY_RECORD_COMPARABLE_SHAPE", id="comparable_not_an_object"),
        pytest.param({"status": "EXECUTED", "runs": [{"command_id": "lean_version", "exit_code": 0, "comparable": {"lean_version": "/usr/bin/lean"}}], "toolchain": {}}, "REPLAY_RECORD_COMPARABLE_DRIFT", id="comparable_machine_path_value"),
        pytest.param({"status": "EXECUTED", "runs": [{"command_id": "cargo_build", "exit_code": 0, "comparable": {}}], "toolchain": {}}, "REPLAY_RECORD_SHAPE", id="unknown_command_id"),
        pytest.param({"status": "EXECUTED", "runs": [{"command_id": "lean_version", "exit_code": 0, "comparable": {}, "stdout_sha256": "0" * 64}], "toolchain": {}}, "REPLAY_RECORD_SHAPE", id="nondeterministic_run_keys"),
        pytest.param("EXECUTED", "REPLAY_RECORD_SHAPE", id="not_an_object"),
    ],
)
def test_author_record_validation(packet: dict[str, Any], record: object, code: str) -> None:
    with pytest.raises(core.AdmissionRejectV1) as captured:
        core.validate_author_replay_record_v1(record, packet["esso_evidence"])
    assert captured.value.code == code


# ---------------------------------------------------------------------------
# Purity and structure of the core itself
# ---------------------------------------------------------------------------


def test_core_module_imports_only_the_allowlist() -> None:
    module = ast.parse((ROOT / core.CORE_PATH_V1).read_text(encoding="utf-8"))
    imported: set[str] = set()
    for node in module.body:
        if isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            imported.add(node.module or "")
    assert imported <= CORE_IMPORT_ALLOWLIST, imported - CORE_IMPORT_ALLOWLIST
    forbidden = {"subprocess", "os", "sys", "pathlib", "time", "random", "socket"}
    assert not (imported & forbidden)


def test_closed_constants_are_internally_consistent() -> None:
    assert len(core.EXPECTED_LANES_V1) == 12
    assert tuple(lane for lane, _, _ in core.LANE_SOURCE_DATA_V1) == core.EXPECTED_LANES_V1
    assert all(status in core.LANE_STATUS_VOCABULARY_V1 for _, status, _ in core.LANE_SOURCE_DATA_V1)
    assert "COMPLETE" not in core.LANE_STATUS_VOCABULARY_V1
    assert len(core.SIDECAR_CHECKS_V1) == 10 and len(core.SIDECAR_FIELDS_V1) == 9
    assert len(core.NONCLAIMS_V1) == 10
    assert set(core.RUST_GATE_TESTS_V1) >= {"records_and_containers_reject_seeded_unknown_keys"}
    assert core.RUST_GATE_EXPECTED_PASSED_V1 == len(core.RUST_GATE_TESTS_V1)
    assert core.PYTHON_GATE_EXPECTED_PASSED_V1 >= len(core.PYTHON_GATE_TESTS_V1)
    assert set(core.LEAN_DEFINITIONAL_THEOREMS_V1) <= {name for _, name in core.THEOREM_INVENTORY_V1}
    assert len(set(core.SOURCE_PIN_PATHS_V1)) == len(core.SOURCE_PIN_PATHS_V1)
    assert set(core.EXECUTING_TOOL_PATHS_V1) <= set(core.SOURCE_PIN_PATHS_V1)
    assert set(core.THV1_REQUIRED_PIN_PATHS_V1) <= set(core.SOURCE_PIN_PATHS_V1)
    assert core.PACKET_JSON_PATH_V1 not in core.SOURCE_PIN_PATHS_V1
    assert core.CLAIM_CEILING_V1["formal_core_complete"] is False
    assert all(core.CLAIM_CEILING_V1[field] == "NONE" for field in core.AUTHORITY_FIELDS_V1)
    assert core.REPLAY_COMMAND_IDS_V1 == tuple(c.command_id for c in core.REPLAY_COMMANDS_V1)
    assert core.RESERVE_INTERPRETATION_V1 == "NAMED_UNENCUMBERED_NO_CLAIMANT"


def test_git_blob_oid_matches_git() -> None:
    expected = subprocess.run(
        ["git", "hash-object", "--stdin"], input=b"hello\n", capture_output=True, check=True, timeout=30
    ).stdout.decode().strip()
    assert core.git_blob_oid_v1(b"hello\n") == expected


# ---------------------------------------------------------------------------
# Shell and CLI against a temporary two-commit chain
# ---------------------------------------------------------------------------

PY = sys.executable


def _git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(root), *args], check=True, capture_output=True, text=True, timeout=60
    ).stdout.strip()


def _commit_all(root: Path, message: str) -> str:
    _git(root, "add", "--all")
    _git(root, "-c", "user.name=o008 test", "-c", "user.email=o008@example.invalid", "commit", "-q", "--allow-empty", "-m", message)
    return _git(root, "rev-parse", "HEAD")


def _build_packet(root: Path, subject: str) -> None:
    args = builder._parse_args(["--root", str(root), "--subject-commit", subject, "--created-date", CREATED])
    status = builder.build_v1(args)
    assert status["ok"] is True, status


@pytest.fixture(scope="module")
def chain(tmp_path_factory: pytest.TempPathFactory) -> Path:
    """A shared clone with S (this worktree's pinned sources) and its packet-only child P."""

    destination = tmp_path_factory.mktemp("o008-chain") / "repo"
    subprocess.run(
        ["git", "clone", "--quiet", "--shared", "--no-checkout", str(ROOT), str(destination)],
        check=True, capture_output=True, timeout=120,
    )
    _git(destination, "checkout", "--quiet", "--detach", "HEAD")
    packets = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / core.HYGIENE_EVIDENCE_DIR_V1).glob("*.json"))
    for path in (*core.SOURCE_PIN_PATHS_V1, *packets, "tools/__init__.py"):
        source = ROOT / path
        if source.is_file():
            target = destination / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
    subject = _commit_all(destination, "temporary O-008 source commit S")
    _build_packet(destination, subject)
    _commit_all(destination, "temporary O-008 packet commit P")
    return destination.resolve()


def _run_cli(root: Path, *extra: str) -> tuple[int, dict[str, Any]]:
    process = subprocess.run(
        [PY, str(root / core.CHECKER_PATH_V1), "--root", str(root), *extra],
        capture_output=True, text=True, timeout=300, check=False,
    )
    assert process.stderr == "", process.stderr
    return process.returncode, json.loads(process.stdout)


def test_cli_admits_generated_chain(chain: Path) -> None:
    code, report = _run_cli(chain)
    assert code == 0, report["errors"]
    assert report["ok"] is True and report["packet_admitted"] is True and report["current_applicable"] is True
    assert report["proof_replay"]["status"] == "NOT_RUN"
    assert report["subject_commit"] == _git(chain, "rev-parse", "HEAD^")
    assert report["packet_commit"] == _git(chain, "rev-parse", "HEAD")
    assert report["claim_ceiling"] == core.CLAIM_CEILING_V1
    assert _run_cli(chain, "--packet-commit", report["packet_commit"])[0] == 0
    assert _run_cli(chain, "--packet-commit", "0" * 40)[1]["errors"][0]["code"] == "PACKET_COMMIT_MISMATCH"


def test_cli_optimized_interpreter_gives_identical_report(chain: Path) -> None:
    baseline = _run_cli(chain)[1]
    optimized = subprocess.run(
        [PY, "-O", str(chain / core.CHECKER_PATH_V1), "--root", str(chain)],
        capture_output=True, text=True, timeout=300, check=False,
    )
    assert json.loads(optimized.stdout) == baseline


def test_builder_check_round_trip(chain: Path) -> None:
    subject = _git(chain, "rev-parse", "HEAD^")
    args = builder._parse_args(["--root", str(chain), "--subject-commit", subject, "--created-date", CREATED, "--check"])
    assert builder.build_v1(args) == {"ok": True, "mode": "check", "drift": [], "subject_commit": subject}


def test_builder_refuses_to_write_on_rejected_subject(chain: Path, tmp_path: Path) -> None:
    # The parent of the commit that introduced the admission core lacks a pinned path.
    introduced = _git(chain, "rev-list", "--reverse", "HEAD", "--", core.CORE_PATH_V1).splitlines()[0]
    args = builder._parse_args(
        ["--root", str(chain), "--subject-commit", _git(chain, "rev-parse", f"{introduced}^"), "--created-date", CREATED,
         "--output-json", str(tmp_path / "out.json"), "--output-md", str(tmp_path / "out.md")]
    )
    with pytest.raises(core.AdmissionRejectV1) as captured:
        builder.build_v1(args)
    assert captured.value.code == "SOURCE_PIN_MISSING_IN_SUBJECT"
    assert not (tmp_path / "out.json").exists() and not (tmp_path / "out.md").exists()


def test_cli_worktree_packet_edit_is_drift(chain: Path) -> None:
    target = chain / core.PACKET_JSON_PATH_V1
    original = target.read_bytes()
    target.write_bytes(original + b"\n")
    try:
        code, report = _run_cli(chain)
    finally:
        target.write_bytes(original)
    assert code == 1 and report["errors"][0]["code"] == "WORKTREE_PACKET_DRIFT"


def test_cli_replay_refused_on_source_drift(chain: Path) -> None:
    target = chain / core.ESSO_MODEL_PATH_V1
    original = target.read_bytes()
    target.write_bytes(original + b"\n# drift\n")
    try:
        code, report = _run_cli(chain, "--replay")
    finally:
        target.write_bytes(original)
    assert code == 1
    assert report["proof_replay"]["status"] == "REFUSED"
    assert "REPLAY_REFUSED_WORKTREE_DRIFT" in [e["code"] for e in report["errors"]]
    assert report["current_source_drift"] == [core.ESSO_MODEL_PATH_V1]


def test_cli_wrong_parent_and_envelope_drift(chain: Path, tmp_path_factory: pytest.TempPathFactory) -> None:
    variant = tmp_path_factory.mktemp("o008-variant") / "repo"
    subprocess.run(["git", "clone", "--quiet", "--shared", str(chain), str(variant)], check=True, capture_output=True, timeout=120)
    packet_commit = _git(variant, "rev-parse", "HEAD")
    subject = _git(variant, "rev-parse", "HEAD^")
    # Envelope drift: a new child of S that changes the packet and another file.
    _git(variant, "checkout", "--quiet", "--detach", subject)
    _build_packet(variant, subject)
    (variant / "README.md").write_text("drift\n", encoding="utf-8")
    _commit_all(variant, "packet plus extra path")
    code, report = _run_cli(variant)
    assert code == 1 and "PACKET_ENVELOPE_DRIFT" in [e["code"] for e in report["errors"]]
    # Wrong parent: the packet blob for S committed on top of a different child of S.
    _git(variant, "checkout", "--quiet", "--detach", subject)
    (variant / "README.md").write_text("another child of S\n", encoding="utf-8")
    _commit_all(variant, "sibling of P")
    _git(variant, "checkout", "--quiet", packet_commit, "--", core.PACKET_JSON_PATH_V1, core.PACKET_MD_PATH_V1)
    _commit_all(variant, "packet on the wrong parent")
    code, report = _run_cli(variant)
    assert code == 1 and "PACKET_PARENT_NOT_SUBJECT" in [e["code"] for e in report["errors"]]


def test_cli_source_commit_after_p_is_fail_closed(chain: Path, tmp_path_factory: pytest.TempPathFactory) -> None:
    """Stage 3 of the lifecycle, exercised on a synthetic chain: a pinned source changes after P."""

    variant = tmp_path_factory.mktemp("o008-after-p") / "repo"
    subprocess.run(["git", "clone", "--quiet", "--shared", str(chain), str(variant)], check=True, capture_output=True, timeout=120)
    target = variant / core.PYTHON_GATE_PATH_V1
    target.write_text(target.read_text(encoding="utf-8") + "\n# drift after P\n", encoding="utf-8")
    _commit_all(variant, "source commit after P")
    code, report = _run_cli(variant)
    assert code == 1 and report["ok"] is False
    assert report["packet_admitted"] is True and report["current_applicable"] is False
    assert report["current_source_drift"] == [core.PYTHON_GATE_PATH_V1]
    assert report["head_commit"] != report["packet_commit"]


def test_builder_check_mode_mismatch_is_named(chain: Path) -> None:
    """A committed EXECUTED record checked without --replay is a mode mismatch, not byte drift."""

    subject = _git(chain, "rev-parse", "HEAD^")
    packet = json.loads((chain / core.PACKET_JSON_PATH_V1).read_bytes())
    executed = copy.deepcopy(packet)
    executed["proof_replay"]["author_record"] = {"status": "EXECUTED", "runs": [], "toolchain": {}}
    original = (chain / core.PACKET_JSON_PATH_V1).read_bytes()
    (chain / core.PACKET_JSON_PATH_V1).write_bytes(core.canonical_packet_bytes_v1(executed))
    try:
        args = builder._parse_args(["--root", str(chain), "--subject-commit", subject, "--created-date", CREATED, "--check"])
        with pytest.raises(core.AdmissionRejectV1) as captured:
            builder.build_v1(args)
    finally:
        (chain / core.PACKET_JSON_PATH_V1).write_bytes(original)
    assert captured.value.code == "CHECK_MODE_MISMATCH"


def test_cli_infrastructure_failures_exit_2(tmp_path: Path) -> None:
    not_a_repo = tmp_path / "plain"
    not_a_repo.mkdir()
    process = subprocess.run([PY, str(ROOT / core.CHECKER_PATH_V1), "--root", str(not_a_repo)], capture_output=True, text=True, timeout=120, check=False)
    assert process.returncode == 2
    assert json.loads(process.stdout)["errors"][0]["code"] == "INFRA_GIT_COMMAND"
    relative = subprocess.run([PY, str(ROOT / core.CHECKER_PATH_V1), "--root", "relative/path"], capture_output=True, text=True, timeout=120, check=False)
    assert relative.returncode == 2
    assert json.loads(relative.stdout)["errors"][0]["code"] == "INFRA_ROOT_UNRESOLVABLE"


def test_committed_packet_lifecycle_at_repository_head() -> None:
    """The live repository is admitted at P; a later source commit S' keeps admission and loses applicability.

    Three exact stages: a legacy packet is rejected before any P exists; at P (HEAD is the
    packet commit) the packet is admitted and applicable; at a source commit after P the
    packet stays admitted while the changed pinned sources are reported as drift and the
    verdict stays fail-closed until the next packet commit re-freezes them.
    """

    report = cli.run_checker_v1(cli._parse_args(["--root", str(ROOT)]))
    raw = (ROOT / core.PACKET_JSON_PATH_V1).read_bytes()
    if json.loads(raw).get("schema") != core.PACKET_SCHEMA_V3:
        assert report["ok"] is False and report["packet_admitted"] is False
        assert report["errors"][0]["code"] == "PACKET_SCHEMA_DRIFT"
    elif report["head_commit"] == report["packet_commit"]:
        assert report["ok"] is True, report["errors"]
        assert report["packet_admitted"] is True and report["current_applicable"] is True
        assert report["current_source_drift"] == []
    else:
        # A source commit after P: derive the drift independently from Git and the worktree
        # (never from the report) and require the fail-closed direction.
        drifted: set[str] = set()
        for pin in json.loads(raw).get("source_pins", ()):
            path = str(pin["path"])
            head_blob = subprocess.run(
                ["git", "-C", str(ROOT), "rev-parse", "--verify", "-q", f"HEAD:{path}"],
                capture_output=True, text=True, check=False, timeout=60,
            ).stdout.strip()
            target = ROOT / path
            current = core.sha256_hex_v1(target.read_bytes()) if target.is_file() else None
            if head_blob != pin["git_blob"] or current != pin["sha256"]:
                drifted.add(path)
        if drifted or not report["packet_admitted"]:
            assert report["ok"] is False and report["current_applicable"] is False
        if report["packet_admitted"]:
            assert set(report["current_source_drift"]) >= drifted
            if not report["current_source_drift"]:
                assert report["ok"] is True and report["current_applicable"] is True
    assert report["claim_ceiling"] == core.CLAIM_CEILING_V1
    assert report["proof_replay"]["status"] == "NOT_RUN"


def test_shell_working_bytes_refuses_symlink(tmp_path: Path) -> None:
    target = tmp_path / "real.txt"
    target.write_bytes(b"x")
    (tmp_path / "link.txt").symlink_to(target)
    assert shell.working_bytes_v1(tmp_path, "real.txt") == b"x"
    assert shell.working_bytes_v1(tmp_path, "link.txt") is None
    assert shell.working_bytes_v1(tmp_path, "missing.txt") is None
