"""Adversarial tests for the M6 Rust/RISC0 semantic-surface blocker."""

from __future__ import annotations

import json
from pathlib import Path

from tools.check_m6_risc0_semantic_surface_v1 import (
    check_m6_risc0_semantic_surface,
    inspect_m6_risc0_semantic_surface,
    main,
)

ROOT = Path(__file__).resolve().parents[1]
_FULL_EXECUTION_FIELDS = (
    "deployment",
    "head",
    "writer_epoch",
    "ingress_nonces",
    "economic_atoms",
    "history",
    "nullifiers",
    "finality_certificates",
    "migration",
    "escrows",
    "withdrawals",
    "outbox",
    "acknowledgments",
    "seller_auction_bids",
    "private_swap_participants",
)
_FULL_COMMAND_FIELDS = ("kind", "command_id", "sender", "nonce", "payload", "created_height")


def _python_state_surface_source(*, connected_codec: bool = True) -> str:
    state_root = (
        '''
    @property
    def state_root(self):
        return hash_v1("m6-state-root-v1", self._state_root_canonical())
'''
        if connected_codec
        else '''
    @property
    def state_root(self):
        return repr(self._state_root_canonical())
'''
    )
    return '''
def canonical_bytes_v1(value):
    return b"canonical-json"

def hash_v1(domain, value):
    return canonical_bytes_v1(value)

class M6ApplicationStateV1:
    deployment: str
    head: str
    writer_epoch: int
    ingress_nonces: tuple[str, ...]
    economic_atoms: tuple[str, ...]
    history: tuple[str, ...]
    nullifiers: tuple[str, ...]
    finality_certificates: tuple[str, ...]
    migration: str
    escrows: tuple[str, ...]
    withdrawals: tuple[str, ...]
    outbox: tuple[str, ...]
    acknowledgments: tuple[str, ...]
    seller_auction_bids: tuple[str, ...]
    private_swap_participants: tuple[str, ...]
    history_root_cache: str | None

    def _state_root_canonical(self):
        return {
            "schema": "zenodex/m6-safe-mount/v1",
            "deployment": self.deployment,
            "writer_epoch": self.writer_epoch,
            "ingress_nonces": self.ingress_nonces,
            "economic_atoms": self.economic_atoms,
            "migration": self.migration,
            "escrows": self.escrows,
            "withdrawals": self.withdrawals,
            "outbox": self.outbox,
            "acknowledgments": self.acknowledgments,
            "seller_auction_bids": self.seller_auction_bids,
            "private_swap_participants": self.private_swap_participants,
        }
__STATE_ROOT__

class GlobalCommandV1:
    kind: str
    command_id: str
    sender: str
    nonce: int
    payload: tuple[str, ...]
    created_height: int
'''.replace("__STATE_ROOT__", state_root)


def _rust_state_surface_source(
    *,
    fields: tuple[str, ...],
    uses_postcard: bool,
    command_fields: tuple[str, ...] = _FULL_COMMAND_FIELDS,
) -> str:
    field_declarations = "\n".join(f"    pub {field_name}: RootV1," for field_name in fields)
    command_declarations = "\n".join(
        f"    pub {field_name}: RootV1," for field_name in command_fields
    )
    codec = "hash_postcard_v1(self)" if uses_postcard else "canonical_json_bytes_v1(self)"
    return f'''
pub struct M6ApplicationStateV1 {{
{field_declarations}
}}

pub struct GlobalCommandV1 {{
{command_declarations}
}}

impl M6ApplicationStateV1 {{
    pub fn state_root(&self) -> RootV1 {{
        {codec}
    }}
}}

pub fn run_m6_transition_v1() {{}}
'''


def test_given_current_reduced_rust_envelope_when_inspected_then_zrpf_activation_is_blocked() -> None:
    """Given current sources, a full-M6 RISC0 claim has observable blockers."""

    # Arrange
    report = check_m6_risc0_semantic_surface(ROOT)

    # Act
    raw_missing_fields = report["missing_state_root_fields"]
    assert isinstance(raw_missing_fields, list)
    assert all(isinstance(field_name, str) for field_name in raw_missing_fields)
    missing_fields = set(raw_missing_fields)
    raw_missing_execution_fields = report["missing_execution_state_fields"]
    assert isinstance(raw_missing_execution_fields, list)
    assert all(isinstance(field_name, str) for field_name in raw_missing_execution_fields)
    missing_execution_fields = set(raw_missing_execution_fields)
    raw_missing_command_fields = report["missing_command_fields"]
    assert isinstance(raw_missing_command_fields, list)
    assert all(isinstance(field_name, str) for field_name in raw_missing_command_fields)
    missing_command_fields = set(raw_missing_command_fields)

    # Assert
    assert report["schema"] == "zenodex/m6-risc0-semantic-surface/v1"
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"
    assert report["activation_eligible"] is False
    assert report["python_to_rust_state_surface_match"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["independent_execution_parity_evidence"] is False
    assert isinstance(report["git_head"], str)
    assert len(report["python_source_sha256"]) == 64
    assert len(report["rust_source_sha256"]) == 64
    assert {
        "ingress_nonces",
        "economic_atoms",
        "migration",
        "escrows",
        "withdrawals",
        "acknowledgments",
        "seller_auction_bids",
        "private_swap_participants",
    } <= missing_fields
    assert {
        "history",
        "nullifiers",
        "finality_certificates",
    } <= missing_execution_fields
    assert report["python_to_rust_execution_state_surface_match"] is False
    assert report["python_to_rust_command_surface_match"] is False
    assert {"payload", "created_height"} <= missing_command_fields
    assert main(["--root", str(ROOT)]) == 1


def test_given_output_paths_when_checked_then_durable_reports_bind_exact_sources(
    tmp_path: Path,
) -> None:
    json_out = tmp_path / "surface.json"
    markdown_out = tmp_path / "surface.md"

    exit_code = main(
        [
            "--root",
            str(ROOT),
            "--json-out",
            str(json_out),
            "--markdown-out",
            str(markdown_out),
        ]
    )

    report = json.loads(json_out.read_text(encoding="utf-8"))
    markdown = markdown_out.read_text(encoding="utf-8")
    assert exit_code == 1
    assert report["activation_eligible"] is False
    assert report["git_head"] in markdown
    assert report["python_source_sha256"] in markdown
    assert report["rust_source_sha256"] in markdown
    assert "M6 remains research-only and unmounted" in markdown


def test_mutant_full_field_declaration_without_codec_or_execution_evidence_remains_blocked(
    tmp_path: Path,
) -> None:
    """A field-list-only parity mutant cannot activate ZRPF semantics."""

    # Arrange: this mutant reaches the state-field check but retains postcard
    # hashing and supplies no independently checked direct/RISC0 trace.
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=True),
        encoding="utf-8",
    )

    # Act
    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    # Assert: semantic drift in the canonical root is independently observable.
    assert report["python_to_rust_state_surface_match"] is True
    assert report["python_to_rust_execution_state_surface_match"] is True
    assert report["python_to_rust_command_surface_match"] is True
    assert report["missing_state_root_fields"] == []
    assert report["missing_execution_state_fields"] == []
    assert report["canonical_state_codec_match"] is False
    assert report["independent_execution_parity_evidence"] is False
    assert report["activation_eligible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_given_matching_static_surface_when_no_independent_trace_exists_then_activation_stays_blocked(
    tmp_path: Path,
) -> None:
    """Static source similarity is a prerequisite, never RISC0 parity evidence."""

    # Arrange
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    # Act
    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    # Assert: a static look-alike cannot promote an execution-equivalence claim.
    assert report["python_to_rust_state_surface_match"] is True
    assert report["python_to_rust_execution_state_surface_match"] is True
    assert report["python_to_rust_command_surface_match"] is True
    assert report["canonical_state_codec_match"] is True
    assert report["extra_rust_state_fields"] == []
    assert report["independent_execution_parity_evidence"] is False
    assert report["activation_eligible"] is False
    assert report["status"] == "BLOCKED_EXECUTABLE_PARITY_EVIDENCE"


def test_mutant_commented_rust_surface_cannot_forge_static_parity(tmp_path: Path) -> None:
    """Commented declarations and calls carry no Rust semantic surface."""

    # Arrange: the comment contains a complete look-alike before the reduced
    # live declarations. A text-only scanner incorrectly selects the comment.
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    forged_surface = _rust_state_surface_source(
        fields=_FULL_EXECUTION_FIELDS,
        uses_postcard=False,
    )
    rust_source.write_text(
        f'''/*
{forged_surface}
*/
pub struct M6ApplicationStateV1 {{
    pub deployment: RootV1,
}}

pub struct GlobalCommandV1 {{
    pub kind: RootV1,
}}

impl M6ApplicationStateV1 {{
    pub fn state_root(&self) -> RootV1 {{
        hash_postcard_v1(self)
    }}
}}
''',
        encoding="utf-8",
    )

    # Act
    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    # Assert: only live Rust code may satisfy a semantic-surface prerequisite.
    assert report["python_to_rust_state_surface_match"] is False
    assert report["python_to_rust_execution_state_surface_match"] is False
    assert report["python_to_rust_command_surface_match"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["rust_postcard_state_codec_visible"] is True
    assert report["rust_transition_function_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_unrelated_python_codec_declaration_cannot_forge_codec_parity(
    tmp_path: Path,
) -> None:
    """A canonical-codec symbol must be connected to the Python state root."""

    # Arrange: the fixture declares canonical_bytes_v1 but its state-root path
    # never calls it, directly or through hash_v1.
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source(connected_codec=False),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    # Act
    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    # Assert: declaration visibility alone is not codec-path evidence.
    assert report["python_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_swapped_python_root_bindings_cannot_forge_state_parity(tmp_path: Path) -> None:
    """Root keys must bind the same-named state attributes."""

    # Arrange: every required key remains present, but two value bindings are
    # crossed. A key-only extractor reports this malformed root as complete.
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source()
        .replace('"deployment": self.deployment', '"deployment": self.outbox')
        .replace('"outbox": self.outbox', '"outbox": self.deployment'),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    # Act
    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    # Assert: crossed key/value identity is a malformed semantic surface.
    assert report["python_to_rust_state_surface_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"
    assert any("must bind self.deployment" in error for error in report["errors"])


def test_mutant_dead_python_codec_call_cannot_forge_codec_parity(tmp_path: Path) -> None:
    """A codec call in an unreachable branch is not state-root evidence."""

    # Arrange: state_root calls hash_v1, but hash_v1 reaches the canonical
    # codec only under an always-false branch and returns noncanonical bytes.
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "def hash_v1(domain, value):\n    return canonical_bytes_v1(value)",
            "def hash_v1(domain, value):\n"
            "    if False:\n"
            "        canonical_bytes_v1(value)\n"
            "    return repr(value)",
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    # Act
    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    # Assert
    assert report["python_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_rust_identifier_prefixes_cannot_forge_live_functions(tmp_path: Path) -> None:
    """V1 function checks require exact Rust identifiers."""

    # Arrange: all fields remain, while the two required function names are
    # replaced by longer prefix-sharing identifiers.
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False)
        .replace("state_root", "state_root_helper")
        .replace("run_m6_transition_v1", "run_m6_transition_v10"),
        encoding="utf-8",
    )

    # Act
    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    # Assert
    assert report["rust_transition_function_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_extra_rust_authority_field_remains_semantically_blocked(tmp_path: Path) -> None:
    """An undeclared Rust authority coordinate cannot be silently accepted."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(
            fields=(*_FULL_EXECUTION_FIELDS, "authority_override"),
            uses_postcard=False,
        ),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["extra_rust_state_fields"] == ["authority_override"]
    assert report["python_to_rust_execution_state_surface_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_unknown_python_cache_field_is_not_assumed_derived(tmp_path: Path) -> None:
    """Only explicitly owned derived caches may leave the execution surface."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "    history_root_cache: str | None",
            "    history_root_cache: str | None\n    authority_cache: str | None",
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["missing_execution_state_fields"] == ["authority_cache"]
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_rust_state_field_reordering_remains_semantically_blocked(tmp_path: Path) -> None:
    """Canonical state declaration order is part of this static prerequisite."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    reordered = list(_FULL_EXECUTION_FIELDS)
    reordered[0], reordered[1] = reordered[1], reordered[0]
    rust_source.write_text(
        _rust_state_surface_source(fields=tuple(reordered), uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["missing_execution_state_fields"] == []
    assert report["extra_rust_state_fields"] == []
    assert report["python_to_rust_execution_state_surface_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"
    assert any("field order differs" in error for error in report["errors"])


def test_source_hash_binding_changes_for_one_byte_without_promoting_status(tmp_path: Path) -> None:
    """A one-byte source drift produces a distinct, non-activating report subject."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )
    before = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    rust_source.write_text(rust_source.read_text(encoding="utf-8") + " ", encoding="utf-8")
    after = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert before["rust_source_sha256"] != after["rust_source_sha256"]
    assert before["python_source_sha256"] == after["python_source_sha256"]
    assert before["status"] == after["status"] == "BLOCKED_EXECUTABLE_PARITY_EVIDENCE"
    assert before["activation_eligible"] is after["activation_eligible"] is False


def test_mutant_command_projection_without_payload_remains_semantically_blocked(
    tmp_path: Path,
) -> None:
    """A root-compatible command envelope cannot replace the typed M6 payload."""

    # Arrange
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    command_fields_without_payload = tuple(
        field_name for field_name in _FULL_COMMAND_FIELDS if field_name != "payload"
    )
    rust_source.write_text(
        _rust_state_surface_source(
            fields=_FULL_EXECUTION_FIELDS,
            command_fields=command_fields_without_payload,
            uses_postcard=False,
        ),
        encoding="utf-8",
    )

    # Act
    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    # Assert
    assert report["python_to_rust_state_surface_match"] is True
    assert report["python_to_rust_execution_state_surface_match"] is True
    assert report["canonical_state_codec_match"] is True
    assert report["missing_command_fields"] == ["payload"]
    assert report["python_to_rust_command_surface_match"] is False
    assert report["activation_eligible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_given_malformed_python_state_surface_when_inspected_then_gate_reports_a_closed_blocker(
    tmp_path: Path,
) -> None:
    """Malformed source is a rejection case, never an implicit empty surface."""

    # Arrange
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text("class M6ApplicationStateV1\n", encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=("deployment",), uses_postcard=False),
        encoding="utf-8",
    )

    # Act
    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    # Assert
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"
    assert report["activation_eligible"] is False
    raw_errors = report["errors"]
    assert isinstance(raw_errors, list)
    assert any("cannot parse Python M6 types" in error for error in raw_errors)


def test_given_missing_source_when_inspected_then_gate_returns_json_safe_blocker(tmp_path: Path) -> None:
    """A missing proof surface is an explicit blocker rather than a traceback."""

    # Arrange
    missing_python_source = tmp_path / "missing_m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    rust_source.write_text(
        _rust_state_surface_source(fields=("deployment",), uses_postcard=False),
        encoding="utf-8",
    )

    # Act
    report = inspect_m6_risc0_semantic_surface(missing_python_source, rust_source)

    # Assert
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"
    assert report["activation_eligible"] is False
    raw_errors = report["errors"]
    assert isinstance(raw_errors, list)
    assert any("cannot read Python M6 types" in error for error in raw_errors)
