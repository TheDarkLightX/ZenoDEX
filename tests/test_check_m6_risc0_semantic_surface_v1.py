"""Adversarial tests for the M6 Rust/RISC0 semantic-surface blocker."""

from __future__ import annotations

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


def _python_state_surface_source() -> str:
    return '''
def canonical_bytes_v1(value):
    return b"canonical-json"

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

class GlobalCommandV1:
    kind: str
    command_id: str
    sender: str
    nonce: int
    payload: tuple[str, ...]
    created_height: int
'''


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
    assert report["independent_execution_parity_evidence"] is False
    assert report["activation_eligible"] is False
    assert report["status"] == "BLOCKED_EXECUTABLE_PARITY_EVIDENCE"


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
