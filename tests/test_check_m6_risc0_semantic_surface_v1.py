"""Adversarial tests for the M6 Rust/RISC0 semantic-surface blocker."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from tools.check_m6_risc0_semantic_surface_v1 import (
    _risc0_guest_calls_m6_transition,
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
    assert len(report["checker_source_sha256"]) == 64
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
    assert report["checker_source_sha256"] in markdown
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


@pytest.mark.parametrize(
    "replacement",
    (
        "return canonical_bytes_v1(value) + b'\\x00'",
        "return b'prefix' + canonical_bytes_v1(value)",
        "return f'{canonical_bytes_v1(value)}'",
    ),
)
def test_mutant_python_codec_transform_blocks_static_parity(
    tmp_path: Path,
    replacement: str,
) -> None:
    """A canonical value must reach hashing byte-for-byte, without transforms."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "return canonical_bytes_v1(value)",
            replacement,
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


@pytest.mark.parametrize(
    "mutation",
    (
        '\nglobals()["hash_v1"] = lambda domain, value: repr(value)\n',
        '\nsetattr(object, "hash_v1", repr)\n',
        '\nexec("hash_v1 = repr")\n',
    ),
)
def test_mutant_dynamic_python_rebinding_blocks_static_parity(
    tmp_path: Path,
    mutation: str,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source() + mutation, encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_python_class_decorator_blocks_static_parity(tmp_path: Path) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "class M6ApplicationStateV1:",
            "@(lambda cls: object)\nclass M6ApplicationStateV1:",
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
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


def test_mutant_unreachable_python_codec_after_raise_cannot_forge_parity(
    tmp_path: Path,
) -> None:
    """A direct call after a terminating statement is not executable evidence."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "def hash_v1(domain, value):\n    return canonical_bytes_v1(value)",
            "def hash_v1(domain, value):\n"
            "    raise RuntimeError('dead')\n"
            "    return canonical_bytes_v1(value)",
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_discarded_python_codec_value_cannot_forge_parity(tmp_path: Path) -> None:
    """Calling the codec is insufficient when its value cannot reach the root."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "def hash_v1(domain, value):\n    return canonical_bytes_v1(value)",
            "def hash_v1(domain, value):\n"
            "    canonical_bytes_v1(value)\n"
            "    return repr(value)",
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_reassigned_python_codec_value_cannot_forge_parity(tmp_path: Path) -> None:
    """Reassignment removes provenance from an earlier canonical value."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "def hash_v1(domain, value):\n    return canonical_bytes_v1(value)",
            "def hash_v1(domain, value):\n"
            "    selected = canonical_bytes_v1(value)\n"
            "    selected = repr(value)\n"
            "    return selected",
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


@pytest.mark.parametrize(
    ("mutant", "label"),
    (
        (
            "    accumulator = {}\n"
            "    accumulator.update(canonical_bytes_v1(value))\n"
            "    return accumulator.clear()",
            "destructive accumulator",
        ),
        (
            "    return canonical_bytes_v1(value)\n\n"
            "def hash_v1(domain, value):\n"
            "    return repr(value)",
            "duplicate function",
        ),
        (
            "    return canonical_bytes_v1(value)\n\n"
            "hash_v1 = repr",
            "assignment rebinding",
        ),
        (
            "    return canonical_bytes_v1(value)\n\n"
            "hash_v1, other = repr, bytes",
            "destructuring rebinding",
        ),
    ),
)
def test_mutant_rebound_or_cleared_python_codec_cannot_upgrade_semantic_surface_status(
    tmp_path: Path,
    mutant: str,
    label: str,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "    return canonical_bytes_v1(value)",
            mutant,
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"
    assert label


def test_mutant_deferred_python_codec_call_cannot_forge_parity(tmp_path: Path) -> None:
    """A codec hidden in a returned lambda has not produced the state root."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "def hash_v1(domain, value):\n    return canonical_bytes_v1(value)",
            "def hash_v1(domain, value):\n"
            "    return lambda: canonical_bytes_v1(value)",
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_selected_away_python_codec_value_cannot_forge_parity(
    tmp_path: Path,
) -> None:
    """A canonical value in a discarded tuple arm does not reach the root."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "def hash_v1(domain, value):\n    return canonical_bytes_v1(value)",
            "def hash_v1(domain, value):\n"
            "    selected = (canonical_bytes_v1(value), repr(value))[1]\n"
            "    return selected",
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_selected_away_python_state_hash_cannot_forge_parity(
    tmp_path: Path,
) -> None:
    """A valid hash call must itself determine the returned state root."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            'return hash_v1("m6-state-root-v1", self._state_root_canonical())',
            'return (repr(self), hash_v1("m6-state-root-v1", self._state_root_canonical()))[0]',
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_dead_rust_codec_branch_cannot_forge_codec_parity(tmp_path: Path) -> None:
    """A canonical-codec call inside a nested branch is not direct root use."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False).replace(
            "canonical_json_bytes_v1(self)",
            "if false { canonical_json_bytes_v1(self); }\n        noncanonical_hash(self)",
        ),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["rust_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_discarded_rust_codec_value_cannot_forge_codec_parity(tmp_path: Path) -> None:
    """A canonical call followed by another tail expression is not root use."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False).replace(
            "canonical_json_bytes_v1(self)",
            "canonical_json_bytes_v1(self);\n        noncanonical_hash(self)",
        ),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["rust_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_selected_away_rust_codec_value_cannot_forge_codec_parity(
    tmp_path: Path,
) -> None:
    """A canonical call in an unselected tuple arm is not root evidence."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False).replace(
            "canonical_json_bytes_v1(self)",
            "(noncanonical_hash(self), canonical_json_bytes_v1(self)).0",
        ),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["rust_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


@pytest.mark.parametrize(
    "replacement",
    (
        "let canonical_json_bytes_v1 = |value: &M6ApplicationStateV1| "
        "noncanonical_hash(value);\n        return canonical_json_bytes_v1(self)",
        "canonical_json_bytes_v1(self).len()",
    ),
)
def test_mutant_rust_codec_shadow_or_post_call_transform_cannot_forge_parity(
    tmp_path: Path,
    replacement: str,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(
            fields=_FULL_EXECUTION_FIELDS,
            uses_postcard=False,
        ).replace("canonical_json_bytes_v1(self)", replacement),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["rust_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_cfg_gated_rust_surface_cannot_forge_static_parity(tmp_path: Path) -> None:
    """Conditionally compiled look-alikes do not satisfy the launch surface."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        "#[cfg(any())]\n"
        + _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_to_rust_state_surface_match"] is False
    assert report["rust_transition_function_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"
    assert any("conditionally compiled" in error for error in report["errors"])


@pytest.mark.parametrize(("opening", "closing"), (("{", "}"), ("(", ")"), ("[", "]")))
def test_mutant_macro_discarded_rust_items_cannot_upgrade_semantic_surface_status(
    tmp_path: Path,
    opening: str,
    closing: str,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        "macro_rules! discard { ($($tokens:tt)*) => {}; }\n"
        f"discard! {opening}\n"
        + _rust_state_surface_source(
            fields=_FULL_EXECUTION_FIELDS,
            uses_postcard=False,
        )
        + f"\n{closing}\n",
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["rust_canonical_codec_visible"] is False
    assert report["rust_transition_function_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_rebound_python_state_class_cannot_upgrade_semantic_surface_status(
    tmp_path: Path,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source()
        + "\nM6ApplicationStateV1 = object\n",
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_conditional_python_state_class_rebind_cannot_upgrade_status(
    tmp_path: Path,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source()
        + "\nif True:\n    M6ApplicationStateV1 = object\n",
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_function_local_python_codec_shadow_cannot_forge_parity(
    tmp_path: Path,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "def hash_v1(domain, value):\n    return canonical_bytes_v1(value)",
            "def hash_v1(domain, value):\n"
            "    canonical_bytes_v1 = lambda item: repr(item)\n"
            "    return canonical_bytes_v1(value)",
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


@pytest.mark.parametrize(
    "rebinding",
    (
        "for M6ApplicationStateV1 in (object,):\n    pass",
        "try:\n    pass\nexcept Exception as M6ApplicationStateV1:\n    pass",
        "match object:\n    case M6ApplicationStateV1:\n        pass",
        "(M6ApplicationStateV1 := object)",
    ),
)
def test_mutant_nonassignment_python_state_rebind_cannot_upgrade_status(
    tmp_path: Path,
    rebinding: str,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source() + "\n" + rebinding + "\n",
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


@pytest.mark.parametrize(
    "replacement",
    (
        "for canonical_bytes_v1 in (lambda item: repr(item),):\n"
        "        pass\n    return canonical_bytes_v1(value)",
        "def canonical_bytes_v1(item):\n"
        "        return repr(item)\n    return canonical_bytes_v1(value)",
    ),
)
def test_mutant_nonassignment_python_codec_shadow_cannot_forge_parity(
    tmp_path: Path,
    replacement: str,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(
        _python_state_surface_source().replace(
            "return canonical_bytes_v1(value)",
            replacement,
        ),
        encoding="utf-8",
    )
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


@pytest.mark.parametrize(
    "replacement",
    (
        "fn canonical_json_bytes_v1(_: &M6ApplicationStateV1) -> Vec<u8> { vec![] }\n"
        "        return canonical_json_bytes_v1(self)",
        "const canonical_json_bytes_v1: fn(&M6ApplicationStateV1) -> Vec<u8> = "
        "noncanonical_hash;\n        return canonical_json_bytes_v1(self)",
        "use attacker::canonical_json_bytes_v1;\n        return canonical_json_bytes_v1(self)",
    ),
)
def test_mutant_rust_item_or_import_codec_shadow_cannot_forge_parity(
    tmp_path: Path,
    replacement: str,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(
            fields=_FULL_EXECUTION_FIELDS,
            uses_postcard=False,
        ).replace("canonical_json_bytes_v1(self)", replacement),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["rust_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_rust_codec_parameter_shadow_cannot_forge_parity(tmp_path: Path) -> None:
    """A same-name function parameter is provider code, not the pinned codec."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(
            fields=_FULL_EXECUTION_FIELDS,
            uses_postcard=False,
        ).replace(
            "pub fn state_root(&self)",
            "pub fn state_root(&self, canonical_json_bytes_v1: fn(&Self) -> RootV1)",
        ),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["rust_canonical_codec_visible"] is False
    assert report["canonical_state_codec_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


@pytest.mark.parametrize(
    "mutation",
    (
        "fn canonical_json_bytes_v1(_: &M6ApplicationStateV1) -> RootV1 { [0; 32] }\n",
        "const canonical_json_bytes_v1: fn(&M6ApplicationStateV1) -> RootV1 = attacker;\n",
        "use attacker::canonical_json_bytes_v1;\n",
    ),
)
def test_mutant_rust_module_codec_shadow_cannot_forge_parity(
    tmp_path: Path,
    mutation: str,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        mutation
        + _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["rust_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_rust_destructuring_parameter_shadow_cannot_forge_parity(
    tmp_path: Path,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False).replace(
            "pub fn state_root(&self)",
            "pub fn state_root(&self, canonical_json_bytes_v1 @ _: fn(&Self) -> RootV1)",
        ),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["rust_canonical_codec_visible"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_mutant_cfg_gated_rust_field_cannot_forge_static_parity(tmp_path: Path) -> None:
    """A required field that disappears in one build profile is not parity."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False).replace(
            "    pub economic_atoms: RootV1,",
            "    #[cfg(feature = \"economic\")]\n    pub economic_atoms: RootV1,",
        ),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_to_rust_state_surface_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"
    assert any("fields are conditionally compiled" in error for error in report["errors"])


@pytest.mark.parametrize(
    "attribute",
    ("skip", "skip_serializing", 'rename = "foreign"', "flatten", 'with = "attacker"'),
)
def test_mutant_rust_serde_field_transform_cannot_forge_parity(
    tmp_path: Path,
    attribute: str,
) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False).replace(
            "    pub economic_atoms: RootV1,",
            f"    #[serde({attribute})]\n    pub economic_atoms: RootV1,",
        ),
        encoding="utf-8",
    )

    report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert report["python_to_rust_state_surface_match"] is False
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"
    assert any("serialization attributes" in error for error in report["errors"])


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


def test_mutant_private_rust_authority_field_remains_semantically_blocked(tmp_path: Path) -> None:
    """Private storage can affect execution and belongs in the state inventory."""

    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_source.write_text(_python_state_surface_source(), encoding="utf-8")
    rust_source.write_text(
        _rust_state_surface_source(fields=_FULL_EXECUTION_FIELDS, uses_postcard=False).replace(
            "    pub private_swap_participants: RootV1,",
            "    pub private_swap_participants: RootV1,\n    authority_override: RootV1,",
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


def test_source_hash_uses_raw_bytes_for_line_ending_bve(tmp_path: Path) -> None:
    python_source = tmp_path / "m6_safe_mount_types_v1.py"
    rust_source = tmp_path / "m6_core_v1.rs"
    python_lf = _python_state_surface_source().encode("utf-8")
    rust_lf = _rust_state_surface_source(
        fields=_FULL_EXECUTION_FIELDS,
        uses_postcard=False,
    ).encode("utf-8")
    python_source.write_bytes(python_lf)
    rust_source.write_bytes(rust_lf)
    lf_report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    python_source.write_bytes(python_lf.replace(b"\n", b"\r\n"))
    rust_source.write_bytes(rust_lf.replace(b"\n", b"\r\n"))
    crlf_report = inspect_m6_risc0_semantic_surface(python_source, rust_source)

    assert lf_report["python_source_sha256"] != crlf_report["python_source_sha256"]
    assert lf_report["rust_source_sha256"] != crlf_report["rust_source_sha256"]


def test_repository_report_binds_guest_transition_and_checker_closure() -> None:
    report = check_m6_risc0_semantic_surface(ROOT)

    assert report["risc0_guest_transition_reachable"] is False
    assert report["checker_subject_matches_executing"] is True
    assert {
        "python_transition",
        "rust_shared_lib",
        "rust_shared_cargo",
        "rust_guest",
        "rust_methods_cargo",
    } <= set(report["source_paths"])
    assert report["status"] == "BLOCKED_SEMANTIC_SURFACE"


def test_scoped_clean_includes_python_transition_and_guest_closure(tmp_path: Path) -> None:
    paths = {
        "src/core/m6_safe_mount_types_v1.py": _python_state_surface_source(),
        "src/core/m6_safe_mount_transition_v1.py": "def transition():\n    return None\n",
        "zk/recursive_stark_v2_risc0/shared/src/m6_core_v1.rs": _rust_state_surface_source(
            fields=_FULL_EXECUTION_FIELDS,
            uses_postcard=False,
        ),
        "zk/recursive_stark_v2_risc0/shared/src/lib.rs": "pub mod m6_core_v1;\n",
        "zk/recursive_stark_v2_risc0/shared/Cargo.toml": "[package]\nname='shared'\n",
        "zk/recursive_stark_v2_risc0/methods/aggregate_v2/src/main.rs": (
            "fn main() { run_m6_transition_v1(); }\n"
        ),
        "zk/recursive_stark_v2_risc0/methods/aggregate_v2/Cargo.toml": (
            "[dependencies]\ntau-state-proof-risc0-shared-v2 = { path = '../../../shared' }\n"
        ),
        "tools/check_m6_risc0_semantic_surface_v1.py": (
            ROOT / "tools/check_m6_risc0_semantic_surface_v1.py"
        ).read_text(encoding="utf-8"),
    }
    for relative, body in paths.items():
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
    subprocess.run(("git", "init", "-q"), cwd=tmp_path, check=True)
    subprocess.run(("git", "config", "user.email", "m6-test@example.invalid"), cwd=tmp_path, check=True)
    subprocess.run(("git", "config", "user.name", "M6 Test"), cwd=tmp_path, check=True)
    subprocess.run(("git", "add", "."), cwd=tmp_path, check=True)
    subprocess.run(("git", "commit", "-qm", "fixture"), cwd=tmp_path, check=True)
    assert check_m6_risc0_semantic_surface(tmp_path)["scoped_worktree_clean"] is True

    transition = tmp_path / "src/core/m6_safe_mount_transition_v1.py"
    transition.write_text(transition.read_text(encoding="utf-8") + "# drift\n", encoding="utf-8")
    assert check_m6_risc0_semantic_surface(tmp_path)["scoped_worktree_clean"] is False
    transition.write_text(paths["src/core/m6_safe_mount_transition_v1.py"], encoding="utf-8")
    guest = tmp_path / "zk/recursive_stark_v2_risc0/methods/aggregate_v2/src/main.rs"
    guest.write_text(guest.read_text(encoding="utf-8") + "// drift\n", encoding="utf-8")
    assert check_m6_risc0_semantic_surface(tmp_path)["scoped_worktree_clean"] is False


def test_mutant_discarded_guest_macro_and_commented_dependency_cannot_forge_reachability(
    tmp_path: Path,
) -> None:
    """RIPR: discarded tokens and Cargo comments carry no execution edge."""

    guest = tmp_path / "main.rs"
    cargo = tmp_path / "Cargo.toml"
    guest.write_text(
        "macro_rules! discard { ($($tokens:tt)*) => {}; }\n"
        "discard! { fn decoy() { run_m6_transition_v1(); } }\n"
        "pub fn main() {}\n",
        encoding="utf-8",
    )
    cargo.write_text(
        "[package]\nname='guest'\nversion='0.1.0'\n"
        "# tau-state-proof-risc0-shared-v2 = { path = '../../shared' }\n",
        encoding="utf-8",
    )

    assert _risc0_guest_calls_m6_transition(guest, cargo) is False

    cargo.write_text(
        "[package]\nname='guest'\nversion='0.1.0'\n"
        "[dependencies]\ntau-state-proof-risc0-shared-v2 = { path = '../../shared' }\n",
        encoding="utf-8",
    )
    assert _risc0_guest_calls_m6_transition(guest, cargo) is False

    guest.write_text("pub fn main() { run_m6_transition_v1(); }\n", encoding="utf-8")
    assert _risc0_guest_calls_m6_transition(guest, cargo) is True

    for decoy in (
        "pub fn main() { if false { run_m6_transition_v1(); } }\n",
        "pub fn main() { discard!(run_m6_transition_v1()); }\n",
        "pub fn main() { let never_called = || run_m6_transition_v1(); }\n",
        "pub fn main() { fn decoy() { run_m6_transition_v1(); } }\n",
    ):
        guest.write_text(decoy, encoding="utf-8")
        assert _risc0_guest_calls_m6_transition(guest, cargo) is False


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
