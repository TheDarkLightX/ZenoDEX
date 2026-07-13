from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
GUEST = REPO_ROOT / "zk/zrpf_risc0/methods/semantic_epoch/src/main.rs"
METHODS_MANIFEST = REPO_ROOT / "zk/zrpf_risc0/methods/Cargo.toml"
METHODS_BUILD = REPO_ROOT / "zk/zrpf_risc0/methods/build.rs"
VERIFIER_LIB = REPO_ROOT / "zk/zrpf_risc0/verifier/src/lib.rs"
VERIFIER_V2 = REPO_ROOT / "zk/zrpf_risc0/verifier/src/semantic_epoch_v2.rs"
PROVER = REPO_ROOT / "zk/zrpf_risc0/harness/src/bin/prove_semantic_epoch.rs"
SEMANTIC_SHARED_MANIFEST = REPO_ROOT / "zk/zrpf_risc0/semantic_shared/Cargo.toml"
SEMANTIC_SHARED_LIB = REPO_ROOT / "zk/zrpf_risc0/semantic_shared/src/lib.rs"
ACTIVE_V2_IDENTITY_SOURCES = (
    GUEST,
    REPO_ROOT / "zk/zrpf_risc0/semantic_shared/src/codec_v2.rs",
    REPO_ROOT / "zk/zrpf_risc0/semantic_shared/src/bind_v2.rs",
    REPO_ROOT / "zk/zrpf_risc0/semantic_shared/src/epoch_v2.rs",
    REPO_ROOT / "zk/zrpf_protocol/protocol/src/semantic_epoch_v2/proposal.rs",
    REPO_ROOT / "zk/zrpf_protocol/protocol/src/semantic_epoch_v2/hash.rs",
)


def _guest_source() -> str:
    return GUEST.read_text(encoding="utf-8")


def _guest_main(source: str) -> str:
    start = source.index("pub fn main()")
    end = source.index("fn read_bounded_input()", start)
    return source[start:end]


def test_semantic_guest_preserves_verify_before_interpret_order() -> None:
    source = _guest_source()
    main = _guest_main(source)
    ordered_markers = (
        "decode_exact_semantic_guest_input_v2(&input_bytes)",
        "for disclosure in raw_input.level_one_disclosures()",
        "env::verify(",
        "bind_semantic_guest_input_after_level_one_verification_v2(&raw_input)",
        "compose_semantic_epoch_after_level_one_verification_v2",
        "encode_semantic_epoch_proposal_v2",
        "env::commit_slice(&proposal_bytes)",
    )
    positions = [main.index(marker) for marker in ordered_markers]
    assert positions == sorted(positions)
    assert main.count("env::verify(") == 1
    assert "PINNED_LEVEL_ONE_IMAGE_ID_B" in source
    assert re.search(
        r"env::verify\(\s*PINNED_LEVEL_ONE_IMAGE_ID_B,\s*"
        r"disclosure\.journal_bytes\(\),?\s*\)",
        source,
    )


def test_semantic_guest_derives_statement_fields_instead_of_accepting_them() -> None:
    source = _guest_source()
    forbidden_raw_input_fields = (
        "receipt_valid",
        "proof_tree_root:",
        "semantic_epoch_root:",
        "program_manifest_root:",
        "proof_profile_id:",
    )
    for field in forbidden_raw_input_fields:
        assert field not in source
    assert "MAX_SEMANTIC_GUEST_INPUT_BYTES_V2 == 297_115" in source
    assert "MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2 == 4_096" in source
    assert "expected_self_image_id" not in source


def test_active_v2_reachable_identity_surface_has_no_runtime_self_field() -> None:
    sources = {path: path.read_text(encoding="utf-8") for path in ACTIVE_V2_IDENTITY_SOURCES}
    codec = sources[ACTIVE_V2_IDENTITY_SOURCES[1]]
    proposal = sources[ACTIVE_V2_IDENTITY_SOURCES[4]]
    combined = "\n".join(sources.values())

    assert "expected_semantic_self_image_id" not in combined
    assert "host_declared_semantic_program_id" not in combined
    assert "SemanticGuestInputV1" not in sources[GUEST]
    assert "expected_self_image_id" not in codec
    assert (
        re.search(
            r"^\s*(?:pub\([^)]*\)\s+|pub\s+)?actual_program_id\s*:",
            proposal,
            re.M,
        )
        is None
    )
    assert "pub const fn actual_program_id" not in proposal
    assert (
        re.search(
            r"^\s*(?:pub\([^)]*\)\s+|pub\s+)?program_manifest_root\s*:",
            proposal,
            re.M,
        )
        is None
    )
    assert "pub const fn program_manifest_root" not in proposal
    assert "dependency_manifest_root" in proposal
    assert "VerifiedSemanticEpochReceiptV2" not in sources[GUEST]


def test_active_v2_guest_excludes_historical_self_bearing_modules() -> None:
    method_manifest = (GUEST.parent.parent / "Cargo.toml").read_text(encoding="utf-8")
    shared_manifest = SEMANTIC_SHARED_MANIFEST.read_text(encoding="utf-8")
    shared_lib = SEMANTIC_SHARED_LIB.read_text(encoding="utf-8")

    assert (
        "zenodex-zrpf-risc0-semantic-shared = { path = \"../../semantic_shared\", "
        "default-features = false }"
    ) in method_manifest
    assert 'default = ["historical-v1"]' in shared_manifest
    assert 'historical-v1 = []' in shared_manifest
    for module in ("bind_v1", "codec_v1", "epoch_v1"):
        assert (
            '#[cfg(feature = "historical-v1")]\n'
            f"mod {module};"
        ) in shared_lib
        assert (
            '#[cfg(feature = "historical-v1")]\n'
            f"pub use {module}::*;"
        ) in shared_lib
    assert "mod disclosure_v1;" in shared_lib
    assert "pub use disclosure_v1::*;" in shared_lib


def test_semantic_guest_has_a_dedicated_duplicate_source_reject_code() -> None:
    source = _guest_source()
    exact_error = (
        "SemanticEpochCompositionErrorV2::SemanticRecomposition(\n"
        "                SemanticRecompositionErrorV1::DuplicateSemanticSource,"
    )
    exact_abort = 'abort("ZRPF semantic epoch duplicate semantic source rejected")'
    generic_abort = 'abort("ZRPF semantic epoch composition rejected")'
    assert exact_error in source
    assert source.index(exact_error) < source.index(exact_abort)
    assert source.index(exact_abort) < source.index(generic_abort)


def test_semantic_method_is_registered_with_fail_closed_host_placeholders() -> None:
    manifest = METHODS_MANIFEST.read_text(encoding="utf-8")
    build = METHODS_BUILD.read_text(encoding="utf-8")
    assert '"semantic_epoch"' in manifest
    assert (
        "pub const ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ELF: &[u8] = &[];" in build
    )
    assert (
        "pub const ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID: [u32; 8] = [0; 8];"
        in build
    )


def test_active_verifier_export_is_v2_and_v1_is_explicitly_historical() -> None:
    source = VERIFIER_LIB.read_text(encoding="utf-8")
    assert '#[path = "semantic_epoch_v1.rs"]' in source
    assert "pub mod historical_semantic_epoch_v1;" in source
    assert "pub use semantic_epoch_v1" not in source
    assert (
        "pub use semantic_epoch_v2::{VerifiedSemanticEpochReceiptErrorV2, "
        "VerifiedSemanticEpochReceiptV2};"
    ) in source


def test_v2_verifier_authenticates_receipt_before_decoding_or_attaching_identity() -> None:
    source = VERIFIER_V2.read_text(encoding="utf-8")
    start = source.index("pub fn verify_canonical_succinct_bytes(")
    end = source.index("pub fn verify_exact_succinct_bytes(", start)
    constructor = source[start:end]
    markers = (
        "verify_canonical_succinct_receipt_artifact(receipt_bytes, expected_image_id)",
        "decode_exact_semantic_epoch_proposal_v2(&receipt.journal.bytes)",
        "attach_verified_runtime_identity_v2(",
        "derive_risc0_verified_claim_binding_v1(expected_image_id, &receipt.journal.bytes)",
        "Ok(Self {",
    )
    positions = [constructor.index(marker) for marker in markers]
    assert positions == sorted(positions)


def test_v2_prover_reports_have_explicit_schemas_and_profile_identity() -> None:
    source = PROVER.read_text(encoding="utf-8")
    assert "zenodex/zrpf_semantic_epoch_v2_proof_report/v1" in source
    assert "zenodex/zrpf_semantic_epoch_v2_duplicate_source_report/v1" in source
    assert '"receipt_profile_id": verified.receipt_profile().profile_id()' in source
