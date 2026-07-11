from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
GUEST = REPO_ROOT / "zk/zrpf_risc0/methods/semantic_epoch/src/main.rs"
METHODS_MANIFEST = REPO_ROOT / "zk/zrpf_risc0/methods/Cargo.toml"
METHODS_BUILD = REPO_ROOT / "zk/zrpf_risc0/methods/build.rs"


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
        "decode_exact_semantic_guest_input_v1(&input_bytes)",
        "for disclosure in raw_input.level_one_disclosures()",
        "env::verify(",
        "bind_semantic_guest_input_after_level_one_verification_v1(&raw_input)",
        "compose_semantic_epoch_after_level_one_verification_v1",
        "encode_semantic_epoch_proposal_v1",
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


def test_semantic_guest_derives_authority_fields_instead_of_accepting_them() -> None:
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
    assert "MAX_SEMANTIC_GUEST_INPUT_BYTES_V1 == 297_147" in source
    assert "MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1 == 4_096" in source
    assert "expected_self_image_id" not in source


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
