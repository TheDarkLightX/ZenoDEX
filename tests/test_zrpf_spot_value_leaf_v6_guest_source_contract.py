from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
GUEST = REPO_ROOT / "zk/zrpf_risc0/methods/spot_value_leaf_v6/src/main.rs"
SHARED = REPO_ROOT / "zk/zrpf_risc0/spot_value_leaf_v6_shared"
V6_METHODS = REPO_ROOT / "zk/zrpf_risc0/spot_v6_methods"
METHODS_MANIFEST = V6_METHODS / "Cargo.toml"
METHODS_BUILD = V6_METHODS / "build.rs"
VERIFIER = REPO_ROOT / "zk/zrpf_risc0/verifier/src/spot_value_leaf_v6.rs"


def test_v6_guest_authenticates_exact_adapter_before_source_recomposition() -> None:
    source = GUEST.read_text(encoding="utf-8")
    authenticate_start = source.index("pub(super) fn authenticate(")
    authenticate_end = source.index("pub(super) fn recompose(", authenticate_start)
    authenticate = source[authenticate_start:authenticate_end]
    main = source[source.index("pub fn main()") : source.index("fn read_bounded_input()")]

    assert authenticate.count("env::verify(") == 1
    assert re.search(
        r"env::verify\(\s*PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,\s*"
        r"envelope\.adapter_journal_bytes\(\),?\s*\)",
        authenticate,
    )
    ordered_markers = (
        "decode_exact_source_opened_spot_value_leaf_input_v6(&input_bytes)",
        "ReceiptVerifiedSourceOpenedSpotInputV6::authenticate(envelope)",
        "verified.recompose()",
        "encode_source_opened_spot_value_leaf_statement_v6(&statement)",
        "env::commit_slice(&statement_bytes)",
    )
    positions = [main.index(marker) for marker in ordered_markers]
    assert positions == sorted(positions)


def test_v6_reachable_statement_surface_has_no_claimed_self_image() -> None:
    paths = (
        GUEST,
        SHARED / "src/input.rs",
        SHARED / "src/statement.rs",
        SHARED / "src/compose.rs",
    )
    combined = "\n".join(path.read_text(encoding="utf-8") for path in paths)
    for field in ("expected_self_image_id", "host_declared_program_id", "actual_program_id"):
        assert re.search(rf"^\s*(?:pub(?:\([^)]*\))?\s+)?{field}\s*:", combined, re.M) is None
        assert f"fn {field}(" not in combined
    assert "receipt_valid" not in combined
    assert "settlement_authority" not in combined
    assert "PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID" in combined
    assert "program_manifest_class_commitment" in combined


def test_v6_method_registration_has_fail_closed_host_placeholders() -> None:
    manifest = METHODS_MANIFEST.read_text(encoding="utf-8")
    build = METHODS_BUILD.read_text(encoding="utf-8")

    assert '"../methods/spot_value_leaf_v6"' in manifest
    assert "ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF: &[u8] = &[];" in build
    assert "ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID: [u32; 8] = [0; 8];" in build


def test_v6_leaf_verifier_public_constructor_selects_the_governed_image() -> None:
    source = VERIFIER.read_text(encoding="utf-8")

    assert "pub fn verify_governed_canonical_succinct_bytes(" in source
    assert "pub fn verify_governed_exact_succinct_bytes(" in source
    assert "\n    fn verify_canonical_succinct_bytes(" in source
    assert "\n    fn verify_exact_succinct_bytes(" in source
    assert "PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6" in source
