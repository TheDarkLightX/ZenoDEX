from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
METHODS = REPO_ROOT / "zk/zrpf_risc0/methods"
V6_METHODS = REPO_ROOT / "zk/zrpf_risc0/spot_v6_methods"


def _source(method: str) -> str:
    return (METHODS / method / "src/main.rs").read_text(encoding="utf-8")


def test_v6_l1_and_l2_verify_every_exact_child_before_composition() -> None:
    for method, image, compose in (
        (
            "spot_value_aggregate_l1_v6",
            "PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6",
            "compose_source_opened_spot_value_aggregate_level_one_after_receipt_verification_v6",
        ),
        (
            "spot_value_aggregate_l2_v6",
            "PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6",
            "compose_value_aggregate_level_two_after_receipt_verification_v5",
        ),
    ):
        source = _source(method)
        capability = source[
            source.index("pub(super) struct ReceiptVerified") : source.index("pub fn main()")
        ]
        assert re.search(rf"env::verify\(\s*{image},", capability)
        assert "for child_" in capability
        assert capability.index("env::verify(") < capability.index(compose)
        assert "expected_self_image_id" not in source
        assert "receipt_valid" not in source


def test_v6_settlement_verifies_l2_before_binding_source_or_composing() -> None:
    source = _source("source_opened_spot_settlement_v6")
    authenticate = source[
        source.index("pub(super) fn authenticate(") : source.index(
            "pub(super) fn compose(", source.index("pub(super) fn authenticate(")
        )
    ]
    markers = (
        "env::verify(",
        "derive_risc0_verified_claim_binding_v1(",
        "bind_source_opened_spot_settlement_guest_input_after_l2_receipt_verification_v3(",
    )
    positions = [authenticate.index(marker) for marker in markers]
    assert positions == sorted(positions)
    assert "PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6" in authenticate
    assert "expected_self_image_id" not in source
    assert "receipt_valid" not in source


def test_all_v6_successor_methods_have_fail_closed_host_placeholders() -> None:
    manifest = (V6_METHODS / "Cargo.toml").read_text(encoding="utf-8")
    build = (V6_METHODS / "build.rs").read_text(encoding="utf-8")
    for method, constant in (
        ("spot_value_aggregate_l1_v6", "SPOT_VALUE_AGGREGATE_L1_V6"),
        ("spot_value_aggregate_l2_v6", "SPOT_VALUE_AGGREGATE_L2_V6"),
        ("source_opened_spot_settlement_v6", "SOURCE_OPENED_SPOT_SETTLEMENT_V6"),
    ):
        assert f'"../methods/{method}"' in manifest
        assert f"ZENODEX_ZRPF_RISC0_{constant}_ELF: &[u8] = &[];" in build
        assert f"ZENODEX_ZRPF_RISC0_{constant}_ID: [u32; 8] = [0; 8];" in build
