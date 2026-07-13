from __future__ import annotations

import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
HISTORICAL = REPO / "zk/recursive_stark_v2_risc0/harness/src/main.rs"
ACTIVE = REPO / "zk/recursive_stark_v2_active_reproof_risc0/src/main.rs"

EXPECTED_ACTIVE_IDS = {
    "PERPS_NP": [
        1_325_857_952,
        1_200_767_500,
        578_985_275,
        1_399_309_097,
        301_662_771,
        3_103_620_299,
        2_267_820_869,
        1_804_992_208,
    ],
    "SPOT": [
        2_148_242_265,
        2_454_778_583,
        2_329_474_620,
        837_039_275,
        4_130_684_675,
        2_620_605_187,
        4_197_967_671,
        2_877_129_776,
    ],
    "ZUSD": [
        316_527_895,
        2_398_178_439,
        2_475_032_828,
        3_385_441_104,
        1_721_318_580,
        1_462_367_529,
        2_350_542_569,
        4_023_247_203,
    ],
}


def _algorithm_body(source: str) -> str:
    marker = "#[derive(Clone, Copy)]\nstruct LeafSurface"
    _, separator, suffix = source.partition(marker)
    assert separator == marker
    return separator + suffix


def _without_supplied_order_observability(source: str) -> str:
    deltas = (
        (
            "    let supplied_leaf_receipt_sha256s = verified_leaves\n"
            "        .iter()\n"
            "        .map(|leaf| receipt_sha256(&leaf.receipt))\n"
            "        .collect::<Result<Vec<_>, _>>()?;\n",
            1,
        ),
        ("            &supplied_leaf_receipt_sha256s,\n", 1),
        ("        &supplied_leaf_receipt_sha256s,\n", 1),
        ("    supplied_leaf_receipt_sha256s: &[String],\n", 1),
        (
            '            "supplied_leaf_receipt_sha256s": supplied_leaf_receipt_sha256s,\n',
            1,
        ),
    )
    normalized = source
    for delta, expected_count in deltas:
        assert normalized.count(delta) == expected_count
        normalized = normalized.replace(delta, "")
    return normalized


def _image_id_words(source: str, surface: str) -> list[int]:
    match = re.search(
        rf"const PINNED_V1_{surface}_LEAF_ID: \[u32; 8\] = \[([^]]+)\];",
        source,
    )
    assert match is not None
    return [
        int(word.replace("_", "").strip()) for word in match.group(1).split(",") if word.strip()
    ]


def test_active_reproof_harness_changes_only_the_governed_identity_preamble() -> None:
    historical = HISTORICAL.read_text(encoding="utf-8")
    active = ACTIVE.read_text(encoding="utf-8")

    assert _algorithm_body(_without_supplied_order_observability(active)) == _algorithm_body(
        historical
    )
    assert (
        active[: active.index("const DEFAULT_INNER_OUTPUT")]
        == historical[: historical.index("const DEFAULT_INNER_OUTPUT")]
    )


def test_active_reproof_harness_records_supplied_order_before_canonical_sort() -> None:
    active = ACTIVE.read_text(encoding="utf-8")

    capture = active.index("let supplied_leaf_receipt_sha256s = verified_leaves")
    canonical_sort = active.index("verified_leaves.sort_by")
    assert capture < canonical_sort
    assert '"supplied_leaf_receipt_sha256s": supplied_leaf_receipt_sha256s' in active


def test_active_reproof_harness_pins_the_current_v1_guest_ids() -> None:
    active = ACTIVE.read_text(encoding="utf-8")

    assert {
        surface: _image_id_words(active, surface) for surface in EXPECTED_ACTIVE_IDS
    } == EXPECTED_ACTIVE_IDS
    assert "Historical proof\n// harnesses retain their older IDs" in active


def test_active_pair_verifier_preserves_security_anchors_and_pins_governed_id() -> None:
    historical = REPO / "zk/recursive_stark_v2_risc0/harness/src/bin/verify_recursive_v2_pair.rs"
    active = REPO / "zk/recursive_stark_v2_active_reproof_risc0/src/bin/verify_recursive_v2_pair.rs"

    active_text = active.read_text(encoding="utf-8")
    historical_text = historical.read_text(encoding="utf-8")
    for shared_security_anchor in (
        "artifact journal does not match the authenticated journal",
        "epoch root does not bind the supplied inner receipt journal",
        "epoch root immediate verifier set mismatch",
    ):
        assert shared_security_anchor in active_text
        assert shared_security_anchor in historical_text

    assert ".verify(GOVERNED_AGGREGATE_V2_ID)" in active_text
    assert ".verify(TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID)" in historical_text
    assert "tau_state_proof_risc0_recursive_v2_methods" not in active_text
    assert "const GOVERNED_AGGREGATE_V2_ID: [u32; 8]" in active_text

    assert "has_exact_active_two_leaf_topology" in active_text
    assert "journal.immediate_child_count != 1" in historical_text
    assert "journal.flat_leaf_count != 1" in historical_text
