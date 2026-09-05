"""Always-run coherence gate over the pinned ASSET_TRANSFER child image ID.

The asset lane coordinator guest recursively verifies its child with
``env::verify(ASSET_TRANSFER_MODULE_IMAGE_ID_V1, ..)``. That constant is a
*source* pin, and the repository keeps three independent copies of it: the Rust
constant, the ``GUESTS`` table in the isolated BLS proof preparation tool, and
the ASSET_TRANSFER lane release in the frozen proof seed. This suite checks
agreement of those copies and detects a pin edit that leaves a recorded
source or fixture value stale.

NONCLAIM: this suite reads source and frozen data only. It never observes built
method bytes, so it cannot and does not certify that the built child guest ELF
hashes to this image ID. That equality is only observable from a real methods
build, and is gated by
``zk/asset_lane_coordinator_risc0/host/tests/real_composition.rs::
linked_child_method_id_matches_the_pinned_coordinator_child_image``.

NONCLAIM: the coordinator's own image ID is a build output with no source pin,
so the ``GUESTS["coordinator"]`` entry is a recorded observation, not a pin, and
is deliberately not asserted here.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

import pytest

from tools import prepare_isolated_bls_proof_v1 as builder

REPO = Path(__file__).resolve().parents[2]
SHARED_SOURCE = REPO / "zk/asset_lane_coordinator_risc0/shared/src/lib.rs"
GUEST_SOURCE = REPO / "zk/asset_lane_coordinator_risc0/methods/guest/src/main.rs"
HOST_SOURCE = REPO / "zk/asset_lane_coordinator_risc0/host/src/lib.rs"
PIN_NAME = "ASSET_TRANSFER_MODULE_IMAGE_ID_V1"
WORD_COUNT = 8
U32_CEILING = 1 << 32


def parse_pinned_child_image_words_v1(source: str) -> list[int]:
    """Parse the pinned child image ID out of the shared crate source.

    Fail-closed: a missing, malformed, out-of-width or all-zero pin raises
    rather than degrading to a weaker comparison.
    """
    match = re.search(
        rf"pub const {PIN_NAME}: \[u32; {WORD_COUNT}\] = \[(?P<words>[^]]*)\];", source
    )
    if match is None:
        raise ValueError(f"{PIN_NAME} pin not found in shared crate source")
    words = [
        int(part.strip().replace("_", "")) for part in match["words"].split(",") if part.strip()
    ]
    if len(words) != WORD_COUNT:
        raise ValueError(f"{PIN_NAME} must pin exactly {WORD_COUNT} words, found {len(words)}")
    if any(word < 0 or word >= U32_CEILING for word in words):
        raise ValueError(f"{PIN_NAME} word out of u32 width")
    if all(word == 0 for word in words):
        raise ValueError(f"{PIN_NAME} is all-zero, which disables the child image check")
    return words


def image_root_hex_v1(words: list[int]) -> str:
    """Mirror ``image_id_root_v1``: little-endian bytes per word, hex encoded."""
    return b"".join(word.to_bytes(4, "little") for word in words).hex()


@pytest.fixture(scope="module")
def pinned_words() -> list[int]:
    return parse_pinned_child_image_words_v1(SHARED_SOURCE.read_text(encoding="utf-8"))


def test_pinned_child_image_is_the_image_the_guest_recursively_verifies(pinned_words):
    # Arrange
    guest = GUEST_SOURCE.read_text(encoding="utf-8")
    host = HOST_SOURCE.read_text(encoding="utf-8")

    # Act / Assert: the guest's single recursive verification takes the pin as a
    # literal argument, never a caller-supplied or journal-carried image ID.
    assert re.findall(r"env::verify\(\s*([A-Za-z_][A-Za-z0-9_]*)", guest) == [PIN_NAME]
    # The host rejects child receipts against the same pin.
    assert f".verify({PIN_NAME})" in host
    assert len(pinned_words) == WORD_COUNT


def test_rust_pin_matches_the_bls_preparation_guest_table(pinned_words):
    # Arrange
    expected = "0x" + image_root_hex_v1(pinned_words)

    # Act / Assert
    assert builder.GUESTS["module"][0] == expected


def test_rust_pin_matches_the_frozen_asset_transfer_lane_release(pinned_words):
    # Arrange
    seed = json.loads((REPO / builder.SEED_FILE).read_text(encoding="utf-8"))
    releases = [row for row in seed["lanes"]["releases"] if row["lane_id"] == "ASSET_TRANSFER"]

    # Act / Assert
    assert len(releases) == 1
    assert releases[0]["guest_image_id"] == "0x" + image_root_hex_v1(pinned_words)


def test_root_encoding_is_little_endian_per_word_and_drift_sensitive(pinned_words):
    # Arrange
    big_endian = b"".join(word.to_bytes(4, "big") for word in pinned_words).hex()
    drifted = list(pinned_words)
    drifted[-1] ^= 1

    # Act / Assert: negative controls on the encoder this gate depends on.
    assert image_root_hex_v1(pinned_words) != big_endian
    assert image_root_hex_v1(drifted) != image_root_hex_v1(pinned_words)
    assert len(image_root_hex_v1(pinned_words)) == 64


@pytest.mark.parametrize(
    ("source", "reason"),
    (
        ("", "pin not found"),
        (f"pub const {PIN_NAME}: [u32; 8] = [0, 0, 0, 0, 0, 0, 0, 0];", "all-zero"),
        (f"pub const {PIN_NAME}: [u32; 8] = [1, 2, 3];", "exactly 8 words"),
        (f"pub const {PIN_NAME}: [u32; 8] = [4294967296, 2, 3, 4, 5, 6, 7, 8];", "u32 width"),
    ),
)
def test_pin_parser_rejects_missing_zeroed_short_and_overwide_pins(source, reason):
    # Act / Assert
    with pytest.raises(ValueError, match=reason):
        parse_pinned_child_image_words_v1(source)
