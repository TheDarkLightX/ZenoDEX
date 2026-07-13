from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "tools" / "check_zrpf_v1_leaf_adapter_vector.py"


def _load_checker():
    spec = importlib.util.spec_from_file_location(
        "check_zrpf_v1_leaf_adapter_vector", CHECKER
    )
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_reference_vector_matches_every_pinned_adapter_value() -> None:
    checker = _load_checker()

    report = checker.check()

    assert report["ok"] is True
    assert report["vector"] == checker.EXPECTED_VECTOR
    assert all(report["checks"].values())


def test_source_statement_mutation_breaks_the_pinned_downstream_vector() -> None:
    checker = _load_checker()
    changed_statement = bytearray(bytes([1]) * 32)
    changed_statement[0] ^= 1

    original = checker.reference_vector()
    changed = checker.reference_vector(bytes(changed_statement))
    report = checker.check(bytes(changed_statement))

    assert report["ok"] is False
    for field in (
        "source_journal_sha256",
        "source_journal_hash",
        "source_claim_hash",
        "source_effect_hash",
        "source_binding_hash",
        "task_id",
        "commitments_hash",
        "node_statement_hash",
        "journal_hash",
        "v3_postcard_sha256",
    ):
        assert changed[field] != original[field]
        assert report["checks"][field] is False

    for stable_identity in (
        "source_verifier_id",
        "source_scope_hash",
        "source_manifest_root",
        "count_unit_id",
        "adapter_manifest_root",
        "v3_verifier_id",
    ):
        assert changed[stable_identity] == original[stable_identity]


def test_noncanonical_image_word_endianness_changes_source_identity() -> None:
    checker = _load_checker()

    canonical_program_id = checker._risc0_program_id(checker.SOURCE_IMAGE_ID_WORDS)
    big_endian_words = checker._v1_image_words(checker.SOURCE_IMAGE_ID_WORDS)

    assert canonical_program_id.hex() == (
        "1275ef413f6513e7671bce019d22fbdcf10bffe1b71dcf68731a056e710a7403"
    )
    assert canonical_program_id != big_endian_words
