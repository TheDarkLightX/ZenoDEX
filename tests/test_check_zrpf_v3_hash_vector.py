from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "tools" / "check_zrpf_v3_hash_vector.py"


def _load_checker():
    spec = importlib.util.spec_from_file_location("check_zrpf_v3_hash_vector", CHECKER)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_reference_vector_matches_pinned_rust_fixture() -> None:
    checker = _load_checker()

    report = checker.check()

    assert report["ok"] is True
    assert report["commitments_hash"] == checker.EXPECTED_COMMITMENTS_HASH
    assert report["journal_hash"] == checker.EXPECTED_JOURNAL_HASH
    assert report["postcard_length"] == checker.EXPECTED_POSTCARD_LENGTH
    assert report["postcard_sha256"] == checker.EXPECTED_POSTCARD_SHA256


def test_reference_vector_detects_a_domain_change() -> None:
    checker = _load_checker()

    altered = checker._empty_list_root(b"zenodex.zrpf.child_tasks_root.v4")
    expected = checker._empty_list_root(b"zenodex.zrpf.child_tasks_root.v3")

    assert altered != expected
