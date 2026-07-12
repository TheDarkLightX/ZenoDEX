from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
from pathlib import Path

import pytest

from tools.build_perp_partial_liquidation_semantics_v1 import (
    DEFAULT_CORPUS,
    DEFAULT_MANIFEST,
    expected_artifacts,
)
from tools.check_perp_partial_liquidation_semantics_v1 import (
    JULIA_REPLAY,
    check_semantics_v1,
)


def test_checked_in_corpus_is_source_pinned_to_live_python_runtime() -> None:
    report = check_semantics_v1(require_julia=False, require_lean=False)

    assert report["ok"] is True
    assert report["claim_scope"] == "artifact_and_python_runtime_only"
    assert report["case_count"] == 2_160
    assert report["backends"]["python_runtime"]["status"] == "passed"
    assert report["backends"]["julia"]["status"] == "not_run"
    assert report["backends"]["lean"]["status"] == "not_run"


def test_corpus_exposes_zero_margin_dust_position() -> None:
    rows = DEFAULT_CORPUS.read_text(encoding="ascii").splitlines()
    columns = rows[1].split("\t")
    first_case = dict(zip(columns, rows[2].split("\t"), strict=True))

    assert first_case["position_base"] == "1"
    assert first_case["collateral_after_pnl"] == "0"
    assert first_case["settle_price_e8"] == "100000000"
    assert first_case["maintenance_margin_bps"] == "500"
    assert first_case["liquidatable"] == "0"
    assert first_case["selected_fraction_bps"] == "0"


def test_checker_rejects_corpus_drift(tmp_path: Path) -> None:
    corpus, manifest = expected_artifacts()
    corpus_path = tmp_path / "corpus.tsv"
    manifest_path = tmp_path / "manifest.json"
    corpus_path.write_bytes(corpus.replace(b"\t0\n", b"\t1\n", 1))
    manifest_path.write_bytes(manifest)

    report = check_semantics_v1(
        corpus_path=corpus_path,
        manifest_path=manifest_path,
        require_julia=False,
        require_lean=False,
    )

    assert report["ok"] is False
    assert "corpus differs from live Python runtime regeneration" in report["errors"]


def test_checker_rejects_manifest_or_source_hash_drift(tmp_path: Path) -> None:
    corpus, manifest = expected_artifacts()
    payload = json.loads(manifest)
    payload["known_nonmonotone_witness"]["selected_fraction_bps"] = 7_710
    corpus_path = tmp_path / "corpus.tsv"
    manifest_path = tmp_path / "manifest.json"
    corpus_path.write_bytes(corpus)
    manifest_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    report = check_semantics_v1(
        corpus_path=corpus_path,
        manifest_path=manifest_path,
        require_julia=False,
        require_lean=False,
    )

    assert report["ok"] is False
    assert "manifest differs from source-pinned regeneration" in report["errors"]


def test_julia_replay_rejects_a_tampered_expected_fraction(tmp_path: Path) -> None:
    julia = shutil.which("julia")
    if not julia:
        pytest.skip("Julia executable is missing")
    corpus = DEFAULT_CORPUS.read_bytes()
    lines = corpus.decode("ascii").splitlines()
    fields = lines[2].split("\t")
    fields[-1] = str(int(fields[-1]) + 1)
    lines[2] = "\t".join(fields)
    tampered = ("\n".join(lines) + "\n").encode("ascii")
    corpus_path = tmp_path / "corpus.tsv"
    corpus_path.write_bytes(tampered)
    digest = hashlib.sha256(tampered).hexdigest()

    proc = subprocess.run(
        [julia, str(JULIA_REPLAY), str(corpus_path), digest],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=180,
        check=False,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert any("selected fraction mismatch" in error for error in report["errors"])


def test_default_artifact_paths_are_the_versioned_v1_bundle() -> None:
    assert DEFAULT_CORPUS.name == "corpus.tsv"
    assert DEFAULT_MANIFEST.name == "manifest.json"
    assert DEFAULT_CORPUS.parent.name == "perp_partial_liquidation_semantics_v1"
