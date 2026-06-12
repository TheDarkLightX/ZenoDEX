"""Guard the OCaml spec-oracle vectors against authority drift.

The OCaml oracle (`ocaml-runtime/`) reads committed TSV vectors generated from
the Python authority. This test re-derives them and asserts the committed files
are byte-identical, so the oracle can never silently test against stale vectors.
It needs no OCaml toolchain; `dune test` is the separate OCaml-side gate.
"""

from __future__ import annotations

import sys
from pathlib import Path

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

from tools.runtime import ocaml_spec_vectors as osv


def test_committed_vectors_match_authority():
    rc = osv.main(["--check"])
    assert rc == 0, "OCaml spec vectors are stale; run tools/runtime/ocaml_spec_vectors.py"


def test_vectors_exist_and_have_rows():
    for name in ("fee_router.tsv", "replay_guard.tsv"):
        path = osv._VECTORS_DIR / name
        assert path.is_file(), f"missing {path}"
        lines = path.read_text(encoding="utf-8").splitlines()
        assert len(lines) >= 2, f"{name} has no data rows"
