from __future__ import annotations

import sys
from pathlib import Path


def _maybe_add_external_esso_to_syspath() -> None:
    """
    Make `python3 -m ESSO ...` work in this repo without requiring callers to set PYTHONPATH.

    This is a no-op if `external/ESSO` is not present.
    """

    repo_root = Path(__file__).resolve().parent
    external_esso = repo_root / "external" / "ESSO"
    if not external_esso.is_dir():
        return

    path = str(external_esso)
    if path not in sys.path:
        sys.path.insert(0, path)


_maybe_add_external_esso_to_syspath()

