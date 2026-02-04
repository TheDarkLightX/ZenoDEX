from __future__ import annotations

import sys
from pathlib import Path


def _maybe_add_external_esso_to_syspath() -> None:
    """
    Make the optional private toolchain importable without requiring callers to set PYTHONPATH.

    This is a no-op if the toolchain is not present under `external/` (git-ignored).
    """

    repo_root = Path(__file__).resolve().parent
    external_esso = repo_root / "external" / "ESSO"
    if not external_esso.is_dir():
        return

    path = str(external_esso)
    if path not in sys.path:
        sys.path.insert(0, path)


_maybe_add_external_esso_to_syspath()
