#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path

import check_runtime_shell_assurance_manifest as base


base.DEFAULT_MANIFEST = Path(__file__).resolve().parents[1] / "tools" / "spot_core_shell_assurance_manifest.json"


if __name__ == "__main__":
    raise SystemExit(base.main())
