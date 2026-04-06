#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path

import check_zusd_repay_assurance_manifest as base


base.DEFAULT_MANIFEST = Path(__file__).resolve().parents[1] / "tools" / "dex_intent_auth_shape_assurance_manifest.json"


if __name__ == "__main__":
    raise SystemExit(base.main())
