#!/usr/bin/env python3
"""Fail-closed checker for the proof-market EconomicWorkKey golden vector."""

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]


def _run() -> int:
    sys.path.insert(0, str(REPO_ROOT))
    from tools.proof_market_key_parity_v2 import main

    return main()


if __name__ == "__main__":
    raise SystemExit(_run())
