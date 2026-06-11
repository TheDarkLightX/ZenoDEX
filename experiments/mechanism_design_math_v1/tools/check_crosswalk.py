#!/usr/bin/env python3
"""Check the mechanism-design obligation crosswalk."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "experiments" / "mechanism_design_math_v1"
CHARTER = ROOT / "docs" / "ZENODEX_MECHANISM_DESIGN_AND_MATH.md"
CROSSWALK = BASE / "CROSSWALK.md"


def _obligations_from_charter() -> set[str]:
    text = CHARTER.read_text(encoding="utf-8")
    return set(re.findall(r"`?(O-(?:SS|SB|PT|VM)-\d{2})`?", text))


def _obligations_from_crosswalk() -> set[str]:
    text = CROSSWALK.read_text(encoding="utf-8")
    return set(re.findall(r"`(O-(?:SS|SB|PT|VM)-\d{2})`", text))


def main() -> int:
    charter = _obligations_from_charter()
    crosswalk = _obligations_from_crosswalk()
    missing = sorted(charter - crosswalk)
    extra = sorted(crosswalk - charter)
    if missing or extra:
        if missing:
            print("missing crosswalk obligations:")
            for item in missing:
                print(f"  {item}")
        if extra:
            print("extra crosswalk obligations:")
            for item in extra:
                print(f"  {item}")
        return 1
    print("crosswalk ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
