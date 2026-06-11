#!/usr/bin/env python3
"""Manually normalize evidence files to the canonical schema.

Thin CLI wrapper over the same normalization logic the program's conftest.py
runs automatically at pytest session end. Useful when evidence files are
edited outside a pytest session.
"""

import importlib.util
import sys
from pathlib import Path

BASE = Path(__file__).parent


def _load_conftest():
    spec = importlib.util.spec_from_file_location(
        "mdm_conftest", BASE / "conftest.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main() -> int:
    conftest = _load_conftest()
    patterns = [
        "wave*_*/evidence/results.json",
        "wave*_formal/results.json",
    ]
    count = 0
    for pattern in patterns:
        for path in sorted(BASE.glob(pattern)):
            conftest._normalize_file(path)
            conftest._apply_cross_wave_overrides_to_file(path)
            print(f"normalized: {path.relative_to(BASE)}")
            count += 1
    if count == 0:
        print("no evidence files found", file=sys.stderr)
        return 1
    print(f"{count} files normalized")
    return 0


if __name__ == "__main__":
    sys.exit(main())
