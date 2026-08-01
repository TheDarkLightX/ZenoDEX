"""Fail-closed command for the FCIS M6 J06 quiescence vector."""

from __future__ import annotations

import sys

from experiments.fcis_m6_j06_quiescence_check import run_checks


def main(argv: list[str]) -> int:
    if len(argv) != 1:
        print("usage: check_fcis_m6_j06_quiescence.py", file=sys.stderr)
        return 2
    try:
        run_checks()
    except (ValueError, TypeError, OSError) as exc:
        print(f"J06_QUIESCENCE_REJECT: {exc}", file=sys.stderr)
        return 1
    print("J06_QUIESCENCE_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
