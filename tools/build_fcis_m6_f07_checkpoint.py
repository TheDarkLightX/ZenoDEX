"""Run the independent F07 checkpoint checker and vector gate."""

from __future__ import annotations

import argparse

from experiments.fcis_m6_f07_checkpoint_check import run_checks


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="run the deterministic source-vector comparison (the default)",
    )
    parser.parse_args()
    result = run_checks(check_vector=True)
    print("F07_CHECKPOINT_VECTOR_MATCH", result["checkpoint_genesis_root"])


if __name__ == "__main__":
    main()
