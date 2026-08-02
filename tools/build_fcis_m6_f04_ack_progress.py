"""Run the independent F04A acknowledgment-progress checker and vector gate."""

from __future__ import annotations

import argparse

from experiments.fcis_m6_f04_ack_progress_check import run_checks


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="run the deterministic source-vector comparison (the default)",
    )
    parser.parse_args()
    result = run_checks(check_vector=True)
    print("F04A_ACK_PROGRESS_VECTOR_MATCH", result["completed_status"])


if __name__ == "__main__":
    main()
