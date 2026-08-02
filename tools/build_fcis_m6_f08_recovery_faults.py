"""Run the independent F08 recovery-fault checker and vector gate."""

from __future__ import annotations

import argparse

from experiments.fcis_m6_f08_recovery_faults_check import run_checks


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="run the deterministic source-vector comparison (the default)",
    )
    parser.parse_args()
    result = run_checks(check_vector=True)
    print("F08_RECOVERY_FAULT_VECTOR_MATCH", result["fault_count"])


if __name__ == "__main__":
    main()
