"""Validate a companion packet with one optional trailing letter in its ID."""

from __future__ import annotations

import re
import sys

import validate_task_packet as _validator

_validator._TASK_ID = re.compile(r"^[A-Z]+[0-9]+[A-Z]?$")


if __name__ == "__main__":
    raise SystemExit(_validator.main(sys.argv))
