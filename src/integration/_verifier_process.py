"""Observe an owned verifier's exit without releasing its process-group ID.

The caller must exclusively own child reaping and kill the group before wait().
This contains same-group descendants; it does not contain session escape.
"""

from __future__ import annotations

import os
import select
import subprocess
import time


def unreaped_exit_status(process_id: int) -> int | None:
    result = os.waitid(os.P_PID, process_id, os.WEXITED | os.WNOHANG | os.WNOWAIT)
    if result is None:
        return None
    return result.si_status if result.si_code == os.CLD_EXITED else -result.si_status


def wait_for_unreaped_exit(process: subprocess.Popen[bytes], *, deadline: float) -> int:
    while True:
        status = unreaped_exit_status(process.pid)
        remaining = deadline - time.monotonic()
        # Even an already-exited child must have been observed before the deadline.
        if remaining <= 0:
            raise subprocess.TimeoutExpired(process.args, 0)
        if status is not None:
            return status
        select.select([], [], [], min(0.05, remaining))
