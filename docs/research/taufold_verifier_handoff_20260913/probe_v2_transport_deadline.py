"""Deterministic late-exit probe; transport evidence, not a receipt proof."""
import argparse
import json
import os
import signal
import subprocess
import sys
from hashlib import sha256
from pathlib import Path
from unittest.mock import patch

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source', type=Path, required=True)
parser.add_argument('--report', type=Path, required=True)
args = parser.parse_args()
sys.path.insert(0, str(args.source / 'zkvm/adapters/python'))
from taufold_adapters import process as transport  # noqa: E402

clock = {'now': 0.0}
real_waitid = os.waitid


def observe_exit(*args):
    observed = real_waitid(*args)
    if observed is not None:
        clock['now'] = 61.0
    return observed


child = subprocess.Popen(['/bin/cat'], stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         bufsize=0, start_new_session=True)
try:
    with patch.object(transport.time, 'monotonic', side_effect=lambda: clock['now']), \
            patch.object(transport.os, 'waitid', side_effect=observe_exit):
        try:
            output, errors = transport._exchange(child, b'completed\n', 60.0)
            outcome = 'accepted' if output == b'completed\n' and not errors else 'unexpected_output'
        except transport.ProcessRejected as error:
            outcome = error.reason.value
finally:
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    child.wait()
    for stream in (child.stdin, child.stdout, child.stderr):
        stream.close()

report = {'source_sha256': sha256(Path(transport.__file__).read_bytes()).hexdigest(),
          'deadline_seconds': 60, 'observed_completion_seconds': clock['now'],
          'outcome': outcome, 'deadline_contract_violated': outcome != 'deadline',
          'cryptographic_evidence': False, 'external_effects': 0}
args.report.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
raise SystemExit(1 if report['deadline_contract_violated'] else 0)
