"""Independent replay: real guard proof, actual host intent, hostile execution path.

The fixture state/commitment is synthetic and independently retained. This
does not authenticate live spending, consume a nonce, or publish a transition.
Only executable copies inside a fresh temporary directory are modified.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from unittest.mock import patch


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--verifier', type=Path, required=True)
    parser.add_argument('--host', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    sys.path[:0] = [str(args.source/'zkvm/adapters/python'),
                   str(args.source/'zkvm/tools'), str(args.host)]
    from advanced_examples import DEPLOYMENT, INTENT, PRE_STATE
    from taufold_adapters.verifier import NativeVerifier, VerificationRejected
    from taufold_adapters.zenodex import swap_guard_request

    from src.state.intents import IntentKind, SwapIntent

    raw = (args.source/'zkvm/examples/proofs/guard.bundle.json').read_bytes()
    commitment = bytes(json.loads(raw)['claim']['input_commitment'])
    intent = SwapIntent(**dict(INTENT, kind=IntentKind.SWAP_EXACT_IN))
    expectations = dict(budget=100000, risk_limit=50, deployment=DEPLOYMENT,
                        pre_state=PRE_STATE, nonce=1, input_commitment=commitment)
    request = swap_guard_request(intent, **expectations)
    pin = hashlib.sha256(args.verifier.read_bytes()).digest()
    verifier = NativeVerifier(args.verifier, pin)
    records = []

    def rejects(fn):
        try:
            fn()
        except VerificationRejected:
            return
        raise AssertionError('unacceptable evidence was admitted')

    def case(name, fn):
        start = time.monotonic()
        try:
            fn()
        except Exception as error:
            records.append(dict(name=name, passed=False, error=type(error).__name__,
                                detail=str(error), seconds=time.monotonic()-start))
        else:
            records.append(dict(name=name, passed=True, seconds=time.monotonic()-start))

    def genuine():
        evidence = verifier.verify(request, raw)
        if evidence.output != 1 or evidence.input_commitment != commitment:
            raise AssertionError('fixed genuine guard result changed')
        if evidence.encode() != verifier.verify(request, raw).encode():
            raise AssertionError('exact proof retry changed evidence')

    def substituted(field, value):
        altered = swap_guard_request(intent, **dict(expectations, **{field: value}))
        rejects(lambda: verifier.verify(altered, raw))

    def changed_recipient():
        altered = swap_guard_request(intent.with_field('recipient', 'mallory'), **expectations)
        rejects(lambda: verifier.verify(altered, raw))

    def replacement(mode):
        # The pinned verifier is genuine. Swap its owned path at the last
        # boundary before process creation, after any measurement/sealing.
        with tempfile.TemporaryDirectory(prefix='taufold-exec-control-') as tmp:
            path = Path(tmp)/'verifier'
            shutil.copy2(args.verifier, path)
            checked = NativeVerifier(path, pin)
            fake = dict(status='verified', output=1, public_memory=[], steps=1,
                        guest_image_id=[0]*8, input_commitment=list(commitment),
                        program_sha256=[0]*32, specification_sha256=[0]*32,
                        receipt_sha256=[0]*32)
            encoded = json.dumps(fake, separators=(',', ':'))
            hostile = ("#!/bin/sh\nprintf '%s' '" + encoded + "'\n").encode()
            original_popen = subprocess.Popen
            launches = []

            def launch(*popen_args, **popen_kwargs):
                launches.append(True)
                if mode == 'replace':
                    other = Path(tmp)/'replacement'
                    other.write_bytes(hostile)
                    other.chmod(0o700)
                    os.replace(other, path)
                else:
                    path.write_bytes(hostile)
                return original_popen(*popen_args, **popen_kwargs)

            with patch('subprocess.Popen', side_effect=launch):
                rejects(lambda: checked.verify(request, b'{}'))
            if len(launches) != 1:
                raise AssertionError('attack did not reach process creation')

    case('genuine_receipt_actual_swap_intent_and_exact_retry', genuine)
    case('counterfeit_receipt_rejected_without_path_attack',
         lambda: rejects(lambda: verifier.verify(request, b'{}')))
    case('wrong_recipient_rejected', changed_recipient)
    for field, value in [('deployment', 'foreign-deployment'), ('pre_state', bytes(32)),
                         ('nonce', 2), ('budget', 99999), ('input_commitment', bytes(32))]:
        case('changed_' + field + '_rejected', lambda f=field, v=value: substituted(f, v))
    case('path_replacement_cannot_admit_counterfeit_proof', lambda: replacement('replace'))
    case('in_place_mutation_cannot_admit_counterfeit_proof', lambda: replacement('in_place'))
    report = dict(format='taufold-zenodex-independent-boundary-replay-v1',
                  source=str(args.source), executable_sha256=pin.hex(),
                  source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in sorted((args.source/'zkvm/adapters/python/taufold_adapters').glob('*.py'))},
                  test_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  genuine_receipt_sha256=hashlib.sha256(raw).hexdigest(),
                  host_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                                                    cwd=args.host, text=True).strip(),
                  cases=records, passed=all(r['passed'] for r in records),
                  authenticated_live_state=False, publication_authority=False,
                  state_changes=0, external_effects=0)
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
