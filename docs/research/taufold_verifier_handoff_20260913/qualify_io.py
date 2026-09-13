"""Independent synthetic transport controls; these scripts prove no computation."""
import argparse
import hashlib
import json
import sys
import tempfile
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.source/'zkvm/adapters/python'))
    from taufold_adapters.context import BoundRequest
    from taufold_adapters.verifier import NativeVerifier, VerificationRejected

    request = BoundRequest.create('guard', {'budget': 10, 'amount': 1, 'risk_limit': 5},
                                  project='zenodex', deployment='transport-control',
                                  pre_state=bytes(32), command=bytes(32), nonce=1,
                                  input_commitment=bytes(32))
    value = dict(status='verified', output=0, public_memory=[], steps=1,
                 guest_image_id=[0]*8, input_commitment=[0]*32,
                 program_sha256=[0]*32, specification_sha256=[0]*32,
                 receipt_sha256=[0]*32)
    records = []

    def invoke(response, *, flood_fd=None):
        with tempfile.TemporaryDirectory(prefix='taufold-io-control-') as tmp:
            child = Path(tmp)/'synthetic-verifier'
            marker = Path(tmp)/'after-limit-marker'
            code = '#!/usr/bin/env python3\nimport os,sys\nsys.stdin.buffer.read()\n'
            if flood_fd is not None:
                # A pipe larger than the acceptance ceiling is essential to
                # distinguish late rejection from stopping consumption at it.
                code += f"data=b' '*(8<<20)\nwhile data:\n n=os.write({flood_fd},data)\n data=data[n:]\n"
                code += f"open({str(marker)!r},'wb').close()\n"
            framed = response + b'\n'  # native serde JSON followed by println!'s newline
            code += f'os.write(1,{framed!r})\n'
            child.write_text(code)
            child.chmod(0o700)
            verifier = NativeVerifier(child, hashlib.sha256(child.read_bytes()).digest())
            try:
                evidence = verifier.verify(request, b'{}')
            except VerificationRejected:
                return 'typed_rejection', marker.exists(), None
            except Exception as error:
                return type(error).__name__, marker.exists(), None
            return 'accepted', marker.exists(), evidence.output

    def check(name, response, *, flood_fd=None, allow=False):
        status, marker, output = invoke(response, flood_fd=flood_fd)
        passed = (status == 'accepted' and output == 0) if allow else status == 'typed_rejection'
        if flood_fd is not None:
            passed = passed and not marker
        records.append(dict(name=name, passed=passed, status=status,
                            child_reached_after_limit_marker=marker, output=output))

    encoded = json.dumps(value).encode()
    check('valid_complete_response_preserves_negative_business_result', encoded, allow=True)
    check('stdout_limit_stops_child_before_post_flood_marker', encoded, flood_fd=1)
    check('stderr_limit_stops_child_before_post_flood_marker', encoded, flood_fd=2)
    check('boolean_byte_alias_rejected', json.dumps(dict(value, input_commitment=[False]*32)).encode())
    check('floating_step_count_rejected', json.dumps(dict(value, steps=1.0)).encode())
    check('unknown_field_rejected', json.dumps(dict(value, extra=1)).encode())
    check('duplicate_status_rejected', encoded.replace(b'{', b'{"status":"forged",', 1))
    check('malformed_hash_typed_rejection', json.dumps(dict(value, program_sha256=[-1]*32)).encode())
    check('deep_json_typed_rejection', b'['*1500+b'0'+b']'*1500)
    source = args.source/'zkvm/adapters/python/taufold_adapters'
    report = dict(format='taufold-independent-transport-replay-v1',
                  cryptographic_evidence=False, cases=records,
                  passed=all(r['passed'] for r in records),
                  source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in sorted(source.glob('*.py'))},
                  test_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))
    return 0 if report['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
