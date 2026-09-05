#!/usr/bin/env bash
# Run on an already authorized CUDA host. No provisioning or tool installation.
# Usage: bash tools/run_whole_program_v3_remote_receipt_job.sh SOURCE_MANIFEST NEW_OUTPUT_DIR
set -euo pipefail
umask 077
if [[ $# != 2 ]]; then
  echo 'usage: remote_receipt_job.sh SOURCE_MANIFEST NEW_OUTPUT_DIR' >&2
  exit 2
fi
source_root=$(cd "$(dirname "$0")/.." && pwd -P)
source_manifest=$(realpath "$1")
output_dir=$(realpath -m "$2")
if [[ -e "$output_dir" || "$output_dir" != /* || ! -f "$source_manifest" ]]; then
  echo 'require a source manifest and a new absolute output directory' >&2
  exit 2
fi
cd "$source_root"
sha256sum --check --strict "$source_manifest"
mkdir "$output_dir"
cp "$source_manifest" "$output_dir/source.sha256"
exec > >(tee "$output_dir/job.log") 2>&1
unset RISC0_SKIP_BUILD RISC0_SKIP_BUILD_KERNELS RUSTC_WORKSPACE_WRAPPER RUSTC_WRAPPER CARGO_CFG_CLIPPY CLIPPY_ARGS
unset BONSAI_API_KEY BONSAI_API_URL RISC0_SERVER_PATH RISC0_R0VM_PATH
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS RISC0_RUST_SRC
export RISC0_DEV_MODE=0 RISC0_PROVER=local
export RUSTUP_TOOLCHAIN=1.90.0 RISC0_BUILD_LOCKED=1
export CARGO_BUILD_JOBS=8 CMAKE_BUILD_PARALLEL_LEVEL=8 RAYON_NUM_THREADS=8
export CARGO_PROFILE_RELEASE_DEBUG=0 CARGO_PROFILE_RELEASE_STRIP=debuginfo
export CARGO_INCREMENTAL=0 PYTHONDONTWRITEBYTECODE=1
export CARGO_TARGET_DIR="$output_dir/target"
export PATH="${HOME}/.cargo/bin:/usr/local/cuda/bin:/usr/bin:/bin"
export CUDA_VISIBLE_DEVICES=0
# Separate selection from any other job's rzup default. These public installed
# compiler bytes and the operating system remain part of the trusted toolchain.
guest_toolchain="${HOME}/.risc0/toolchains/v1.97.0-rust-x86_64-unknown-linux-gnu"
export RISC0_HOME="$output_dir/risc0"
mkdir -p "$RISC0_HOME/toolchains"
python3 - "$guest_toolchain" "$RISC0_HOME/toolchains" <<'PY'
import pathlib, sys
source = pathlib.Path(sys.argv[1])
target = pathlib.Path(sys.argv[2]) / source.name
target.mkdir()
# rzup excludes symlinks at the version-directory level.
for child in source.iterdir():
    (target / child.name).symlink_to(child, target_is_directory=child.is_dir())
PY
printf '[default_versions]\nrust = "1.97.0"\n' > "$RISC0_HOME/settings.toml"
python3 - "$guest_toolchain/bin/rustc" <<'PY'
import hashlib, pathlib, sys
expected = '288ee1994dd8ec08184686e7a52b779c9b075498ffe73003884fefe60389c351'
if hashlib.sha256(pathlib.Path(sys.argv[1]).read_bytes()).hexdigest() != expected:
    raise SystemExit('selected guest compiler executable drift')
PY
ulimit -f 2097152
for command in cargo rustup nvcc nvidia-smi timeout python3; do
  command -v "$command"
done
rustup run 1.90.0 rustc --version
"$guest_toolchain/bin/rustc" --version
nvcc --version
nvidia-smi --query-gpu=name,memory.total,driver_version --format=csv,noheader
python3 - "$output_dir" <<'PY'
import pathlib, shutil, sys
path = pathlib.Path(sys.argv[1])
if shutil.disk_usage(path).free < 40 * 1024**3:
    raise SystemExit('require at least 40 GiB free on the output filesystem')
PY

crate="$source_root/zk/global_economic_epoch_risc0"
package=zenodex-global-economic-epoch-risc0-host
cd "$crate"
# Preserve a verifier without CUDA dependencies before enabling CUDA for proving.
timeout --kill-after=30 3600 cargo build --locked --release -p "$package" \
  --bin verify_receipt_v1
cp "$CARGO_TARGET_DIR/release/verify_receipt_v1" "$output_dir/verify_receipt_v1"
sha256sum "$output_dir/verify_receipt_v1"
timeout --kill-after=30 3600 cargo test --locked --release -p "$package" \
  --features risc0-zkvm/cuda --test real_structural_bridge_export --no-run
export ZENODEX_STRUCTURAL_RECEIPT_OUTPUT="$output_dir/proofs"
timeout --kill-after=30 1800 cargo test --locked --release -p "$package" \
  --features risc0-zkvm/cuda --test real_structural_bridge_export \
  export_real_structural_epoch_bridge_receipts_v1 -- --exact --ignored --nocapture

cd "$source_root"
sha256sum --check --strict "$source_manifest"
python3 - "$output_dir" <<'PY'
import hashlib
import json
import pathlib
import struct
import subprocess
import sys
from src.integration.global_receipt_verifier_v1 import (
    GlobalReceiptVerifierErrorV1, GlobalReceiptVerifierV1,
)

output = pathlib.Path(sys.argv[1])
proofs = output / 'proofs'
metadata = json.loads((proofs / 'proof_metadata.json').read_bytes())
if metadata['asset_transfer_semantics_proved'] or metadata['publication_authority']:
    raise SystemExit('invalid structural claim scope')
image = metadata['epoch_image_id']
foreign_image = metadata['foreign_image_id']
journal = (proofs / 'epoch.journal').read_bytes()
receipt = (proofs / 'epoch.receipt').read_bytes()
binary = output / 'verify_receipt_v1'
digest = hashlib.sha256(binary.read_bytes()).hexdigest()
verifier = GlobalReceiptVerifierV1(str(binary), digest, image, 60000)
checks = []

def bridge_case(name, encoded, expected_journal, expected_image, rejection=None, adapter=verifier):
    try:
        adapter.verify_succinct_receipt(encoded, expected_image_id=expected_image,
                                       expected_journal_bytes=expected_journal)
        actual = 'ACCEPTED'
    except GlobalReceiptVerifierErrorV1 as error:
        actual = error.reason.value
    expected = rejection or 'ACCEPTED'
    if actual != expected:
        raise SystemExit(f'{name}: expected {expected}, got {actual}')
    checks.append({'name': name, 'result': actual})

bridge_case('real_epoch_exact_image_and_journal', receipt, journal, image)
bridge_case('wrong_journal', receipt, journal + b'\n', image, 'VERIFICATION_REJECTED')
bridge_case('wrong_requested_image', receipt, journal, foreign_image, 'IMAGE_BINDING')
foreign_adapter = GlobalReceiptVerifierV1(str(binary), digest, foreign_image, 60000)
bridge_case('wrong_configured_image_reaches_rust', receipt, journal, foreign_image,
            'VERIFICATION_REJECTED', foreign_adapter)
for name in ('foreign_same_journal', 'fake', 'corrupt_seal'):
    bridge_case(name, (proofs / f'{name}.receipt').read_bytes(), journal, image,
                'VERIFICATION_REJECTED')
bridge_case('malformed_receipt', b'malformed', journal, image, 'VERIFICATION_REJECTED')
bridge_case('truncated_receipt', receipt[:-1], journal, image, 'VERIFICATION_REJECTED')
bridge_case('trailing_receipt_bytes', receipt + b'\x00', journal, image, 'VERIFICATION_REJECTED')
wrong_digest = ('0' if digest[0] != '0' else '1') + digest[1:]
bridge_case('wrong_executable_hash', receipt, journal, image, 'EXECUTABLE_BINDING',
            GlobalReceiptVerifierV1(str(binary), wrong_digest, image, 60000))
bridge_case('unavailable_verifier', receipt, journal, image, 'EXECUTABLE_UNAVAILABLE',
            GlobalReceiptVerifierV1(str(output / 'absent'), digest, image, 60000))

# Independent frame construction and direct endpoint classes supplement the
# measured bridge. Only the preceding calls exercise sealed memfd execution.
def frame(encoded, expected_journal=journal, expected_image=image):
    return (b'ZDXRV1RQ' + bytes.fromhex(expected_image[2:])
            + struct.pack('<II', len(expected_journal), len(encoded))
            + expected_journal + encoded)

request = frame(receipt)
response = subprocess.run([str(binary)], input=request, capture_output=True,
                          env={'RISC0_DEV_MODE': '0', 'LC_ALL': 'C'}, timeout=60, check=True)
expected_response = b'ZDXRV1OK' + hashlib.sha256(request).digest() + bytes.fromhex(image[2:])
if response.stdout != expected_response or response.stderr:
    raise SystemExit('independent successful frame response mismatch')
(proofs / 'epoch.request').write_bytes(request)
(proofs / 'epoch.response').write_bytes(response.stdout)
for name, encoded, expected_class in (
    ('foreign_same_journal', (proofs / 'foreign_same_journal.receipt').read_bytes(), 'ReceiptVerification'),
    ('fake', (proofs / 'fake.receipt').read_bytes(), 'ReceiptKind'),
    ('corrupt_seal', (proofs / 'corrupt_seal.receipt').read_bytes(), 'ReceiptVerification'),
    ('malformed', b'malformed', 'ReceiptEncoding'),
):
    result = subprocess.run([str(binary)], input=frame(encoded), capture_output=True,
                            env={'RISC0_DEV_MODE': '0', 'LC_ALL': 'C'}, timeout=60)
    if (result.returncode != 2 or result.stdout or
            result.stderr != f'receipt verifier rejected: {expected_class}\n'.encode()):
        raise SystemExit(f'independent endpoint rejection mismatch: {name}')
    checks.append({'name': 'direct_' + name, 'result': expected_class})
artifacts = {}
for path in sorted(proofs.iterdir()):
    artifacts[path.name] = {'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                            'bytes': path.stat().st_size}
report = {'schema': 'zenodex-structural-bridge-qualification-v1',
          'scope': metadata['scope'], 'asset_transfer_semantics_proved': False,
          'production_value_safety_qualified': False, 'publication_authority': False,
          'verifier_sha256': digest, 'image_id': image, 'checks': checks,
          'artifacts': artifacts,
          'source_manifest_sha256': hashlib.sha256((output / 'source.sha256').read_bytes()).hexdigest()}
(output / 'qualification.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
print(json.dumps({'qualification': 'STRUCTURAL_BRIDGE_ONLY', 'checks': len(checks),
                  'image_id': image, 'verifier_sha256': digest}, sort_keys=True))
PY
sha256sum "$output_dir/qualification.json"
