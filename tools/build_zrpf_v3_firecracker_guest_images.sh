#!/bin/bash -p

if [[ $- != *p* ]]; then
  builtin printf '%s\n' "error: privileged bash mode required" >&2
  builtin exit 2
fi

set -euo pipefail

for variable in \
  BASH_ENV CDPATH ENV GLOBIGNORE LD_AUDIT LD_LIBRARY_PATH LD_PRELOAD \
  POSIXLY_CORRECT SOURCE_DATE_EPOCH; do
  [[ ! -v "$variable" ]] || {
    builtin printf '%s\n' "error: hostile build environment rejected" >&2
    builtin exit 2
  }
done

builtin unset -f \
  chmod cmp cut dirname find install mkdir mksquashfs mktemp mv realpath rm sha256sum sort stat wc \
  2>/dev/null || :
readonly PATH=/usr/bin:/bin
export PATH

# Deterministically assemble the bounded ZRPF Firecracker root and input images.
# Captured hashes do not establish same-UID resistance or packed-file identity.
# This build helper creates artifacts only. It grants no launch or proof authority.

readonly EXPECTED_RECEIPT_COUNT=8
readonly GUEST_BINARY_SHA256=6f0efc78966813444cc157f2e9c856e71da91c19538318cdb2e8be520214a150
readonly GUEST_ELF_CHECKER_BINARY_SHA256=015ad4f9406a1683ee23fe4a1ad991c8f30f418366fee1881722512a1711092d
readonly GUEST_ELF_REFERENCE_SHA256=7abd685b3cb5d88a9678c1cdd303ec95d8844607b8c39b1ba12e06a4c350cfeb
readonly IMAGE_EPOCH=1780396050
readonly MKSQUASHFS_BINARY_SHA256=47d5c1af3da11864e64c9dc6bb4e568719dcc315e6a744e79381ce3374fb7393
readonly RECEIPT_SET_SHA256=d5ecd5494318e21fa3da227409fdb5285c85ff8ae10815df5bcf0eb22fa1027f
readonly SQUASHFS_BLOCK_BYTES=131072
readonly MKSQUASHFS_BINARY=/usr/bin/mksquashfs
SCRIPT_DIRECTORY=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
readonly SCRIPT_DIRECTORY
GUEST_ELF_REFERENCE="$SCRIPT_DIRECTORY/check_zrpf_v3_firecracker_guest_elf.py"
readonly GUEST_ELF_REFERENCE

guest_binary=""
receipt_directory=""
output_directory=""
guest_elf_checker_binary=""
declare -A seen_options=()

while (($#)); do
  [[ -n $1 && $# -ge 2 && -n ${2-} && ${2-} != --* \
    && -z ${seen_options[$1]+present} ]] || {
    echo "error: unknown, duplicate, or incomplete argument" >&2
    exit 2
  }
  seen_options["$1"]=1
  case "$1" in
    --guest-binary)
      guest_binary=${2-}
      shift 2
      ;;
    --receipt-dir)
      receipt_directory=${2-}
      shift 2
      ;;
    --output-dir)
      output_directory=${2-}
      shift 2
      ;;
    --guest-elf-checker-binary)
      guest_elf_checker_binary=${2-}
      shift 2
      ;;
    *)
      echo "error: unknown, duplicate, or incomplete argument" >&2
      exit 2
      ;;
  esac
done

for value in \
  "$guest_binary" \
  "$receipt_directory" \
  "$output_directory" \
  "$guest_elf_checker_binary"; do
  [[ -n "$value" ]] || { echo "error: required argument missing" >&2; exit 2; }
done

umask 077
export LC_ALL=C
export TZ=UTC

[[ "$output_directory" == /* && ! -e "$output_directory" ]] || {
  echo "error: output path rejected" >&2
  exit 2
}
output_parent=$(dirname -- "$output_directory")
[[ $(realpath -e -- "$output_parent") == "$output_parent" ]] || {
  echo "error: output parent rejected" >&2
  exit 2
}
[[ "$guest_binary" == /* \
  && $(realpath -e -- "$guest_binary") == "$guest_binary" \
  && -f "$guest_binary" && ! -L "$guest_binary" \
  && $(stat -c %h -- "$guest_binary") -eq 1 ]] || {
  echo "error: guest binary rejected" >&2
  exit 2
}
[[ "$receipt_directory" == /* \
  && $(realpath -e -- "$receipt_directory") == "$receipt_directory" \
  && -d "$receipt_directory" && ! -L "$receipt_directory" ]] || {
  echo "error: receipt directory rejected" >&2
  exit 2
}
[[ "$guest_elf_checker_binary" == /* \
  && $(realpath -e -- "$guest_elf_checker_binary") == "$guest_elf_checker_binary" \
  && -f "$guest_elf_checker_binary" && ! -L "$guest_elf_checker_binary" \
  && $(stat -c %h "$guest_elf_checker_binary") -eq 1 ]] || {
  echo "error: guest ELF checker binary rejected" >&2
  exit 2
}
[[ -f "$MKSQUASHFS_BINARY" && ! -L "$MKSQUASHFS_BINARY" \
  && $(realpath -e -- "$MKSQUASHFS_BINARY") == "$MKSQUASHFS_BINARY" ]] || {
  echo "error: mksquashfs binary rejected" >&2
  exit 2
}
mksquashfs_sha256_before=$(sha256sum "$MKSQUASHFS_BINARY" | cut -d' ' -f1)
[[ "$mksquashfs_sha256_before" == "$MKSQUASHFS_BINARY_SHA256" ]] || {
  echo "error: mksquashfs identity mismatch" >&2
  exit 2
}
[[ -f "$GUEST_ELF_REFERENCE" && ! -L "$GUEST_ELF_REFERENCE" ]] || {
  echo "error: guest ELF reference rejected" >&2
  exit 2
}
guest_elf_reference_sha256_before=$(sha256sum "$GUEST_ELF_REFERENCE" | cut -d' ' -f1)
[[ "$guest_elf_reference_sha256_before" == "$GUEST_ELF_REFERENCE_SHA256" ]] || {
  echo "error: guest ELF reference identity mismatch" >&2
  exit 2
}
receipt_set_sha256() {
  local directory=$1
  find -- "$directory" -mindepth 1 -maxdepth 1 -type f -print0 \
    | sort -z \
    | while IFS= read -r -d '' local_path; do
        name=${local_path##*/}
        [[ "$name" =~ ^[A-Za-z0-9._-]+$ ]] || exit 3
        size=$(stat -c %s -- "$local_path")
        digest=$(sha256sum -- "$local_path" | cut -d' ' -f1)
        printf '%s\0%s\0%s\n' "$name" "$size" "$digest"
      done \
    | sha256sum \
    | cut -d' ' -f1
}

capture_regular() {
  local source=$1
  local destination=$2
  local mode=$3
  local expected_sha256=$4
  local label=$5
  local descriptor
  exec {descriptor}<"$source" || { echo "error: $label capture failed" >&2; exit 2; }
  install -m "$mode" "/proc/$$/fd/$descriptor" "$destination"
  exec {descriptor}<&-
  [[ $(sha256sum -- "$destination" | cut -d' ' -f1) == "$expected_sha256" ]] || {
    echo "error: $label identity mismatch" >&2
    exit 2
  }
}

mkdir -m 0700 "$output_directory"
capture_directory=$(mktemp -d "$output_directory/.captured.XXXXXX")
captured_guest="$capture_directory/guest-init"
captured_checker="$capture_directory/guest-elf-checker"
captured_receipts="$capture_directory/receipts"
mkdir -m 0700 "$captured_receipts"
capture_regular "$guest_binary" "$captured_guest" 0555 "$GUEST_BINARY_SHA256" "guest"
capture_regular \
  "$guest_elf_checker_binary" \
  "$captured_checker" \
  0555 \
  "$GUEST_ELF_CHECKER_BINARY_SHA256" \
  "guest ELF checker"

mapfile -d '' -t receipt_paths < <(
  find -- "$receipt_directory" -mindepth 1 -maxdepth 1 -type f -print0 | sort -z
)
inventory_count=$(find -- "$receipt_directory" -mindepth 1 -maxdepth 1 -printf '.' | wc -c)
[[ "${#receipt_paths[@]}" -eq "$EXPECTED_RECEIPT_COUNT" \
  && "$inventory_count" -eq "${#receipt_paths[@]}" ]] || {
  echo "error: receipt inventory mismatch" >&2
  exit 2
}
for local_path in "${receipt_paths[@]}"; do
  name=${local_path##*/}
  [[ "$name" =~ ^[A-Za-z0-9._-]+$ && -f "$local_path" && ! -L "$local_path" ]] || {
    echo "error: receipt artifact rejected" >&2
    exit 2
  }
  descriptor=""
  exec {descriptor}<"$local_path" || { echo "error: receipt capture failed" >&2; exit 2; }
  install -m 0444 "/proc/$$/fd/$descriptor" "$captured_receipts/$name"
  exec {descriptor}<&-
done
captured_receipt_set=$(receipt_set_sha256 "$captured_receipts")
[[ "$captured_receipt_set" == "$RECEIPT_SET_SHA256" ]] || {
  echo "error: receipt-set identity mismatch" >&2
  exit 2
}
env -i -- LC_ALL=C TZ=UTC \
  "$captured_checker" --guest-elf "$captured_guest" >/dev/null

stage_a=$(mktemp -d "$output_directory/.stage-a.XXXXXX")
stage_b=$(mktemp -d "$output_directory/.stage-b.XXXXXX")

stage_inputs() {
  local stage=$1
  install -d -m 0755 \
    "$stage/rootfs" \
    "$stage/rootfs/dev" \
    "$stage/rootfs/input" \
    "$stage/rootfs/sbin" \
    "$stage/input"
  install -d -m 0755 "$stage/input/receipts"
  install -m 0555 "$captured_guest" "$stage/rootfs/sbin/zrpf-replay-init"
  find -- "$captured_receipts" -mindepth 1 -maxdepth 1 -type f -print0 \
    | sort -z \
    | while IFS= read -r -d '' local_path; do
        name=${local_path##*/}
        install -m 0444 \
          "$local_path" \
          "$stage/input/receipts/$name"
      done
  chmod 0555 "$stage/input/receipts"
}

build_images() {
  local stage=$1
  local label=$2
  "$MKSQUASHFS_BINARY" \
    "$stage/rootfs" \
    "$output_directory/rootfs-$label.squashfs" \
    -noappend -comp zstd -b "$SQUASHFS_BLOCK_BYTES" -all-root \
    -all-time "$IMAGE_EPOCH" -mkfs-time "$IMAGE_EPOCH" \
    -no-exports -no-xattrs -no-progress >/dev/null
  "$MKSQUASHFS_BINARY" \
    "$stage/input" \
    "$output_directory/input-$label.squashfs" \
    -noappend -comp zstd -b "$SQUASHFS_BLOCK_BYTES" -all-root \
    -all-time "$IMAGE_EPOCH" -mkfs-time "$IMAGE_EPOCH" \
    -no-exports -no-xattrs -no-progress >/dev/null
}

stage_inputs "$stage_a"
stage_inputs "$stage_b"
build_images "$stage_a" a
build_images "$stage_b" b

cmp --silent "$output_directory/rootfs-a.squashfs" "$output_directory/rootfs-b.squashfs"
cmp --silent "$output_directory/input-a.squashfs" "$output_directory/input-b.squashfs"
mv "$output_directory/rootfs-a.squashfs" "$output_directory/zrpf-replay-rootfs.squashfs"
mv "$output_directory/input-a.squashfs" "$output_directory/zrpf-replay-input.squashfs"
rm "$output_directory/rootfs-b.squashfs" "$output_directory/input-b.squashfs"
chmod 0755 "$stage_a/input/receipts" "$stage_b/input/receipts"
rm -rf "$stage_a" "$stage_b"

after_receipt_set=$(receipt_set_sha256 "$captured_receipts")
[[ "$after_receipt_set" == "$captured_receipt_set" ]] || {
  echo "error: captured receipt set changed during build" >&2
  exit 2
}
[[ $(sha256sum -- "$captured_guest" | cut -d' ' -f1) == "$GUEST_BINARY_SHA256" ]] || {
  echo "error: captured guest identity changed during build" >&2
  exit 2
}
[[ $(sha256sum "$GUEST_ELF_REFERENCE" | cut -d' ' -f1) == "$guest_elf_reference_sha256_before" ]] || {
  echo "error: guest ELF reference identity changed during build" >&2
  exit 2
}
[[ $(sha256sum -- "$captured_checker" | cut -d' ' -f1) == "$GUEST_ELF_CHECKER_BINARY_SHA256" ]] || {
  echo "error: captured guest ELF checker identity changed during build" >&2
  exit 2
}
[[ $(sha256sum "$MKSQUASHFS_BINARY" | cut -d' ' -f1) == "$mksquashfs_sha256_before" ]] || {
  echo "error: mksquashfs identity changed during build" >&2
  exit 2
}
env -i -- LC_ALL=C TZ=UTC \
  "$captured_checker" --guest-elf "$captured_guest" >/dev/null
rm -rf "$capture_directory"

rootfs_sha256=$(sha256sum "$output_directory/zrpf-replay-rootfs.squashfs" | cut -d' ' -f1)
input_sha256=$(sha256sum "$output_directory/zrpf-replay-input.squashfs" | cut -d' ' -f1)
rootfs_size=$(stat -c %s "$output_directory/zrpf-replay-rootfs.squashfs")
input_size=$(stat -c %s "$output_directory/zrpf-replay-input.squashfs")

printf '%s\n' \
  "schema=zenodex/zrpf_firecracker_image_build_proposal/v1" \
  "status=non_authoritative_image_build_proposal" \
  "complete_build_input_closure_verified=false" \
  "packed_contents_independently_verified=false" \
  "same_uid_resistance_verified=false" \
  "captured_guest_sha256=$GUEST_BINARY_SHA256" \
  "guest_elf_checker_sha256=$GUEST_ELF_CHECKER_BINARY_SHA256" \
  "guest_elf_reference_sha256=$GUEST_ELF_REFERENCE_SHA256" \
  "input_sha256=$input_sha256" \
  "input_size_bytes=$input_size" \
  "captured_receipt_set_sha256=$after_receipt_set" \
  "mksquashfs_binary_sha256=$MKSQUASHFS_BINARY_SHA256" \
  "rootfs_sha256=$rootfs_sha256" \
  "rootfs_size_bytes=$rootfs_size"
