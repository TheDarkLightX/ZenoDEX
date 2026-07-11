#!/usr/bin/env bash
set -euo pipefail

# Deterministically assemble the bounded ZRPF Firecracker root and input images.
# This build helper creates artifacts only. It grants no launch or proof authority.

readonly EXPECTED_RECEIPT_COUNT=8
readonly GUEST_ELF_REFERENCE_SHA256=214701b87714777b07aabd6cc24dae00a4356887416891cf8edacd3d34cf1995
readonly IMAGE_EPOCH=1780396050
readonly SQUASHFS_BLOCK_BYTES=131072
SCRIPT_DIRECTORY=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
readonly SCRIPT_DIRECTORY
GUEST_ELF_REFERENCE="$SCRIPT_DIRECTORY/check_zrpf_v3_firecracker_guest_elf.py"
readonly GUEST_ELF_REFERENCE

guest_binary=""
receipt_directory=""
output_directory=""
expected_guest_sha256=""
expected_receipt_set_sha256=""
expected_mksquashfs_sha256=""
guest_elf_checker_binary=""
expected_guest_elf_checker_sha256=""

while (($#)); do
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
    --expected-guest-sha256)
      expected_guest_sha256=${2-}
      shift 2
      ;;
    --expected-receipt-set-sha256)
      expected_receipt_set_sha256=${2-}
      shift 2
      ;;
    --expected-mksquashfs-sha256)
      expected_mksquashfs_sha256=${2-}
      shift 2
      ;;
    --guest-elf-checker-binary)
      guest_elf_checker_binary=${2-}
      shift 2
      ;;
    --expected-guest-elf-checker-sha256)
      expected_guest_elf_checker_sha256=${2-}
      shift 2
      ;;
    *)
      echo "error: unknown or incomplete argument" >&2
      exit 2
      ;;
  esac
done

for value in \
  "$guest_binary" \
  "$receipt_directory" \
  "$output_directory" \
  "$expected_guest_sha256" \
  "$expected_receipt_set_sha256" \
  "$expected_mksquashfs_sha256" \
  "$guest_elf_checker_binary" \
  "$expected_guest_elf_checker_sha256"; do
  [[ -n "$value" ]] || { echo "error: required argument missing" >&2; exit 2; }
done

umask 077
export LC_ALL=C
export TZ=UTC

[[ ! -e "$output_directory" ]] || { echo "error: output exists" >&2; exit 2; }
[[ -f "$guest_binary" && ! -L "$guest_binary" && $(stat -c %h "$guest_binary") -eq 1 ]] || {
  echo "error: guest binary rejected" >&2
  exit 2
}
[[ -d "$receipt_directory" && ! -L "$receipt_directory" ]] || {
  echo "error: receipt directory rejected" >&2
  exit 2
}
[[ -f "$guest_elf_checker_binary" && ! -L "$guest_elf_checker_binary" \
  && $(stat -c %h "$guest_elf_checker_binary") -eq 1 ]] || {
  echo "error: guest ELF checker binary rejected" >&2
  exit 2
}
guest_elf_checker_binary_sha256_before=$(sha256sum "$guest_elf_checker_binary" | cut -d' ' -f1)
[[ "$guest_elf_checker_binary_sha256_before" == "$expected_guest_elf_checker_sha256" ]] || {
  echo "error: guest ELF checker binary identity mismatch" >&2
  exit 2
}

mksquashfs_path=$(command -v mksquashfs)
[[ $(sha256sum "$mksquashfs_path" | cut -d' ' -f1) == "$expected_mksquashfs_sha256" ]] || {
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
guest_sha256_before=$(sha256sum "$guest_binary" | cut -d' ' -f1)
[[ "$guest_sha256_before" == "$expected_guest_sha256" ]] || {
  echo "error: guest identity mismatch" >&2
  exit 2
}
env -i LC_ALL=C TZ=UTC \
  "$guest_elf_checker_binary" --guest-elf "$guest_binary" >/dev/null

receipt_set_sha256() {
  local directory=$1
  find "$directory" -mindepth 1 -maxdepth 1 -type f -printf '%f\n' \
    | sort \
    | while IFS= read -r name; do
        [[ "$name" != *$'\n'* && "$name" != *$'\r'* ]] || exit 3
        local_path="$directory/$name"
        [[ -f "$local_path" && ! -L "$local_path" ]] || exit 3
        size=$(stat -c %s "$local_path")
        digest=$(sha256sum "$local_path" | cut -d' ' -f1)
        printf '%s\0%s\0%s\n' "$name" "$size" "$digest"
      done \
    | sha256sum \
    | cut -d' ' -f1
}

receipt_count=$(find "$receipt_directory" -mindepth 1 -maxdepth 1 -type f | wc -l)
inventory_count=$(find "$receipt_directory" -mindepth 1 -maxdepth 1 | wc -l)
[[ "$receipt_count" -eq "$EXPECTED_RECEIPT_COUNT" && "$inventory_count" -eq "$receipt_count" ]] || {
  echo "error: receipt inventory mismatch" >&2
  exit 2
}
before_receipt_set=$(receipt_set_sha256 "$receipt_directory")
[[ "$before_receipt_set" == "$expected_receipt_set_sha256" ]] || {
  echo "error: receipt-set identity mismatch" >&2
  exit 2
}

mkdir -m 0700 "$output_directory"
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
  install -m 0555 "$guest_binary" "$stage/rootfs/sbin/zrpf-replay-init"
  find "$receipt_directory" -mindepth 1 -maxdepth 1 -type f -printf '%f\n' \
    | sort \
    | while IFS= read -r name; do
        install -m 0444 \
          "$receipt_directory/$name" \
          "$stage/input/receipts/$name"
      done
  chmod 0555 "$stage/input/receipts"
}

build_images() {
  local stage=$1
  local label=$2
  "$mksquashfs_path" \
    "$stage/rootfs" \
    "$output_directory/rootfs-$label.squashfs" \
    -noappend -comp zstd -b "$SQUASHFS_BLOCK_BYTES" -all-root \
    -all-time "$IMAGE_EPOCH" -mkfs-time "$IMAGE_EPOCH" \
    -no-exports -no-xattrs -no-progress >/dev/null
  "$mksquashfs_path" \
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

after_receipt_set=$(receipt_set_sha256 "$receipt_directory")
[[ "$after_receipt_set" == "$before_receipt_set" ]] || {
  echo "error: receipt set changed during build" >&2
  exit 2
}
[[ $(sha256sum "$guest_binary" | cut -d' ' -f1) == "$guest_sha256_before" ]] || {
  echo "error: guest identity changed during build" >&2
  exit 2
}
[[ $(sha256sum "$GUEST_ELF_REFERENCE" | cut -d' ' -f1) == "$guest_elf_reference_sha256_before" ]] || {
  echo "error: guest ELF reference identity changed during build" >&2
  exit 2
}
[[ $(sha256sum "$guest_elf_checker_binary" | cut -d' ' -f1) == "$guest_elf_checker_binary_sha256_before" ]] || {
  echo "error: guest ELF checker binary identity changed during build" >&2
  exit 2
}
env -i LC_ALL=C TZ=UTC \
  "$guest_elf_checker_binary" --guest-elf "$guest_binary" >/dev/null

rootfs_sha256=$(sha256sum "$output_directory/zrpf-replay-rootfs.squashfs" | cut -d' ' -f1)
input_sha256=$(sha256sum "$output_directory/zrpf-replay-input.squashfs" | cut -d' ' -f1)
rootfs_size=$(stat -c %s "$output_directory/zrpf-replay-rootfs.squashfs")
input_size=$(stat -c %s "$output_directory/zrpf-replay-input.squashfs")

printf '%s\n' \
  "guest_sha256=$expected_guest_sha256" \
  "input_sha256=$input_sha256" \
  "input_size_bytes=$input_size" \
  "receipt_set_sha256=$after_receipt_set" \
  "rootfs_sha256=$rootfs_sha256" \
  "rootfs_size_bytes=$rootfs_size"
