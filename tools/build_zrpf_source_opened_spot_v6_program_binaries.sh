#!/bin/bash -p

if [[ $- != *p* ]]; then
  builtin printf '%s\n' "error: privileged bash mode required" >&2
  builtin exit 2
fi

set -euo pipefail

for variable in \
  BASH_ENV CDPATH ENV GLOBIGNORE LD_AUDIT LD_LIBRARY_PATH LD_PRELOAD \
  POSIXLY_CORRECT; do
  [[ ! -v "$variable" ]] || {
    builtin printf '%s\n' "error: hostile build environment rejected" >&2
    builtin exit 2
  }
done

builtin unset -f \
  basename dirname docker find git id install mkdir mktemp od readlink realpath \
  rm sha256sum sort stat tar tr 2>/dev/null || :
readonly PATH=/usr/bin:/bin
export PATH

# This recipe only builds and extracts four bounded RISC0 program binaries. It
# does not generate proofs or establish release, settlement, or production
# authority.
# This exact local image was built from `.docker/zrpf-assurance.Dockerfile`.
# Its pinned Ubuntu parent is recorded separately. Cross-host image rebuild
# reproducibility remains outside this recipe's claim.
readonly BUILD_IMAGE='sha256:de7091a181792417fbd5eaf6b3aff77d8a26ae0f2ae7ce298c01bf4ad9cd4b9c'
readonly BUILD_IMAGE_PARENT='ubuntu@sha256:4fbb8e6a8395de5a7550b33509421a2bafbc0aab6c06ba2cef9ebffbc7092d90'
readonly CANONICAL_SOURCE_ROOT=/src/zenodex
readonly CONTAINER_OUTPUT_ROOT=/build/output
readonly CONTAINER_TARGET_ROOT=/build/target
readonly PROGRAM_BINARY_MAGIC_HEX=52304246
readonly RISC0_TOOLCHAIN_BASENAME=v1.94.1-rust-x86_64-unknown-linux-gnu
readonly EXPECTED_CARGO_VERSION='cargo 1.94.1-dev (29ea6fb6a 2026-03-24)'
readonly EXPECTED_RUSTC_VERSION='rustc 1.94.1-dev (06e01cb0d 2026-04-09)'
readonly MAX_PROGRAM_BINARY_BYTES=16777216

usage() {
  builtin printf '%s\n' \
    'usage: build_zrpf_source_opened_spot_v6_program_binaries.sh' \
    '  --source-commit <full-40-byte-hex-commit>' \
    '  --risc0-toolchain-dir <absolute-v1.94.1-toolchain-directory>' \
    '  --cargo-registry-dir <absolute-cargo-registry-directory>' \
    '  --target-dir <absolute-new-external-target-directory>' \
    '  --output-dir <absolute-new-external-output-directory>'
}

source_commit=''
risc0_toolchain_dir=''
cargo_registry_dir=''
target_dir=''
output_dir=''
declare -A seen_options=()

while (($#)); do
  if [[ $1 == --help && $# -eq 1 ]]; then
    usage
    exit 0
  fi
  [[ -n $1 && $# -ge 2 && -n ${2-} && ${2-} != --* \
    && -z ${seen_options[$1]+present} ]] || {
    builtin printf '%s\n' "error: unknown, duplicate, or incomplete argument" >&2
    exit 2
  }
  seen_options["$1"]=1
  case "$1" in
    --source-commit)
      source_commit=$2
      ;;
    --risc0-toolchain-dir)
      risc0_toolchain_dir=$2
      ;;
    --cargo-registry-dir)
      cargo_registry_dir=$2
      ;;
    --target-dir)
      target_dir=$2
      ;;
    --output-dir)
      output_dir=$2
      ;;
    *)
      builtin printf '%s\n' "error: unknown, duplicate, or incomplete argument" >&2
      exit 2
      ;;
  esac
  shift 2
done

for value in \
  "$source_commit" \
  "$risc0_toolchain_dir" \
  "$cargo_registry_dir" \
  "$target_dir" \
  "$output_dir"; do
  [[ -n $value ]] || {
    builtin printf '%s\n' "error: required argument missing" >&2
    exit 2
  }
done

[[ $source_commit =~ ^[0-9a-f]{40}$ ]] || {
  builtin printf '%s\n' "error: source commit must be full lowercase hexadecimal" >&2
  exit 2
}

SCRIPT_DIRECTORY=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
readonly SCRIPT_DIRECTORY
REPOSITORY_ROOT=$(realpath -e -- "$SCRIPT_DIRECTORY/..")
readonly REPOSITORY_ROOT

git_clean() {
  env -i \
    GIT_CONFIG_GLOBAL=/dev/null \
    GIT_CONFIG_NOSYSTEM=1 \
    HOME=/nonexistent \
    LC_ALL=C \
    PATH="$PATH" \
    TZ=UTC \
    /usr/bin/git -C "$REPOSITORY_ROOT" "$@"
}

[[ $(git_clean rev-parse --show-toplevel) == "$REPOSITORY_ROOT" ]] || {
  builtin printf '%s\n' "error: script is not inside the canonical Git worktree" >&2
  exit 2
}
ACTUAL_SOURCE_COMMIT=$(git_clean rev-parse --verify 'HEAD^{commit}')
readonly ACTUAL_SOURCE_COMMIT
[[ $ACTUAL_SOURCE_COMMIT == "$source_commit" ]] || {
  builtin printf '%s\n' "error: checked-out source commit mismatch" >&2
  exit 2
}
[[ -z $(git_clean status --porcelain=v1 --untracked-files=all) ]] || {
  builtin printf '%s\n' "error: source worktree must be completely clean" >&2
  exit 2
}
[[ -z $(git_clean ls-files --stage | /usr/bin/awk '$1 == "160000" { print $4 }') ]] || {
  builtin printf '%s\n' "error: submodule source is outside this bounded recipe" >&2
  exit 2
}
SOURCE_COMMIT_EPOCH=$(git_clean show -s --format=%ct "$source_commit")
readonly SOURCE_COMMIT_EPOCH
[[ $SOURCE_COMMIT_EPOCH =~ ^[0-9]+$ ]] || {
  builtin printf '%s\n' "error: source commit epoch is invalid" >&2
  exit 2
}

canonical_existing_directory() {
  local candidate=$1
  local label=$2
  [[ $candidate == /* && -d $candidate && ! -L $candidate \
    && $(realpath -e -- "$candidate") == "$candidate" ]] || {
    builtin printf 'error: %s must be a canonical real directory\n' "$label" >&2
    exit 2
  }
  [[ $candidate != *:* && $candidate != *,* && $candidate != *$'\n'* ]] || {
    builtin printf 'error: %s contains an unsafe mount character\n' "$label" >&2
    exit 2
  }
}

canonical_new_external_directory() {
  local candidate=$1
  local label=$2
  local parent
  local canonical
  [[ $candidate == /* && ! -e $candidate && ! -L $candidate ]] || {
    builtin printf 'error: %s must be an absent absolute path\n' "$label" >&2
    exit 2
  }
  parent=$(dirname -- "$candidate")
  canonical=$(realpath -e -- "$parent")/$(basename -- "$candidate")
  [[ $canonical == "$candidate" ]] || {
    builtin printf 'error: %s path must be canonical\n' "$label" >&2
    exit 2
  }
  case "$candidate/" in
    "$REPOSITORY_ROOT/"*)
      builtin printf 'error: %s must be external to the source repository\n' "$label" >&2
      exit 2
      ;;
  esac
  [[ $candidate != *:* && $candidate != *,* && $candidate != *$'\n'* ]] || {
    builtin printf 'error: %s contains an unsafe mount character\n' "$label" >&2
    exit 2
  }
}

canonical_existing_directory "$risc0_toolchain_dir" "RISC0 toolchain"
canonical_existing_directory "$cargo_registry_dir" "Cargo registry"
canonical_new_external_directory "$target_dir" "target directory"
canonical_new_external_directory "$output_dir" "output directory"
[[ $target_dir != "$output_dir" \
  && $target_dir != "$output_dir/"* \
  && $output_dir != "$target_dir/"* ]] || {
  builtin printf '%s\n' "error: target and output directories must not overlap" >&2
  exit 2
}
[[ ${risc0_toolchain_dir##*/} == "$RISC0_TOOLCHAIN_BASENAME" ]] || {
  builtin printf '%s\n' "error: unexpected RISC0 toolchain directory" >&2
  exit 2
}
[[ -x $risc0_toolchain_dir/bin/cargo && ! -L $risc0_toolchain_dir/bin/cargo \
  && -x $risc0_toolchain_dir/bin/rustc && ! -L $risc0_toolchain_dir/bin/rustc ]] || {
  builtin printf '%s\n' "error: pinned RISC0 Cargo or rustc is unavailable" >&2
  exit 2
}
[[ $($risc0_toolchain_dir/bin/cargo --version) == "$EXPECTED_CARGO_VERSION" \
  && $($risc0_toolchain_dir/bin/rustc --version) == "$EXPECTED_RUSTC_VERSION" ]] || {
  builtin printf '%s\n' "error: pinned RISC0 toolchain version mismatch" >&2
  exit 2
}
for registry_component in cache index src; do
  [[ -d $cargo_registry_dir/$registry_component \
    && ! -L $cargo_registry_dir/$registry_component ]] || {
    builtin printf '%s\n' "error: Cargo registry inventory is incomplete" >&2
    exit 2
  }
done

readonly DOCKER=/usr/bin/docker
[[ -x $DOCKER && ! -L $DOCKER ]] || {
  builtin printf '%s\n' "error: canonical Docker client is unavailable" >&2
  exit 2
}
"$DOCKER" image inspect "$BUILD_IMAGE" >/dev/null || {
  builtin printf '%s\n' "error: pinned build image must already exist locally" >&2
  exit 2
}

umask 077
mkdir -m 0700 -- "$target_dir" "$output_dir"
SOURCE_SNAPSHOT=$(mktemp -d "$(dirname -- "$target_dir")/.zrpf-v6-source.XXXXXX")
readonly SOURCE_SNAPSHOT
build_completed=0

cleanup() {
  local status=$?
  trap - EXIT
  rm -rf -- "$SOURCE_SNAPSHOT"
  if ((status != 0 || build_completed == 0)); then
    rm -rf -- "$output_dir"
  fi
  exit "$status"
}
trap cleanup EXIT

git_clean archive --format=tar "$source_commit" \
  | /usr/bin/tar \
      --extract \
      --directory "$SOURCE_SNAPSHOT" \
      --no-same-owner \
      --no-same-permissions
[[ -f $SOURCE_SNAPSHOT/zk/zrpf_risc0/Cargo.toml \
  && -f $SOURCE_SNAPSHOT/zk/zrpf_risc0/Cargo.lock \
  && ! -L $SOURCE_SNAPSHOT/zk/zrpf_risc0/Cargo.toml \
  && ! -L $SOURCE_SNAPSHOT/zk/zrpf_risc0/Cargo.lock ]] || {
  builtin printf '%s\n' "error: exact committed ZRPF workspace was not archived" >&2
  exit 2
}

HOST_UID=$(id -u)
HOST_GID=$(id -g)
readonly HOST_UID HOST_GID
[[ $HOST_UID =~ ^[0-9]+$ && $HOST_GID =~ ^[0-9]+$ ]] || {
  builtin printf '%s\n' "error: host UID or GID is invalid" >&2
  exit 2
}

CONTAINER_SCRIPT=''
read -r -d '' CONTAINER_SCRIPT <<'CONTAINER_SCRIPT_EOF' || :
set -euo pipefail
umask 077
export PATH="/risc0/toolchains/v1.94.1-rust-x86_64-unknown-linux-gnu/bin:/usr/bin:/bin"
export HOME=/home/zrpf
export CARGO_HOME=/home/zrpf/.cargo
export CARGO_NET_OFFLINE=true
export CARGO_TARGET_DIR=/build/target
export RISC0_BUILD_LOCKED=1
export RISC0_HOME=/risc0
unset RISC0_SKIP_BUILD RUSTUP_TOOLCHAIN

install -d -m 0700 /home/zrpf/.cargo
[[ -d /risc0/toolchains && ! -L /risc0/toolchains ]]
ln -s /opt/cargo-registry /home/zrpf/.cargo/registry
ln -s /risc0 /home/zrpf/.risc0
printf '%s\n' \
  '[build]' \
  'jobs = 2' \
  '' \
  '[net]' \
  'offline = true' \
  '' \
  '[target.x86_64-unknown-linux-gnu]' \
  'linker = "/usr/bin/cc"' \
  > /home/zrpf/.cargo/config.toml
printf '%s\n' \
  '[default_versions]' \
  'rust = "1.94.1"' \
  > /risc0/settings.toml

[[ "$(pwd -P)" == /src/zenodex ]]
[[ ! -e /src/zenodex/target && ! -e /src/zenodex/zk/zrpf_risc0/target ]]
[[ -z "$(find /build/output -mindepth 1 -maxdepth 1 -print -quit)" ]]

/risc0/toolchains/v1.94.1-rust-x86_64-unknown-linux-gnu/bin/cargo build \
  --manifest-path /src/zenodex/zk/zrpf_risc0/Cargo.toml \
  --package zenodex-zrpf-risc0-spot-v6-methods \
  --release \
  --locked \
  --offline \
  --jobs 2 \
  --target-dir /build/target

readonly guest_root=/build/target/riscv-guest/zenodex-zrpf-risc0-spot-v6-methods
readonly -a source_program_binaries=(
  "$guest_root/zenodex-zrpf-risc0-source-opened-spot-settlement-v6/riscv32im-risc0-zkvm-elf/release/zenodex-zrpf-risc0-source-opened-spot-settlement-v6.bin"
  "$guest_root/zenodex-zrpf-risc0-spot-value-aggregate-l1-v6/riscv32im-risc0-zkvm-elf/release/zenodex-zrpf-risc0-spot-value-aggregate-l1-v6.bin"
  "$guest_root/zenodex-zrpf-risc0-spot-value-aggregate-l2-v6/riscv32im-risc0-zkvm-elf/release/zenodex-zrpf-risc0-spot-value-aggregate-l2-v6.bin"
  "$guest_root/zenodex-zrpf-risc0-spot-value-leaf-v6/riscv32im-risc0-zkvm-elf/release/zenodex-zrpf-risc0-spot-value-leaf-v6.bin"
)
readonly -a output_program_binaries=(
  /build/output/source_opened_spot_settlement_v6.bin
  /build/output/spot_value_aggregate_l1_v6.bin
  /build/output/spot_value_aggregate_l2_v6.bin
  /build/output/spot_value_leaf_v6.bin
)

mapfile -d '' -t discovered_program_binaries < <(
  find "$guest_root" -type f -name '*.bin' -print0 | sort -z
)
[[ ${#discovered_program_binaries[@]} -eq ${#source_program_binaries[@]} ]]
for index in "${!source_program_binaries[@]}"; do
  source_program=${source_program_binaries[$index]}
  destination=${output_program_binaries[$index]}
  [[ ${discovered_program_binaries[$index]} == "$source_program" ]]
  [[ -f $source_program && ! -L $source_program ]]
  size=$(stat -c %s -- "$source_program")
  [[ $size -gt 4 && $size -le 16777216 ]]
  magic=$(od -An -tx1 -N4 -- "$source_program" | tr -d ' \n')
  [[ $magic == 52304246 ]]
  install -m 0444 -- "$source_program" "$destination"
  cmp --silent -- "$source_program" "$destination"
done

readonly -a expected_output_names=(
  source_opened_spot_settlement_v6.bin
  spot_value_aggregate_l1_v6.bin
  spot_value_aggregate_l2_v6.bin
  spot_value_leaf_v6.bin
)
mapfile -t actual_output_names < <(
  find /build/output -mindepth 1 -maxdepth 1 -type f -printf '%f\n' | sort
)
[[ ${#actual_output_names[@]} -eq ${#expected_output_names[@]} ]]
for index in "${!expected_output_names[@]}"; do
  [[ ${actual_output_names[$index]} == "${expected_output_names[$index]}" ]]
done
sha256sum -- "${output_program_binaries[@]}"
CONTAINER_SCRIPT_EOF
readonly CONTAINER_SCRIPT

"$DOCKER" run --rm \
  --network none \
  --read-only \
  --cap-drop ALL \
  --security-opt no-new-privileges \
  --pids-limit 512 \
  --cpus 2 \
  --memory 6g \
  --memory-swap 6g \
  --user "$HOST_UID:$HOST_GID" \
  --hostname zrpf-v6-program-build \
  --tmpfs "/tmp:rw,nosuid,nodev,noexec,size=256m,mode=1777,uid=$HOST_UID,gid=$HOST_GID" \
  --tmpfs "/home/zrpf:rw,nosuid,nodev,noexec,size=512m,mode=0700,uid=$HOST_UID,gid=$HOST_GID" \
  --tmpfs "/risc0:rw,nosuid,nodev,noexec,size=2m,mode=0700,uid=$HOST_UID,gid=$HOST_GID" \
  --mount "type=bind,source=$SOURCE_SNAPSHOT,target=$CANONICAL_SOURCE_ROOT,readonly" \
  --mount "type=bind,source=$risc0_toolchain_dir,target=/risc0/toolchains/v1.94.1-rust-x86_64-unknown-linux-gnu,readonly" \
  --mount "type=bind,source=$cargo_registry_dir,target=/opt/cargo-registry,readonly" \
  --mount "type=bind,source=$target_dir,target=$CONTAINER_TARGET_ROOT" \
  --mount "type=bind,source=$output_dir,target=$CONTAINER_OUTPUT_ROOT" \
  --env LC_ALL=C \
  --env SOURCE_DATE_EPOCH="$SOURCE_COMMIT_EPOCH" \
  --env TZ=UTC \
  --workdir "$CANONICAL_SOURCE_ROOT" \
  --entrypoint /bin/bash \
  "$BUILD_IMAGE" \
  -p -ceu "$CONTAINER_SCRIPT"

readonly -a HOST_OUTPUTS=(
  "$output_dir/source_opened_spot_settlement_v6.bin"
  "$output_dir/spot_value_aggregate_l1_v6.bin"
  "$output_dir/spot_value_aggregate_l2_v6.bin"
  "$output_dir/spot_value_leaf_v6.bin"
)
mapfile -t host_output_names < <(
  find "$output_dir" -mindepth 1 -maxdepth 1 -type f -printf '%f\n' | sort
)
[[ ${#host_output_names[@]} -eq ${#HOST_OUTPUTS[@]} ]] || {
  builtin printf '%s\n' "error: extracted program-binary inventory mismatch" >&2
  exit 2
}
for index in "${!HOST_OUTPUTS[@]}"; do
  candidate=${HOST_OUTPUTS[$index]}
  [[ ${host_output_names[$index]} == "${candidate##*/}" \
    && -f $candidate && ! -L $candidate ]] || {
    builtin printf '%s\n' "error: extracted program binary rejected" >&2
    exit 2
  }
  size=$(stat -c %s -- "$candidate")
  magic=$(od -An -tx1 -N4 -- "$candidate" | tr -d ' \n')
  [[ $size -gt 4 && $size -le $MAX_PROGRAM_BINARY_BYTES \
    && $magic == "$PROGRAM_BINARY_MAGIC_HEX" ]] || {
    builtin printf '%s\n' "error: extracted file is not a bounded R0BF program binary" >&2
    exit 2
  }
done

build_completed=1
builtin printf 'build_image=%s\n' "$BUILD_IMAGE"
builtin printf 'build_image_parent=%s\n' "$BUILD_IMAGE_PARENT"
builtin printf 'source_commit=%s\n' "$source_commit"
sha256sum -- "${HOST_OUTPUTS[@]}"
