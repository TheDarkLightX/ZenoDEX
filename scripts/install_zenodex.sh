#!/usr/bin/env sh
set -eu

usage() {
  cat <<'USAGE'
Usage: scripts/install_zenodex.sh [--bin-dir DIR] [--dry-run]

Installs small command wrappers for this checkout:
  zenoctl                 -> tools/zenoctl.py
  zenodex-node            -> tools/zeno_ledger_node.py
  zenodex-local-testnet   -> tools/zenoctl.py testnet local
  zenodex-public-testnet  -> tools/zenoctl.py testnet local public
  zenodex-public-follower -> tools/zenodex_public_follower.py

The script does not install system services, write secrets, or edit shell
profiles. Add the chosen bin directory to PATH yourself if needed.
USAGE
}

bin_dir="${HOME}/.local/bin"
dry_run=0

while [ "$#" -gt 0 ]; do
  case "$1" in
    --bin-dir)
      [ "$#" -ge 2 ] || { echo "missing value for --bin-dir" >&2; exit 2; }
      bin_dir="$2"
      shift 2
      ;;
    --dry-run)
      dry_run=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if ! command -v python3 >/dev/null 2>&1; then
  echo "python3 not found on PATH" >&2
  exit 1
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "${script_dir}/.." && pwd)

install_wrapper() {
  name="$1"
  shift
  out="${bin_dir}/${name}"
  if [ "$dry_run" -eq 1 ]; then
    echo "would install ${out} -> $*"
    return 0
  fi
  mkdir -p "$bin_dir"
  {
    printf '%s\n' '#!/usr/bin/env sh'
    printf '%s\n' 'set -eu'
    printf 'exec'
    for arg in "$@"; do
      arg_quoted=$(printf "%s" "$arg" | sed "s/'/'\\\\''/g")
      printf " '%s'" "$arg_quoted"
    done
    printf ' "$@"\n'
  } > "$out"
  chmod 755 "$out"
  echo "installed ${out}"
}

install_wrapper "zenoctl" python3 "${repo_dir}/tools/zenoctl.py"
install_wrapper "zenodex-node" python3 "${repo_dir}/tools/zeno_ledger_node.py"
install_wrapper "zenodex-local-testnet" python3 "${repo_dir}/tools/zenoctl.py" testnet local
install_wrapper "zenodex-public-testnet" python3 "${repo_dir}/tools/zenoctl.py" testnet local public
install_wrapper "zenodex-public-follower" python3 "${repo_dir}/tools/zenodex_public_follower.py"

if [ "$dry_run" -eq 0 ]; then
  echo "run: ${bin_dir}/zenoctl doctor --engine none --strict"
  echo "run: ${bin_dir}/zenodex-local-testnet up --out-dir /tmp/zenodex-local"
  echo "run: ${bin_dir}/zenodex-public-testnet"
  echo "run: ${bin_dir}/zenodex-public-follower --config-url <public_network_config.json URL>"
fi
