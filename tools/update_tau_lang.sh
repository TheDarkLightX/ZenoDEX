#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
usage: tools/update_tau_lang.sh [--ref <git-ref>] [--build-dir <dir>] [--tau-dir <dir>] [--python-bindings] [--resolve-only]

Updates (or clones) external/tau-lang and builds a Tau binary.

Examples:
  # Build latest main into external/tau-lang/build-Release/tau
  tools/update_tau_lang.sh

  # Build the bitblasting branch into a separate build dir (recommended for A/B benchmarking)
  tools/update_tau_lang.sh --ref feature/bitblasting --build-dir build-Release-bitblasting

  # Keep separate clones for baseline vs experimental branches (recommended)
  tools/update_tau_lang.sh --ref main --tau-dir external/tau-lang --build-dir build-Release
  tools/update_tau_lang.sh --ref feature/bitblasting --tau-dir external/tau-lang-bitblasting --build-dir build-Release-bitblasting

  # Build with Python bindings enabled (optional tooling; not for consensus-critical verification)
  tools/update_tau_lang.sh --python-bindings

  # Fetch and resolve the exact source revision without running submodules or a build
  tools/update_tau_lang.sh --resolve-only
EOF
}

ROOT_REAL="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"

REF="main"
BUILD_DIR="build-Release"
BUILD_TYPE="Release"
TAU_DIR_REL="external/tau-lang"
PY_BINDINGS=0
RESOLVE_ONLY=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --ref)
      REF="${2:-}"
      shift 2
      ;;
    --build-dir)
      BUILD_DIR="${2:-}"
      shift 2
      ;;
    --tau-dir)
      TAU_DIR_REL="${2:-}"
      shift 2
      ;;
    --python-bindings)
      PY_BINDINGS=1
      shift 1
      ;;
    --resolve-only)
      RESOLVE_ONLY=1
      shift 1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown arg: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ -z "${REF}" ]]; then
  echo "error: --ref must be non-empty" >&2
  exit 2
fi
if [[ -z "${BUILD_DIR}" ]]; then
  echo "error: --build-dir must be non-empty" >&2
  exit 2
fi
if [[ -z "${TAU_DIR_REL}" ]]; then
  echo "error: --tau-dir must be non-empty" >&2
  exit 2
fi
if [[ "${TAU_DIR_REL}" == /* ]]; then
  echo "error: --tau-dir must be a repo-relative path (e.g., external/tau-lang)" >&2
  exit 2
fi

# Tau's CMake build currently breaks when the source/build path contains spaces.
# Work around by building through a no-space symlink path while keeping the repo
# location unchanged.
ROOT_BUILD="${ROOT_REAL}"
ROOT_SYMLINK=""
if [[ "${ROOT_REAL}" == *" "* ]]; then
  SAFE_BASE="$(basename "${ROOT_REAL}" | tr ' ' '_' )"
  # Use a stable symlink path so CMake caches remain valid across rebuilds.
  # (CMake stores absolute source/build paths in CMakeCache.txt.)
  ROOT_SYMLINK="/tmp/codex_ws_${SAFE_BASE}"
  if [[ -L "${ROOT_SYMLINK}" ]]; then
    # If the symlink points somewhere else (e.g. after moving the repo), refresh it.
    if [[ "$(readlink "${ROOT_SYMLINK}")" != "${ROOT_REAL}" ]]; then
      rm -f "${ROOT_SYMLINK}"
    fi
  elif [[ -e "${ROOT_SYMLINK}" ]]; then
    echo "error: ${ROOT_SYMLINK} exists and is not a symlink; remove it or choose a different workspace path" >&2
    exit 2
  fi
  if [[ ! -e "${ROOT_SYMLINK}" ]]; then
    ln -s "${ROOT_REAL}" "${ROOT_SYMLINK}"
  fi
  ROOT_BUILD="${ROOT_SYMLINK}"
  echo "Note: workspace path contains spaces; building Tau via symlink: ${ROOT_BUILD}"
fi

TAU_DIR_REAL="${ROOT_REAL}/${TAU_DIR_REL}"
TAU_DIR_BUILD="${ROOT_BUILD}/${TAU_DIR_REL}"

if [[ ! -d "${TAU_DIR_REAL}" ]]; then
  mkdir -p "$(dirname "${TAU_DIR_REAL}")"
  git clone https://github.com/IDNI/tau-lang "${TAU_DIR_REAL}"
fi

if [[ -n "$(git -C "${TAU_DIR_REAL}" status --porcelain --untracked-files=all)" ]]; then
  echo "error: Tau checkout has local tracked or untracked changes; refusing to switch or update it" >&2
  echo "  checkout: ${TAU_DIR_REAL}" >&2
  echo "  preserve the changes or use a separate --tau-dir" >&2
  exit 1
fi

git -C "${TAU_DIR_REAL}" fetch --prune origin

# Accept a local/remote branch, origin/<branch>, tag, or commit hash. A named
# branch may advance only by an ordinary fast-forward. In particular, never
# suppress a pull failure and then build a stale or unrelated local history.
REF_NAME="${REF#origin/}"
LOCAL_BRANCH_REF="refs/heads/${REF_NAME}"
REMOTE_BRANCH_REF="refs/remotes/origin/${REF_NAME}"
if git -C "${TAU_DIR_REAL}" show-ref --verify --quiet "${LOCAL_BRANCH_REF}" && \
   git -C "${TAU_DIR_REAL}" show-ref --verify --quiet "${REMOTE_BRANCH_REF}"; then
  LOCAL_OID="$(git -C "${TAU_DIR_REAL}" rev-parse "${LOCAL_BRANCH_REF}^{commit}")"
  REMOTE_OID="$(git -C "${TAU_DIR_REAL}" rev-parse "${REMOTE_BRANCH_REF}^{commit}")"
  if [[ "${LOCAL_OID}" != "${REMOTE_OID}" ]]; then
    if ! git -C "${TAU_DIR_REAL}" merge-base "${LOCAL_OID}" "${REMOTE_OID}" >/dev/null 2>&1; then
      echo "error: local branch '${REF_NAME}' and 'origin/${REF_NAME}' have no common ancestor" >&2
      echo "  local:  ${LOCAL_OID}" >&2
      echo "  remote: ${REMOTE_OID}" >&2
      echo "  upstream history may have been replaced; preserve this checkout and use a separate --tau-dir" >&2
      exit 1
    fi
    if ! git -C "${TAU_DIR_REAL}" merge-base --is-ancestor "${LOCAL_OID}" "${REMOTE_OID}"; then
      echo "error: local branch '${REF_NAME}' cannot fast-forward to 'origin/${REF_NAME}'" >&2
      echo "  local:  ${LOCAL_OID}" >&2
      echo "  remote: ${REMOTE_OID}" >&2
      echo "  preserve this checkout and use a separate --tau-dir" >&2
      exit 1
    fi
  fi
  git -C "${TAU_DIR_REAL}" checkout "${REF_NAME}"
  git -C "${TAU_DIR_REAL}" merge --ff-only "${REMOTE_BRANCH_REF}"
elif git -C "${TAU_DIR_REAL}" show-ref --verify --quiet "${REMOTE_BRANCH_REF}"; then
  git -C "${TAU_DIR_REAL}" checkout --track -b "${REF_NAME}" "${REMOTE_BRANCH_REF}"
elif git -C "${TAU_DIR_REAL}" show-ref --verify --quiet "${LOCAL_BRANCH_REF}"; then
  git -C "${TAU_DIR_REAL}" checkout "${REF_NAME}"
elif git -C "${TAU_DIR_REAL}" rev-parse --verify --quiet "${REF}^{commit}" >/dev/null; then
  git -C "${TAU_DIR_REAL}" checkout --detach "${REF}"
else
  echo "error: Tau ref does not resolve to a local branch, remote branch, tag, or commit: ${REF}" >&2
  exit 1
fi

RESOLVED_TAU_HEAD="$(git -C "${TAU_DIR_REAL}" rev-parse HEAD)"
if [[ "${RESOLVE_ONLY}" -eq 1 ]]; then
  echo "tau-lang git: ${RESOLVED_TAU_HEAD}"
  echo "resolve-only: source resolved; submodules and build were not run"
  exit 0
fi

git -C "${TAU_DIR_REAL}" submodule update --init --recursive

JOBS="$(command -v nproc >/dev/null 2>&1 && nproc || echo 4)"

# Some upstream branches are WIP and do not build under our toolchain flags
# (-Werror, unified tau.h generation, etc). Keep tiny, local build-fix patches
# in-repo so experimentation stays reproducible.
if [[ "${REF}" == "feature/bitblasting" ]] || [[ "${REF}" == "origin/feature/bitblasting" ]]; then
  for PATCH in \
    "${ROOT_REAL}/tools/patches/tau-lang/feature-bitblasting-buildfix.patch" \
    "${ROOT_REAL}/tools/patches/tau-lang/feature-bitblasting-semanticfix.patch" \
    "${ROOT_REAL}/tools/patches/tau-lang/local-cvc5-bv-perfopts.patch"
  do
    if [[ -f "${PATCH}" ]]; then
      if git -C "${TAU_DIR_REAL}" apply --reverse --check "${PATCH}" >/dev/null 2>&1; then
        echo "Tau patch already applied: $(basename "${PATCH}")"
      else
        if git -C "${TAU_DIR_REAL}" apply --check "${PATCH}" >/dev/null 2>&1; then
          echo "Applying Tau patch: $(basename "${PATCH}")"
          git -C "${TAU_DIR_REAL}" apply "${PATCH}"
        else
          echo "Warning: Tau patch no longer applies cleanly (possibly upstream changed). Skipping: $(basename "${PATCH}")" >&2
          echo "  Patch path: ${PATCH}" >&2
        fi
      fi
    fi
  done
fi

CMAKE_ARGS=(-DCMAKE_BUILD_TYPE="${BUILD_TYPE}")
if [[ "${PY_BINDINGS}" -eq 1 ]]; then
  CMAKE_ARGS+=(-DTAU_BUILD_BINDING_PYTHON=ON)
fi

cmake -S "${TAU_DIR_BUILD}" -B "${TAU_DIR_BUILD}/${BUILD_DIR}" "${CMAKE_ARGS[@]}"
cmake --build "${TAU_DIR_BUILD}/${BUILD_DIR}" -j "${JOBS}"

echo
echo "tau-lang git: ${RESOLVED_TAU_HEAD}"
"${TAU_DIR_REAL}/${BUILD_DIR}/tau" --version
