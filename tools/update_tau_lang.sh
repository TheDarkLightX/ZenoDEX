#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
usage: tools/update_tau_lang.sh [--ref <remote-ref>] [--expected-commit <sha>]
       [--expected-parser-commit <sha>] [--expected-origin-url <url>]
       [--expected-parser-origin-url <url>] [--build-dir <dir>] [--tau-dir <dir>]
       [--python-bindings]

Updates (or clones) external/tau-lang and builds a Tau binary.

The requested ref is resolved only through origin's remote-tracking refs (or
an explicit full commit), then checked out detached. Expected commits must be
full 40-hex pins. Feature/bitblasting remains a research-only, non-promotable
patch lane.
EOF
}

die() {
  echo "error: $*" >&2
  exit 1
}

ROOT_REAL="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"

REF="main"
EXPECTED_COMMIT=""
EXPECTED_PARSER_COMMIT=""
EXPECTED_ORIGIN_URL="https://github.com/IDNI/tau-lang"
EXPECTED_PARSER_ORIGIN_URL="https://github.com/IDNI/parser.git"
BUILD_DIR="build-Release"
BUILD_TYPE="Release"
TAU_DIR_REL="external/tau-lang"
PY_BINDINGS=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --ref)
      [[ $# -ge 2 ]] || die "--ref requires a value"
      REF="$2"
      shift 2
      ;;
    --expected-commit)
      [[ $# -ge 2 ]] || die "--expected-commit requires a value"
      EXPECTED_COMMIT="$2"
      shift 2
      ;;
    --expected-parser-commit)
      [[ $# -ge 2 ]] || die "--expected-parser-commit requires a value"
      EXPECTED_PARSER_COMMIT="$2"
      shift 2
      ;;
    --expected-origin-url)
      [[ $# -ge 2 ]] || die "--expected-origin-url requires a value"
      EXPECTED_ORIGIN_URL="$2"
      shift 2
      ;;
    --expected-parser-origin-url)
      [[ $# -ge 2 ]] || die "--expected-parser-origin-url requires a value"
      EXPECTED_PARSER_ORIGIN_URL="$2"
      shift 2
      ;;
    --build-dir)
      [[ $# -ge 2 ]] || die "--build-dir requires a value"
      BUILD_DIR="$2"
      shift 2
      ;;
    --tau-dir)
      [[ $# -ge 2 ]] || die "--tau-dir requires a value"
      TAU_DIR_REL="$2"
      shift 2
      ;;
    --python-bindings)
      PY_BINDINGS=1
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

[[ -n "${REF}" ]] || die "--ref must be non-empty"
[[ -n "${BUILD_DIR}" ]] || die "--build-dir must be non-empty"
[[ -n "${TAU_DIR_REL}" ]] || die "--tau-dir must be non-empty"
[[ "${TAU_DIR_REL}" != /* ]] || die "--tau-dir must be a repo-relative path (e.g., external/tau-lang)"
[[ -n "${EXPECTED_ORIGIN_URL}" ]] || die "--expected-origin-url must be non-empty"
[[ -n "${EXPECTED_PARSER_ORIGIN_URL}" ]] || die "--expected-parser-origin-url must be non-empty"

full_pin_or_empty() {
  local name="$1"
  local value="$2"
  if [[ -n "${value}" && ! "${value}" =~ ^[0-9a-fA-F]{40}$ ]]; then
    die "${name} must be a full 40-hex commit"
  fi
}

full_pin_or_empty "--expected-commit" "${EXPECTED_COMMIT}"
full_pin_or_empty "--expected-parser-commit" "${EXPECTED_PARSER_COMMIT}"
EXPECTED_COMMIT="${EXPECTED_COMMIT,,}"
EXPECTED_PARSER_COMMIT="${EXPECTED_PARSER_COMMIT,,}"

if [[ ! "${TAU_BUILD_JOBS:-}" =~ ^[1-9][0-9]*$ ]] || [[ "${TAU_BUILD_JOBS:-0}" -gt 16 ]]; then
  if [[ -n "${TAU_BUILD_JOBS:-}" ]]; then
    die "TAU_BUILD_JOBS must be a positive integer between 1 and 16"
  fi
fi
if [[ -n "${TAU_BUILD_JOBS:-}" ]]; then
  JOBS="${TAU_BUILD_JOBS}"
else
  DETECTED_JOBS="$(command -v nproc >/dev/null 2>&1 && nproc || echo 4)"
  if [[ ! "${DETECTED_JOBS}" =~ ^[1-9][0-9]*$ ]] || [[ "${DETECTED_JOBS}" -gt 4 ]]; then
    JOBS=4
  else
    JOBS="${DETECTED_JOBS}"
  fi
fi

# Tau's CMake build currently breaks when the source/build path contains spaces.
# Work around by building through a no-space symlink path while keeping the repo
# location unchanged.
ROOT_BUILD="${ROOT_REAL}"
ROOT_SYMLINK=""
if [[ "${ROOT_REAL}" == *" "* ]]; then
  SAFE_BASE="$(basename "${ROOT_REAL}" | tr ' ' '_' )"
  ROOT_SYMLINK="/tmp/codex_ws_${SAFE_BASE}"
  if [[ -L "${ROOT_SYMLINK}" ]]; then
    if [[ "$(readlink "${ROOT_SYMLINK}")" != "${ROOT_REAL}" ]]; then
      rm -f "${ROOT_SYMLINK}"
    fi
  elif [[ -e "${ROOT_SYMLINK}" ]]; then
    die "${ROOT_SYMLINK} exists and is not a symlink; remove it or choose a different workspace path"
  fi
  if [[ ! -e "${ROOT_SYMLINK}" ]]; then
    ln -s "${ROOT_REAL}" "${ROOT_SYMLINK}"
  fi
  ROOT_BUILD="${ROOT_SYMLINK}"
  echo "Note: workspace path contains spaces; building Tau via symlink: ${ROOT_BUILD}"
fi

TAU_DIR_REAL="$(realpath -m "${ROOT_REAL}/${TAU_DIR_REL}")"
case "${TAU_DIR_REAL}" in
  "${ROOT_REAL}"/*) ;;
  *) die "--tau-dir must resolve inside the repository" ;;
esac
TAU_DIR_REL_NORMALIZED="${TAU_DIR_REAL#"${ROOT_REAL}/"}"
TAU_DIR_BUILD="${ROOT_BUILD}/${TAU_DIR_REL_NORMALIZED}"

BUILD_DIR_REAL="$(realpath -m "${TAU_DIR_REAL}/${BUILD_DIR}")"
case "${BUILD_DIR_REAL}" in
  "${TAU_DIR_REAL}"/*) ;;
  *) die "--build-dir must resolve inside the Tau checkout" ;;
esac
BUILD_DIR_REL_NORMALIZED="${BUILD_DIR_REAL#"${TAU_DIR_REAL}/"}"
BUILD_DIR_BUILD="${TAU_DIR_BUILD}/${BUILD_DIR_REL_NORMALIZED}"

repo_is_initialized() {
  local repo="$1"
  local top
  [[ -d "${repo}" ]] || return 1
  top="$(git -C "${repo}" rev-parse --show-toplevel 2>/dev/null)" || return 1
  [[ "$(realpath "${top}")" == "$(realpath "${repo}")" ]]
}

assert_clean_worktree() {
  local repo="$1"
  local label="$2"
  local status
  status="$(git -C "${repo}" status --porcelain=v1 --untracked-files=all --ignore-submodules=none)"
  [[ -z "${status}" ]] || die "${label} worktree is dirty; refusing to update"
}

if [[ ! -d "${TAU_DIR_REAL}" ]]; then
  mkdir -p "$(dirname "${TAU_DIR_REAL}")"
  git clone "${EXPECTED_ORIGIN_URL}" "${TAU_DIR_REAL}"
fi

repo_is_initialized "${TAU_DIR_REAL}" || die "Tau source directory is not a Git worktree"
PARSER_DIR="${TAU_DIR_REAL}/external/parser"

# Check nested source state before fetch/checkout. A dirty parser is called out
# separately because the root worktree reports it as a gitlink change.
if repo_is_initialized "${PARSER_DIR}"; then
  assert_clean_worktree "${PARSER_DIR}" "parser"
fi
assert_clean_worktree "${TAU_DIR_REAL}" "source"

ORIGIN_URL="$(git -C "${TAU_DIR_REAL}" remote get-url origin)"
[[ -n "${ORIGIN_URL}" ]] || die "Tau source origin URL is empty"
[[ "${ORIGIN_URL}" == "${EXPECTED_ORIGIN_URL}" ]] || die "Tau origin URL mismatch: expected ${EXPECTED_ORIGIN_URL}, got ${ORIGIN_URL}"

# Fetch is the only ref movement operation. Never prefer refs/heads/<REF> and
# never pull after resolving the remote-tracking ref: the fetched object is the
# immutable input for this invocation, even when origin was force-pushed.
git -C "${TAU_DIR_REAL}" fetch --prune origin

REMOTE_REF="${REF}"
case "${REMOTE_REF}" in
  origin/*)
    REMOTE_REF="${REMOTE_REF#origin/}"
    ;;
  refs/remotes/origin/*)
    REMOTE_REF="${REMOTE_REF#refs/remotes/origin/}"
    ;;
  refs/heads/*)
    REMOTE_REF="${REMOTE_REF#refs/heads/}"
    ;;
esac

if [[ "${REMOTE_REF}" =~ ^[0-9a-fA-F]{40}$ ]]; then
  git -C "${TAU_DIR_REAL}" cat-file -e "${REMOTE_REF}^{commit}" || die "requested commit is not available locally"
  RESOLVED_COMMIT="$(git -C "${TAU_DIR_REAL}" rev-parse --verify "${REMOTE_REF}^{commit}")"
  CONTAINING_ORIGIN_REFS="$(git -C "${TAU_DIR_REAL}" for-each-ref --format='%(refname)' --contains "${RESOLVED_COMMIT}" refs/remotes/origin/)"
  [[ -n "${CONTAINING_ORIGIN_REFS}" ]] || die "requested commit is not reachable from an origin remote-tracking ref"
else
  git check-ref-format "refs/remotes/origin/${REMOTE_REF}" >/dev/null 2>&1 || die "invalid remote ref: ${REF}"
  REMOTE_TRACKING_REF="refs/remotes/origin/${REMOTE_REF}"
  git -C "${TAU_DIR_REAL}" show-ref --verify --quiet "${REMOTE_TRACKING_REF}" || die "origin remote ref not found: ${REF}"
  RESOLVED_COMMIT="$(git -C "${TAU_DIR_REAL}" rev-parse --verify "${REMOTE_TRACKING_REF}^{commit}")"
fi

[[ "${RESOLVED_COMMIT}" =~ ^[0-9a-fA-F]{40}$ ]] || die "resolved source ref is not a full commit"
if [[ -n "${EXPECTED_COMMIT}" && "${RESOLVED_COMMIT}" != "${EXPECTED_COMMIT}" ]]; then
  die "expected root commit ${EXPECTED_COMMIT}, resolved ${RESOLVED_COMMIT}"
fi

git -C "${TAU_DIR_REAL}" checkout --detach "${RESOLVED_COMMIT}"
git -C "${TAU_DIR_REAL}" submodule update --init --recursive

FINAL_ROOT_HEAD="$(git -C "${TAU_DIR_REAL}" rev-parse HEAD)"
[[ "${FINAL_ROOT_HEAD}" == "${RESOLVED_COMMIT}" ]] || die "final root HEAD does not match resolved source commit"
FINAL_ORIGIN_URL="$(git -C "${TAU_DIR_REAL}" remote get-url origin)"
[[ "${FINAL_ORIGIN_URL}" == "${ORIGIN_URL}" ]] || die "root origin URL changed during update"
[[ "${FINAL_ORIGIN_URL}" == "${EXPECTED_ORIGIN_URL}" ]] || die "Tau origin URL mismatch after update"

GITLINK_LINE="$(git -C "${TAU_DIR_REAL}" ls-tree HEAD -- external/parser)"
GITLINK_MODE="$(awk '{print $1}' <<<"${GITLINK_LINE}")"
PARSER_GITLINK="$(awk '{print $3}' <<<"${GITLINK_LINE}")"
[[ "${GITLINK_MODE}" == "160000" && "${PARSER_GITLINK}" =~ ^[0-9a-fA-F]{40}$ ]] || die "root external/parser gitlink is missing or malformed"

PARSER_HEAD="$(git -C "${PARSER_DIR}" rev-parse HEAD)"
[[ "${PARSER_HEAD}" == "${PARSER_GITLINK}" ]] || die "parser HEAD does not match root external/parser gitlink"
DECLARED_PARSER_ORIGIN_URL="$(git -C "${TAU_DIR_REAL}" config -f .gitmodules --get submodule.external/parser.url)"
[[ "${DECLARED_PARSER_ORIGIN_URL}" == "${EXPECTED_PARSER_ORIGIN_URL}" ]] || die "declared parser origin URL mismatch: expected ${EXPECTED_PARSER_ORIGIN_URL}, got ${DECLARED_PARSER_ORIGIN_URL}"
PARSER_ORIGIN_URL="$(git -C "${PARSER_DIR}" remote get-url origin)"
[[ "${PARSER_ORIGIN_URL}" == "${EXPECTED_PARSER_ORIGIN_URL}" ]] || die "parser origin URL mismatch: expected ${EXPECTED_PARSER_ORIGIN_URL}, got ${PARSER_ORIGIN_URL}"
if [[ -n "${EXPECTED_PARSER_COMMIT}" && "${PARSER_HEAD}" != "${EXPECTED_PARSER_COMMIT}" ]]; then
  die "expected parser commit ${EXPECTED_PARSER_COMMIT}, resolved ${PARSER_HEAD}"
fi

assert_clean_worktree "${PARSER_DIR}" "parser"
assert_clean_worktree "${TAU_DIR_REAL}" "source"
# This command deliberately propagates any nested-submodule status or Git
# failure; it is a verification gate, not an advisory status probe.
git -C "${TAU_DIR_REAL}" submodule foreach --quiet --recursive \
  'test -z "$(git status --porcelain=v1 --untracked-files=all --ignore-submodules=none)"'

# Preserve this exact experimental lane only. These patches are deliberately
# non-promotable and remain outside the normal source-cleanliness guarantee.
if [[ "${REF}" == "feature/bitblasting" ]] || [[ "${REF}" == "origin/feature/bitblasting" ]]; then
  echo "WARNING: feature/bitblasting patches are research-only and non-promotable" >&2
  for PATCH in \
    "${ROOT_REAL}/tools/patches/tau-lang/feature-bitblasting-buildfix.patch" \
    "${ROOT_REAL}/tools/patches/tau-lang/feature-bitblasting-semanticfix.patch" \
    "${ROOT_REAL}/tools/patches/tau-lang/local-cvc5-bv-perfopts.patch"
  do
    if [[ -f "${PATCH}" ]]; then
      if git -C "${TAU_DIR_REAL}" apply --reverse --check "${PATCH}" >/dev/null 2>&1; then
        echo "Tau patch already applied: $(basename "${PATCH}")"
      elif git -C "${TAU_DIR_REAL}" apply --check "${PATCH}" >/dev/null 2>&1; then
        echo "Applying Tau patch: $(basename "${PATCH}")"
        git -C "${TAU_DIR_REAL}" apply "${PATCH}"
      else
        echo "Warning: Tau patch no longer applies cleanly (possibly upstream changed). Skipping: $(basename "${PATCH}")" >&2
        echo "  Patch path: ${PATCH}" >&2
      fi
    fi
  done
fi

CMAKE_ARGS=(-DCMAKE_BUILD_TYPE="${BUILD_TYPE}")
if [[ "${PY_BINDINGS}" -eq 1 ]]; then
  CMAKE_ARGS+=(-DTAU_BUILD_BINDING_PYTHON=ON)
fi

cmake -S "${TAU_DIR_BUILD}" -B "${BUILD_DIR_BUILD}" "${CMAKE_ARGS[@]}"
cmake --build "${BUILD_DIR_BUILD}" -j "${JOBS}"

BINARY="${BUILD_DIR_REAL}/tau"
[[ -x "${BINARY}" ]] || die "Tau binary was not produced: ${BINARY}"
BINARY_SHA256="$(sha256sum "${BINARY}" | awk '{print $1}')"
TAU_VERSION="$("${BINARY}" --version)"

RESOLVED_LOWER="${RESOLVED_COMMIT,,}"
VERSION_MATCH=0
while IFS= read -r VERSION_HASH; do
  VERSION_HASH_LOWER="${VERSION_HASH,,}"
  if [[ "${#VERSION_HASH_LOWER}" -ge 7 && "${RESOLVED_LOWER}" == "${VERSION_HASH_LOWER}"* ]]; then
    VERSION_MATCH=1
    break
  fi
done < <(printf '%s\n' "${TAU_VERSION}" | grep -Eo '[0-9a-fA-F]{7,40}' || true)
[[ "${VERSION_MATCH}" -eq 1 ]] || die "Tau --version does not contain resolved source commit ${RESOLVED_COMMIT:0:7}"

echo
echo "origin URL: ${FINAL_ORIGIN_URL}"
echo "source SHA: ${RESOLVED_COMMIT}"
echo "parser SHA: ${PARSER_HEAD}"
echo "binary SHA-256: ${BINARY_SHA256}"
echo "tau version: ${TAU_VERSION}"
