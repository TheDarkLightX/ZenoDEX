#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
TAU_REF="${1:?usage: build_tau_adt_research_pin_v1.sh <tau-ref> [tau-dir] [build-dir]}"
TAU_DIR_REL="${2:-external/tau-lang-adt-logical-abi-v1}"
BUILD_DIR="${3:-build-Release}"
TAU_DIR="${ROOT}/${TAU_DIR_REL}"

# Resolve the exact source with the repository's fail-closed updater, but do
# not let that helper auto-parallelize the heavy pinned dependency builds.
bash "${ROOT}/tools/update_tau_lang.sh" \
  --ref "${TAU_REF}" \
  --tau-dir "${TAU_DIR_REL}" \
  --build-dir "${BUILD_DIR}" \
  --resolve-only

git -C "${TAU_DIR}" submodule update --init --recursive

# Tau's dependency scripts accept TAU_BUILD_JOBS. GitHub-hosted runners expose
# many logical CPUs relative to memory; the auto-parallel cvc5 build was
# observed to OOM-kill cc1plus. Build Tau's exact pinned cvc5 and Boost/log
# dependencies explicitly with one job before configuring Tau. Upstream CMake
# only auto-builds Boost for PIC/Windows configurations, so a clean Linux
# non-PIC checkout otherwise fails at find_package(Boost COMPONENTS log).
export TAU_BUILD_JOBS=1
(
  cd "${TAU_DIR}"
  bash ./dev dep-cvc5.sh -DTAU_BUILD_JOBS=1
  bash ./dev dep-boost.sh -DTAU_BUILD_JOBS=1 -DTAU_BUILD_PIC=OFF
)

cmake \
  -S "${TAU_DIR}" \
  -B "${TAU_DIR}/${BUILD_DIR}" \
  -DCMAKE_BUILD_TYPE=Release \
  -DTAU_BUILD_JOBS=1 \
  -DTAU_DONT_USE_FTXUI=ON

cmake --build "${TAU_DIR}/${BUILD_DIR}" --target tau --parallel 1

test -x "${TAU_DIR}/${BUILD_DIR}/tau"
test "$(git -C "${TAU_DIR}" rev-parse HEAD)" = "${TAU_REF}"

echo "tau-adt-research-build-v1: exact source ${TAU_REF}"
"${TAU_DIR}/${BUILD_DIR}/tau" --version
