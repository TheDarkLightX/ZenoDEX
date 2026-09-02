#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
TAU_REF="${1:?usage: build_tau_adt_research_pin_v1.sh <tau-ref> [tau-dir] [build-dir]}"
TAU_DIR_REL="${2:-external/tau-lang-adt-logical-abi-v1}"
BUILD_DIR="${3:-build-Release}"
TAU_DIR="${ROOT}/${TAU_DIR_REL}"

# Resolve the exact source with the repository's fail-closed updater, but do
# not let that helper auto-parallelize the heavy cvc5 dependency build.
bash "${ROOT}/tools/update_tau_lang.sh" \
  --ref "${TAU_REF}" \
  --tau-dir "${TAU_DIR_REL}" \
  --build-dir "${BUILD_DIR}" \
  --resolve-only

git -C "${TAU_DIR}" submodule update --init --recursive

# Tau's CMake passes TAU_BUILD_JOBS to its pinned cvc5 dependency builder.
# GitHub-hosted runners expose many logical CPUs but substantially less memory;
# the auto-parallel cvc5 build was observed to OOM-kill cc1plus around 51-54%.
# One job is slower but deterministic and memory-bounded enough for replay CI.
export TAU_BUILD_JOBS=1

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
