#!/bin/bash
# Formal-core candidate chain (research tooling; grants no authority).
#
# Turns the staged source write set into the two-commit S/P chain the O-008 packet checker admits:
#   1. commit S (the source candidate) from the given message file;
#   2. run the repository test-hygiene gate against the parent of S AND against the campaign base
#      (the parent-only gate cannot see a packet selected for a path changed by an earlier commit);
#   3. build the packet with proof replay, commit P (artifact-only child);
#   4. re-check P with the packet checker (replay), the builder round trip, and the committed-packet
#      lifecycle test at P;
#   5. push and tag.
# Every Lean-bearing step takes the shared lock. A red step before P stops the chain before P exists;
# a red re-check after P stops it before the push and the tag, so P then exists only locally
# (Opus P34 P2-4).
#
# usage: bash tools/formal_core_candidate_chain_v1.sh <message-file> <packet-label> <tag> <report.json>   (stored non-executable: the packet pins sources as mode 100644)
# env:   FORMAL_CORE_PY, FORMAL_CORE_ESSO_PYTHONPATH, FORMAL_CORE_ESSO_PYTHON, FORMAL_CORE_LEAN_LOCK,
#        FORMAL_CORE_DEEP_BASE (default: the campaign handoff commit), FORMAL_CORE_BRANCH, FORMAL_CORE_CREATED_DATE
set -u
MSG="$1"; LABEL="$2"; TAG="$3"; REPORT="$4"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT" || exit 1
PY="${FORMAL_CORE_PY:-$ROOT/.venv/bin/python}"
LOCK="${FORMAL_CORE_LEAN_LOCK:-/tmp/zenodex-lean.lock}"
ESSO_PP="${FORMAL_CORE_ESSO_PYTHONPATH:-$ROOT/external/ESSO}"
ESSO_PY="${FORMAL_CORE_ESSO_PYTHON:-/usr/bin/python3}"
DEEP_BASE="${FORMAL_CORE_DEEP_BASE:-fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85}"
BRANCH="${FORMAL_CORE_BRANCH:-$(git rev-parse --abbrev-ref HEAD)}"
DATE="${FORMAL_CORE_CREATED_DATE:-$(date -u +%F)}"
export PYTHONDONTWRITEBYTECODE=1
PACKET_JSON=docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
PACKET_MD=docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
git add -A src/core src/kernels tools tests lean-mathlib zk/global_settlement_abi_v1 && git commit -q -F "$MSG" || exit 1
S=$(git rev-parse HEAD); echo "S=$S $(date -u +%FT%TZ)"
"$PY" tools/check_test_hygiene_v1.py --base-ref "$S^" --json > "${REPORT%.json}_hygiene_at_S.json" 2>&1 || { echo "HYGIENE RED at S vs parent: $(head -c 300 "${REPORT%.json}_hygiene_at_S.json")"; exit 1; }
"$PY" tools/check_test_hygiene_v1.py --base-ref "$DEEP_BASE" --json > "${REPORT%.json}_hygiene_deep.json" 2>&1 || { echo "HYGIENE RED at S vs campaign base $DEEP_BASE: $(head -c 300 "${REPORT%.json}_hygiene_deep.json")"; exit 1; }
echo "hygiene at S ok (parent and campaign base)"
flock -w 7200 "$LOCK" "$PY" tools/build_o008_formal_cycle_v1.py --root "$PWD" --subject-commit "$S" --created-date "$DATE" \
  --replay --esso-python "$ESSO_PY" --esso-pythonpath "$ESSO_PP" --output-json "$PACKET_JSON" --output-md "$PACKET_MD" || { echo "builder FAILED"; exit 1; }
echo "builder exit 0"
git add "$PACKET_JSON" "$PACKET_MD" && git commit -q -m "docs: freeze the O-008 formal-cycle packet at $LABEL" || exit 1
P=$(git rev-parse HEAD); echo "P=$P $(date -u +%FT%TZ)"
git diff-tree --no-commit-id --name-status -r "$S" "$P"
flock -w 7200 "$LOCK" "$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit "$P" --replay --esso-python "$ESSO_PY" --esso-pythonpath "$ESSO_PP" > "$REPORT" 2>&1
CHK=$?; echo "checker replay exit $CHK"; [ "$CHK" = 0 ] || { echo "CHECKER REPLAY RED at P: not pushed, not tagged"; exit 1; }
flock -w 7200 "$LOCK" "$PY" tools/build_o008_formal_cycle_v1.py --root "$PWD" --subject-commit "$S" --created-date "$DATE" --check --replay \
  --esso-python "$ESSO_PY" --esso-pythonpath "$ESSO_PP" --output-json "$PACKET_JSON" --output-md "$PACKET_MD"
BLD=$?; echo "builder check exit $BLD"; [ "$BLD" = 0 ] || { echo "BUILDER CHECK RED at P: not pushed, not tagged"; exit 1; }
"$PY" -m pytest -q -p no:cacheprovider tests/test_check_o008_formal_cycle_v1.py::test_committed_packet_lifecycle_at_repository_head > "${REPORT%.json}_lifecycle_at_P.log" 2>&1; LC=$?; echo "lifecycle at P exit $LC"; [ "$LC" = 0 ] || { echo "LIFECYCLE RED at P: not pushed, not tagged"; exit 1; }
git push -q origin "$BRANCH" && echo pushed || { echo "PUSH FAILED"; exit 1; }
git tag "$TAG" "$P" && echo "tagged $TAG" || { echo "TAG FAILED"; exit 1; }
sha256sum "$PACKET_JSON"
echo "chain done $(date -u +%FT%TZ)"
