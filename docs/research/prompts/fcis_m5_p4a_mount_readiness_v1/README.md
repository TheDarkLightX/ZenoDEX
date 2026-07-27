# FCIS M5-P4A mount-readiness packet

Status: semantically approved prerequisite checkpoint

Visibility: repository-local

Milestone: M5-P4A only

Required reviewed source ancestor:

```text
c669aa678f04498cb9c08f0c6f6489fd07d0b6f1
```

P4A captures the final mounted-legacy baseline, builds the exact-vs-legacy
differential oracle, inventories the mounted authority call graph, and emits a
fail-closed readiness decision. It does not switch authority.

The implementation agent must read, in order:

1. `IMPLEMENTATION_PROMPT.md` in this folder.
2. `REVIEW_CHECKLIST.md` in this folder.
3. Every repository file named by the implementation prompt.

## Fast start

```bash
git fetch origin
git worktree add /tmp/zenodex-fcis-m5-p4a-20260726 \
  -b agent/fcis-m5-p4a-readiness-20260726 \
  origin/agent/fcis-m5-p3-commit-bundle-20260726
cd /tmp/zenodex-fcis-m5-p4a-20260726
git merge-base --is-ancestor \
  c669aa678f04498cb9c08f0c6f6489fd07d0b6f1 HEAD
git status --short
```

Stop if the ancestor check fails or the worktree is not clean.

## Authorized outcome

The agent may return exactly one of:

```text
M5_P4A_READY_FOR_REVIEWED_SWITCH
M5_P4A_BLOCKED_NO_AUTHORITY_SWITCH
```

`READY` requires every readiness row and differential fixture to be closed with
source-pinned evidence. A missing Rust/verifier parity row, unknown mounted
consumer, stale artifact, or unexplained final-mount finding forces `BLOCKED`.

The agent must stop after one local P4A commit. It must not edit `src/core/dex.py`,
mount a new runtime path, delete legacy code, push, merge, or begin P4B/P5/M6.
