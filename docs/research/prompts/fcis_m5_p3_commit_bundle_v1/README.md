# FCIS M5-P3 implementation packet

Status: semantically approved implementation handoff

Visibility: repository-local

Milestone: M5-P3 only

Required source ancestors:

```text
b19bb0e1  M5-P1 support-root v5 and read containment
79e3ff11  M5-P2 controlled decision source
f21ef0f7  M5-P2 evidence note
```

The implementation agent must read, in order:

1. `IMPLEMENTATION_PROMPT.md` in this folder.
2. `REVIEW_CHECKLIST.md` in this folder.
3. The repository files named by the prompt.

The prompt authorizes one isolated local P3 implementation branch, focused
tests, structural-checker updates, and local commits. It does not authorize a
mount, legacy deletion, force-push, merge, PR approval, or production claim.
The reviewer will inspect and push accepted commits.

## Fast start

```bash
git fetch origin
git worktree add /tmp/zenodex-fcis-m5-p3-20260726 \
  -b agent/fcis-m5-p3-commit-bundle-20260726 \
  origin/agent/fcis-m5-authority-mount-20260725
cd /tmp/zenodex-fcis-m5-p3-20260726
git merge-base --is-ancestor 79e3ff11 HEAD
git status --short
```

Stop if the ancestry command fails, the worktree is dirty, or the remote branch
does not contain this packet.

## Terminal outcome

The task is complete only when one local checkpoint commit implements and
tests:

```text
DecisionV1
  -> controlled immutable CommitBundleV1 | existing RejectV1
  -> pure immutable expected-root reference commit result
```

The mounted DEX path must remain byte-for-byte unchanged. The `final-mount`
profile is expected to remain blocked until P4/P5.

## Handoff

Return the exact start and end SHAs, changed paths, commands and results,
unavailable lanes, residual risks, and the local commit SHA. Do not push. The
reviewer will grade the result using `REVIEW_CHECKLIST.md`, inspect the diff,
run the mutation suite, and make any required corrective commit.
