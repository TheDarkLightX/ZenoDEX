# M6 Task Report Schema V1

Every implementation-task report under `docs/research/m6_tasks/` uses these
fields in this order. Values are plain text unless a field is explicitly
marked as a hash or a list.

```text
# FCIS M6 Task <id> Report

TASK_ID: <stable task ID>
BASE_SHA: <40 lowercase hexadecimal Git commit>
SOURCE_HEAD_SHA: <40 lowercase hexadecimal Git commit or NONE>
SOURCE_HEAD_TREE: <40 lowercase hexadecimal Git tree or NONE>
BRANCH: <exact local or remote branch name>
FILES_CHANGED:
- <repository-relative path>
CLAIM_IMPLEMENTED: <scoped claim>
COMMANDS_RUN:
- <exact command>
RESULTS:
- <observable result>
MUTANTS_ADDED: <None or named mutants>
FORMAL_EVIDENCE: <formal evidence or None>
REMAINING_NONCLAIMS:
- <claim deliberately not made>
REVIEW_RISKS: <residual review risks>
```

The report must name the exact source head, distinguish the task commit from
the reviewed source packet, and state what remains unproved or unmounted.
The report is descriptive evidence. It does not promote a task status by
itself.
