# FCIS M6 E07 transport-loss schema

Status: `IMPLEMENTED_TESTED_RESEARCH_ONLY_UNMOUNTED`

E07 separates transport knowledge from durable outcome. Four loss points are
modeled:

```text
before request reaches server
after validation before transaction
after transaction commit before response
after response generation during transport
```

The first two points leave the database at PRE. A fresh E04 lookup returns
`ABSENT_RETRYABLE` with client knowledge `INDETERMINATE`; a subsequent E05
submission commits once.

The last two points leave the database at POST while the response is lost. A
fresh E04 lookup against the post-state returns `ALREADY_COMMITTED` with
client knowledge `INDETERMINATE`. A blind resubmission carrying the old
pre-state receives `STALE_SNAPSHOT_CAS`, and the durable publication remains
unique.

The model creates no network connection and does not claim a process-crash
surrogate. It tests the semantic contract that a fresh canonical lookup
resolves the durable class after transport uncertainty.
