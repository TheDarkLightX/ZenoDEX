# FCIS M5-P4B5A B1B Revision 3.4 focused review packet

Review the configuration-semantic-validation and phase-DAG correction at exact
target commit:

```text
a8b9d191b91a3258e3d7857784bbd6067a0463e1
```

The target is documentation-only and unmounted. It accepts the Revision 3.3
review findings that:

```text
proposed content was root-matched without passing the frozen B1A validator
V2TransitionCandidate contained a receipt while the receipt depended on it
```

Start with:

```text
REVIEW_PROMPT.md
FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md
FCIS_M5_P4B5A_B1B_REVISION_3_3_CHATGPT_ADJUDICATION_20260729.md
```

Use only files declared in `SOURCE_MANIFEST.sha256` for the initial review.
Additional repository inspection is allowed only when a concrete finding
requires following a named caller, consumer, schema, or authority path. Record
every additional path. Do not explore unrelated directories.

Verify:

```bash
sha256sum -c \
  docs/research/prompts/fcis_m5_p4b5a_b1b_revision34_review_v1/SOURCE_MANIFEST.sha256

git merge-base --is-ancestor \
  a8b9d191b91a3258e3d7857784bbd6067a0463e1 HEAD
```

Return exactly one verdict:

```text
APPROVE_B1B1_REVISION_3_4_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```

Approval permits only the unchanged unmounted B1B-1 authority-header,
bootstrap-anchor-claim, and migration-manifest carriers; schemas; canonical
Python/Rust codecs and roots; shared vectors; and limited structural-checker
coverage. It does not approve a content decoder, semantic authority wrapper,
update command, pinned verifier, migration execution, committed V2 state, state
binding, transition cause, evaluation candidate, decision, receipt, bundle,
proof input, publication, or mount.
