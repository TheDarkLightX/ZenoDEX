# FCIS M5-P4B5A B1B Revision 3.2 focused review packet

Review the whole-state source-binding correction at exact target commit:

```text
27bfde2a5679250e949d397960d6dba09117c6bd
```

The target is documentation-only and unmounted. It accepts the Revision 3.1
counterexample in which an allowed ordinary transition preserved a
configuration root from a directly constructed `pre` header rather than from
the exact authenticated pre-state.

Start with:

```text
REVIEW_PROMPT.md
FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_2_20260729.md
FCIS_M5_P4B5A_B1B_REVISION_3_1_CHATGPT_ADJUDICATION_20260729.md
```

Use only files declared in `SOURCE_MANIFEST.sha256` for the initial review.
Additional repository inspection is allowed only when a concrete finding
requires following a named caller, consumer, schema, or authority path. Record
every additional path. Do not explore unrelated directories.

Verify:

```bash
sha256sum -c \
  docs/research/prompts/fcis_m5_p4b5a_b1b_revision32_review_v1/SOURCE_MANIFEST.sha256

git merge-base --is-ancestor \
  27bfde2a5679250e949d397960d6dba09117c6bd HEAD
```

Return exactly one verdict:

```text
APPROVE_B1B1_REVISION_3_2_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```

Approval permits only the unmounted B1B-1 authority-header,
bootstrap-anchor-claim, and migration-manifest carriers; schemas; canonical
Python/Rust codecs and roots; shared vectors; and limited structural-checker
coverage. It does not approve a pinned verifier, migration execution, committed
V2 state, state binding, configuration update, receipt, bundle, proof input,
publication, or mount.

