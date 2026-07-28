# FCIS M5-P4B5A B1B Revision 3 focused review packet

Review the authority correction at exact target commit:

```text
798f4ba862ff07cf1f92b54946c67e13e7a939b6
```

The target is documentation-only and unmounted. Its purpose is to repair the
deployment-bootstrap counterexample found in B1B Revision 2. It does not
authorize implementation, migration, state-root integration, or mounting.

Start with:

```text
REVIEW_PROMPT.md
FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_20260728.md
```

Use only files declared in `SOURCE_MANIFEST.sha256` for the initial review.
That keeps the review bounded and excludes prior model verdicts. Additional
repository inspection is allowed only when a concrete finding requires
following a named caller, consumer, schema, or authority path. Record every
additional path.

Verify:

```bash
sha256sum -c \
  docs/research/prompts/fcis_m5_p4b5a_b1b_revision3_review_v1/SOURCE_MANIFEST.sha256

git merge-base --is-ancestor \
  798f4ba862ff07cf1f92b54946c67e13e7a939b6 HEAD
```

Return exactly one verdict:

```text
APPROVE_B1B1_REVISION_3_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```

Approval permits only the unmounted B1B-1 values, schemas, canonical
Python/Rust codecs, and shared vectors named in Revision 3. It does not approve
later state binding, migration execution, publication, or mounting.
