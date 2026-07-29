# FCIS M5-P4B5A B1B Revision 3.4 and B1B-1 review packet

Review the semantic-validation closure and unmounted carrier implementation at exact target commit:

```text
e28f5806a05ea621595d86ccc55190acbf324c4c
```

The target is unmounted. It repairs the Revision 3.3 error in which command-root equality could install a structurally admitted but B1A-invalid configuration, and it separates the evaluation candidate from receipt-bearing decision authority.

Start with:

```text
REVIEW_PROMPT.md
FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md
FCIS_M5_P4B5A_B1B1_REVISION34_IMPLEMENTATION_REPORT_20260729.md
```

Use only files declared in `SOURCE_MANIFEST.sha256` for the initial review. Follow additional repository paths only for a concrete named caller, consumer, schema, or authority finding, and record each extra path.

Verify:

```bash
sha256sum -c \
  docs/research/prompts/fcis_m5_p4b5a_b1b_revision34_review_v1/SOURCE_MANIFEST.sha256

git merge-base --is-ancestor \
  e28f5806a05ea621595d86ccc55190acbf324c4c HEAD

python tools/build_fcis_b1b_authority_v2_golden.py --check
python tools/fcis_b1b_revision34_adversarial_model.py
python tools/check_fcis_b1b_revision34_contract.py
```

Return exactly one verdict:

```text
APPROVE_B1B1_REVISION_3_4_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```

Approval applies only to the untrusted B1B-1 authority-header, bootstrap-anchor-claim, and migration-manifest carriers, schemas, codecs, roots, shared vectors, and structural evidence. It does not approve a pinned verifier, migration execution, committed V2 state, state binding, configuration update, receipt, decision, bundle, proof input, publication, datastore adapter, or runtime mount.
