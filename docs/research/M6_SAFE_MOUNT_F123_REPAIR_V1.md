# M6 safe-mount F1/F2/F3 repair evidence

Status: research-only hardening evidence. It does not establish `M6Ready`, a
production writer, settlement authority, or deployment readiness.

Subjects:

- Base source subject: `e8059cb5e27e80c2f8ba627501d6097f3c5e6b0c`
- Verified repair descendant: `ea25e6ec70ef0aca4881d671a34d00d5dcef06b2`

The repair closes three scoped boundary families identified during the exact
subject audit.

## F1: post-install descriptor cleanup

`_write_bundle_directory` now classifies a descriptor cleanup failure after
the block rename as a typed post-install uncertainty. The durable publisher
validates the exact installed block against the already verified publication,
re-drives the compare-and-swap `HEAD` update, and reopens the complete chain.
The existing fail-closed behavior for an uncertain commit-parent directory
fsync remains unchanged: an orphan is rejected on reopen.

Permanent evidence:

- `test_post_install_descriptor_close_failure_recovers_idempotently`
- `test_commit_parent_fsync_failure_leaves_orphan_rejected_on_reopen`
- `test_head_parent_fsync_failure_reopens_and_retry_is_idempotent`

## F2: nested finality ownership

The commit and durable publication entrypoints detach every finality field and
the separately supplied Tau certificate before any comparison, hashing,
adapter call, replay check, or publication lock. Exact reconstructed values
reject executable subclasses and inconsistent roots. Direct, ZRPF, direct-batch,
and durable routes use the same ownership seam.

Permanent evidence:

- `test_durable_publication_detaches_nested_finality_before_lock_hooks`
- the existing exact finality subclass rejection test
- the full M6 core/durable test pair

## F3: hostile path ingress

`M6DurableLedgerStoreV1.__init__` and `.create` accept only an exact built-in
`str` or the native concrete `Path` representation. The value is checked before
any filesystem conversion, so a caller-defined `__fspath__` hook cannot run.

Permanent evidence:

- `test_durable_root_rejects_hostile_fspath_before_conversion`

Current nonclaims:

- The M6 shell remains explicitly research-only and is not a production
  ZenoLedger writer.
- G1 still has open economic-policy, terminal-path, global-state, and
  production-mount decisions.
- The repair does not supply validator cryptography, proof promotion, dynamic
  reachability, credentials, deployment wiring, or a complete value-lifecycle
  receipt.
