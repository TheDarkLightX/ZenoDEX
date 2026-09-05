# Isolated economic verifier factory review

Date: 2026-09-04. Independent bounded review. Authority: `NONE`.
Git HEAD at review start: `051ecaa47682c2116d99c58e99ace3d800cfedf0`.
The modifications were uncommitted; the hashes below identify the actual subject.

Completion note: the bridge dependency changed after replay from recorded
`0393f291...` to `5e727d826ea298559e3bc2136fe96dec62f2d56eb66e6488771e652b699fcd47`.
The frozen source archive supplied the reviewed old bytes. Removing docstrings
and comparing complete Python ASTs established that this change only corrects
documentation: receipt codec belongs to the selected endpoint. The five direct
factory/purpose review subjects retain the hashes recorded below. Later
publisher extensions require their own review subject.

Verdict: no blocking behavioral defect found in the stated root-only factory
and publisher-purpose change. **Current qualification is blocked by a retained
canonical source-closure gate failure.** This is an advisory source/local-test
assessment, with no production or whole-program safety verdict. This review
changes only this report.

## IVR-01: canonical source evidence requires explicit review update

The expanded replay returned **124 passed, 1 failed**. The sole failure is
`tests/test_check_global_settlement_canonical_manifest_v1.py::test_repository_canonical_manifest_source_closure_passes`:

```text
canonical source closure digest is
e4cb0e935d5996b1e7b0978bd898673add91fc1f2f68a051b819440661366dbd;
expected
e577e288f05985d7b64fc8c2606f2b119229db7f0f6175c0f938dc3913a0cc23
```

Severity: qualification blocker; no demonstrated acceptance bypass. The
checker refuses stale evidence as intended. Serializer/enum type counts and
the canonical-helper call inventory did not change.

A read-only counterfactual digest calculation isolated the cause. Exactly two
changed files belong to the retained 95-file canonical closure:

- `src/core/economic_receipt_verifier_registry_v1.py`
- `src/integration/global_economic_durable_publisher_v1.py`

Substituting these two files' exact
`c6a9fd028ded9224427a645c1217d0ce576f78af` bytes during the calculation restores
the retained expected digest exactly. No source or manifest was changed. Thus
the failure belongs to this purpose/publisher patch, rather than the earlier
allocation additions.

The reproducible read-only computation is:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tools/check_global_settlement_canonical_manifest_v1.py --json
```

No automatic regeneration command was found for this pinned constant. The
checker's CLI offers only `--repo-root` and `--json`. Its header requires a fresh
audit and explicit checker update after a digest change. Historical reviews
record explicit re-pins. The integration owner must deliberately update the
current reviewed closure through that process, then rerun the retained gate.
Historical packet identities remain historical evidence. This review preserves
`EXPECTED_SOURCE_CLOSURE_SHA256_V1` and does not authorize a blind re-pin.

## Contract assessment

The factory exposes neither caller backend nor caller measured-byte arguments.
It owns the profile snapshot and selects the exact profile-governed root
release for `ISOLATED_QUALIFICATION`. The selector requires an ACTIVE profile
and exactly one SHADOW verifier release. `PRODUCTION_NEW` still refuses because
its activation certificate is unimplemented.

Artifact acquisition opens an absolute path read-only with `O_NOFOLLOW` and
`O_NONBLOCK`, checks a regular file and 32 MiB ceiling, performs a bounded read,
requires captured length to equal the initial size, checks ELF magic, and
closes the descriptor on rejection. The **same acquired bytes** supply both the
concrete `GlobalReceiptVerifierV1` SHA-256 and the core deployment binder's
implementation-root measurement. The binder checks exact profile, registry,
release, manifest, image, protocol and size coordinates.

Subsequent verification copies the reopened source to a sealed memfd and checks
its digest before launch. Replacement with different bytes rejects before the
backend starts. Replacement after snapshotting cannot alter that call's sealed
bytes. Content identity is the contract; replacing a file with byte-identical
contents does not require an inode-identity rejection.

Both `_prepare_verified_activation_v1` purpose checks require
`ISOLATED_QUALIFICATION`. The first precedes initial-state receipt verification.
Both publisher `create` and `open` call this helper before acquiring the journal
or creating store authority. An additional independent replay confirmed that a
bound `RESEARCH_SHADOW` verifier produces the following for both entry points:

```text
economic receipt verifier selection purpose binding mismatch
backend_calls = 0
files = 0
```

The existing publisher test helper changed only its purpose value; existing
transaction/recovery tests pass. Refusing old SHADOW-purpose publisher
construction is intentional. Existing purpose strings and receipt/journal
encodings retain their representation. The new purpose receives its own
process-local binding identity, without silently reinterpreting old bindings.

## Evidence and limits

Executed replay:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/integration/test_isolated_economic_receipt_verifier_v1.py \
  tests/core/test_economic_receipt_verifier_release_v1.py \
  tests/integration/test_global_economic_durable_publisher_v1.py \
  tests/integration/test_global_receipt_verifier_v1.py \
  tests/test_check_global_settlement_canonical_manifest_v1.py
```

Result: **124 passed, 1 failed**, as recorded above. The 12 factory cases pass,
covering wrong/missing/symlink/directory/non-ELF artifacts, replacement before
launch, the size ceiling before `os.read`, SHADOW-profile refusal before
missing-file access, and absence of both caller backend and measured-byte
keyword ports. Retained production tests still refuse complete
caller-supplied active evidence labels.

Ruff passes for the factory, registry, publisher and new tests. Style routing
identifies the factory/publisher as effect adapters and the registry as
deterministic functional core. Scanning reports two pre-existing LOW broad
catches in publisher outcome/recovery handling; no new factory/purpose finding.
Scanners remain advisory.

The positive factory artifact is explicitly synthetic ELF-shaped data. It
establishes measurement/construction behavior, not successful execution,
guest validity or cryptographic receipt verification. Existing transport tests
cover framing, sealing, source replacement and typed failures. No real receipt,
fresh guest build or mounted deployment was qualified in this review.

The low-level deployment binder still accepts caller backend and measured
bytes. It remains callable alongside unmounted structural/test adapters. This
factory therefore establishes no deployment-complete mediation claim. An enum
value does not authenticate artifact review history, make an arbitrary ELF
honest, establish physical ledger isolation, authorize initial balances or
exclude other writers. Publisher process, OS, dynamic loader and shared-library
integrity remain premises. The factory's source documentation states the
artifact-provenance and isolation limits.

The factory serves one selected root image. Existing lane/coordinator/route
ports retain prior rejection rules; isolated root selection enables none of
those images. Their measured endpoints and real receipt qualification remain
separate work. Production activation and deployment-complete no-bypass claims
remain closed.

## Exact reviewed identities

```text
311b6e993cb3fc756968833770bf33f9dae9269004e4c630fce6bf01aa98fe3c  src/integration/isolated_economic_receipt_verifier_v1.py
e9889722b3887cc27ba3524cd87fcf4311e8d33d2030c4af21d561d170c06fda  src/core/economic_receipt_verifier_registry_v1.py
88796387451b475d004f6440c0c1a99ff2a73dc9ccdf381bba33d1fcc74a4d3a  src/integration/global_economic_durable_publisher_v1.py
1f9e35cfc9fa399eeff7598c1757a86dc11e5c3778da4ac84e648b2207f0051a  tests/integration/test_isolated_economic_receipt_verifier_v1.py
828e9facc673fe27625c68f642625868bc06b5e047717425e6117bdd7f8b3987  tests/integration/test_global_economic_durable_publisher_v1.py
3359741d55b056cce42b110487f4a5a534a40652976d05cab9b84f472236d997  src/core/economic_receipt_verifier_deployment_v1.py
0393f29114b9ceb0ef26ac65baa022eb4f831fb7f0971ee0ca52d83dcf5a07a9  src/integration/global_receipt_verifier_v1.py
66bbc6de53605e05a28d45602f2de896058370d6ac3df7cb04ef0a1cb97ce045  src/core/economic_receipt_verifier_evidence_v1.py
0720ab3b99bba4b10e238bf0c9720f782e4d2034e5de6b1d1d159f0ebfe4e122  tools/check_global_settlement_canonical_manifest_v1.py
f9b20f7181b9601369479e1917a982b460c4563e37b5194bbaa49da539d1cd40  tests/test_check_global_settlement_canonical_manifest_v1.py
```
