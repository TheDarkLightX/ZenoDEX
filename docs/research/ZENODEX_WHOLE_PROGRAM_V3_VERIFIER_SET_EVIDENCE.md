# Isolated measured receipt-verifier set

Date: 2026-09-05. Research implementation; authority `NONE`.

The isolated factory now measures the root endpoint and every profile-selected
`ACTIVE_NEW` module, coordinator and route endpoint that accepts new objects.
The implementation commitment contains each exact image and ELF byte sequence
in sorted image order. Acquisition paths do not enter that commitment.
Calls select the expected image, remeasure its executable, seal the measured
bytes and execute the sealed descriptor through the existing bridge.

This solves a concrete integration problem: the root-only factory cannot
verify leaf receipts under their different fixed images. The existing bound
verifier now admits isolated leaf verification only for an `ACTIVE` profile,
an `ACTIVE_NEW` selected release and `accepts_new_objects=true`. Its historical
SHADOW conditions and production rejection branches retain their behavior.
No wire journal, profile schema, canonical serializer or image ID was changed
by this Python patch. The new complete artifact preimage requires its own
implementation commitment and corresponding selected release.

## Boundary and review

The factory accepts acquisition coordinates and a selected evidence manifest.
It has no caller-backend or measured-byte argument. It snapshots the profile
and coordinates, requires exact selected-image coverage before IO, measures
the actual ELF bytes and derives each endpoint hash from those same bytes.
Manifest preparation is separate from binding; binding always reacquires.

The private artifact frame is `ZDXVSET1`, a little-endian u16 count, followed
by sorted image32, little-endian u32 ELF length and exact ELF bytes per row.
The complete frame, including all row overhead, is limited to 32 MiB. Existing
endpoint receipt/journal/time limits remain in force.

Opus independently reviewed three frozen files at base `7b2467067`. It found
the measurement/execution relation, exact image identity, snapshot ownership,
resource limits and sealed execution consistent with the stated contract.
The reviewer did not execute the tests or review the historical purpose
branches. The integration owner separately read those branches, confirmed by
AST comparison that only the three profile-specific verifier methods changed,
and ran the retained release and factory tests.

Two review limitations remain explicit:

- The public low-level core binder still accepts an arbitrary backend. This
  narrow factory establishes measurement/execution binding on its own path.
  Mandatory publisher use of that path and deployment-complete mediation
  remain open. A same-process construction token alone would not secure a
  compromised Python process or operating system.
- `DRAIN_ONLY` and `VERIFY_ONLY` images are outside this initial new-object
  qualification set. They require separately qualified historical and draining
  lifecycles. Their exclusion is fail-closed and does not complete those
  required workflows. Existing profile decoding remains available.

The final factory docstrings clarify these limits. That is the only change
after the frozen Opus code review; test and core-deployment bytes are unchanged.
The advisory report remains preserved separately as `OPUS_VERIFIER_SET_REVIEW.md`.

## Evidence and exact subjects

The focused suite passed **52 tests**; adding the canonical checker suite after
the explicit pin refresh gave **60 passed**. The first combined invocation used
an incorrect checker-test path and collected no tests; the corrected command
below supplied the result. The verifier tests use synthetic ELF bytes and recording
verification calls; they do not claim genuine whole-set receipt qualification.
Controls cover exact independent framing, missing/duplicate/reversed/foreign
images before IO, nonroot executable substitution, all four receipt roles,
foreign image refusal, SHADOW coordinator refusal, path relocation, exact
32 MiB framing and one-byte overflow, caller-coordinate mutation during IO,
and executable replacement before launch.

| Source | SHA-256 |
| --- | --- |
| `src/integration/isolated_economic_verifier_set_v1.py` | `5bf788f676c771a6ee0dd80ab30a53a289037314d2419d0984d2c573e081becd` |
| `src/core/economic_receipt_verifier_deployment_v1.py` | `eb36d6a631e875777c565c77ff3f9c9955e1e89e599a7c2cd820dae6fd990fff` |
| `tests/integration/test_isolated_economic_verifier_set_v1.py` | `50e86035d230fc8e2c27df48b925b39fd0f80d10ade01850a3a49a13958763de` |

Commands:

```bash
python3 -m pytest -q -p no:cacheprovider \
  tests/integration/test_isolated_economic_verifier_set_v1.py \
  tests/core/test_economic_receipt_verifier_release_v1.py \
  tests/integration/test_isolated_economic_receipt_verifier_v1.py \
  tests/test_check_global_settlement_canonical_manifest_v1.py
python3 -m ruff check src/integration/isolated_economic_verifier_set_v1.py \
  src/core/economic_receipt_verifier_deployment_v1.py \
  tests/integration/test_isolated_economic_verifier_set_v1.py
python3 -m mypy src/integration/isolated_economic_verifier_set_v1.py \
  src/core/economic_receipt_verifier_deployment_v1.py
python3 tools/check_global_settlement_canonical_manifest_v1.py --json
```

The canonical checker has no generation command. Its documented process
requires a fresh audit and explicit constant update. Before that update it
correctly rejected source-closure drift from `9643388a...` to
`de0b457db34904297b3cb9b7cf169e8b88dcdcb93394e6b45de943dfcc995b9a`.
The audit found the three isolated-purpose branches above, with the same
104 serializers, 35 enums, 93 canonical-caller files and 95 closure members.
The source digest is explicitly refreshed for those reviewed bytes; this is
static closure evidence, not semantic refinement or deployment admission.

Ruff and mypy passed; the security red-flag scan covered the three actual source
and test files and reported no findings. Metrics flag the inherited large core
deployment module and its explicit per-role parameter lists. Those checks remain
separate so this behavior change can be audited against the previous branches;
no unrelated authority refactor was mixed into it. The new factory's keyword
arguments name distinct profile, registry, manifest, artifact, deployment and
timeout inputs. Scanner silence and style signals supply no safety proof.

Genuine root and transfer receipts are retained in separate exact-build
evidence. The composed module/coordinator/route/root build is still undergoing
source-path normalization and qualification. No whole-set real receipt chain,
signature authentication, allocation publication mediation, production
activation or whole-program safety is established by this patch.
