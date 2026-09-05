# Fill-index optimization: held after parity review

Candidate P4 from the critical-algorithm review was evaluated against integration
HEAD `04f0d32b6b6679aa23da645263ec6575f7872c4e`. Its production change was
withdrawn. `src/core/batch_clearing_compute.py` remains byte-identical to that
subject. The new `tests/core/test_batch_fill_intent_lookup_v1.py` retains the
behavioral contract and the discovered counterexamples.

The proposed first-match index could become stale inside a single phase: an
initial accepted fill populated it; a later exact `Fill` carried an action
equality hook that replaced a subsequent intent; the final fill then selected
the original intent while the existing lookup selected its replacement. Exact
`Fill` type did not ensure primitive fields. A guard comparing the application
callback against a dynamically imported module binding also failed to establish
an immutable callback contract.

The minimized cases failed the proposed optimization. After restoring the
original lookup, **13 tests passed**, including the two failures, duplicate
first-match behavior, missing IDs and prior buffers, rejected-only laziness,
subclass values, and clear/application callback mutation. Parent replayed the
tests, Ruff and mypy. This is factory-behavior parity evidence, not a demonstrated
public authority bypass.

```bash
python3 -m pytest -q tests/core/test_batch_fill_intent_lookup_v1.py
python3 -m ruff check tests/core/test_batch_fill_intent_lookup_v1.py
python3 -m mypy tests/core/test_batch_fill_intent_lookup_v1.py
```

Test SHA-256:
`73b044e40958ceb94cdbb17a14b59821c6153862c24771649f1ae26e751f2bc2`.
The implementation and independent reviewer identified the same cache-lifetime
problem. Earlier timing used a synthetic clearer returning prebuilt fills; those
measurements are withdrawn as acceptance evidence and its new benchmark tool
was removed. No throughput improvement is claimed.

A future index needs a stable, owned input/callback contract and measurement on
the actual standard clearing path. A caller-constructible flag or a new private
token alone cannot establish that contract. This optimization is deferred until
that wider change is justified; V3 safety work continues independently.
