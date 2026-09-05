# Whole-program V3: retained ESSO replay

The three unchanged ESSO gates passed 180 tests on the pinned source below.
The final preservation run retained all 52 subprocess reports and 52 exact
YAML inputs: eight successful validation calls, 16 successful two-solver
verification calls, and 28 expected verification failures. The failures cover
14 semantic mutant families and their invariant-attribution variants. This
replays existing model obligations; it grants no publication authority.

| Model | Tests | Baseline solver queries | Declared integer domains |
| --- | ---: | ---: | --- |
| [Allocation certificate](../../src/kernels/dex/global_accounting_allocation_certificate_v1.yaml) | 24 | 8 passed | State 0–8; amounts 1–2; two lanes and two claimants |
| [Claimant/custody certificate](../../src/kernels/dex/global_claimant_custody_certificate_v1.yaml) | 20 | 4 passed | State 0–8; amounts 1–2; two domains and two claimants |
| [Global settlement core](../../src/kernels/dex/global_settlement_core_v1.yaml) | 136 | 2 passed | State intervals 0–3, 0–4, 0–20, 0–15,624; parameter intervals recorded in the model |

The baseline reports identify `Inductive(k=1)`, unbounded sequential time,
and the declared finite state domains. They report agreement between Z3 and
cvc5, zero failed or inconclusive baseline queries, and two deterministic
trials. The certificate models use a 10,000 ms solver timeout; the global-core
baseline uses 5,000 ms. These model bounds remain abstract parameters. They
do not select production policy values or establish implementation refinement.

## Exact subject and tools

```text
source commit:
7b2467067c8c978e9eca19ddd33a24ce0740560d
ESSO source commit / reported code hash:
7f80c6216be85c827e8d1cc2fa08ee3107a74588
complete 379-file source manifest SHA256:
e16128d88b53ff145ca7c46114fa77ab7d5f1d880117ba73ef26eb3ad42d630f
allocation model source SHA256:
7afad7b256a19b1a162dd24dad5ca89f3ebe47c8c02f63bb60d1cfff7b709456
claimant/custody model source SHA256:
d7b547e32790828c149fb0e3bdd6b32e11a235bbb67b6cf02eaaff4db2681252
global-core model source SHA256:
121972779c7ac2f06dee1a6970498ab6b8e17c80c3050342648d8d2d432a2b7d
```

The execution used Python 3.11.10, pytest 9.0.3, PyYAML 6.0.3,
`z3-solver==4.15.4.0` (solver reports 4.15.4), cvc5 1.1.2, Cargo 1.90.0,
and rustfmt 1.8.0-stable. The archive retains the hashed Python dependency
lock, actual Cargo/rustfmt executable measurements, and the cvc5 executable,
loader, libraries, launcher, and runtime manifest. The cvc5 runtime manifest
hash is `786e3b0d3f25e28c4234ca6c82a2813caa329ef5595a1eff49b86c7de5d2eb08`;
its retained installation archive hash is
`ea57e854ce869d4dcfe4e46f6f104d02762e1375ab32ad6f97f3dcf9643c9179`.
Those measurements identify the selected runtime; they do not imply a
publisher-signed solver distribution or a verified operating system.

## Replay and negative evidence

In the pinned environment, the unchanged test command was:

```bash
python -m pytest -q -p no:cacheprovider \
  tests/formal/test_esso_global_accounting_allocation_certificate_v1.py \
  tests/formal/test_esso_global_claimant_custody_certificate_v1.py \
  tests/formal/test_esso_global_settlement_core_v1.py
```

The final run passed in 90.46 seconds with two CPUs. A job-only capture wrapper
retained each subprocess's exact arguments, return code, complete captured
stdout/stderr, and referenced YAML bytes before temporary-directory cleanup.
It preserved the subprocess return behavior and rechecked all 379 source files
after the run. No model or retained test was edited, skipped, or weakened.

The 14 negative families cover reserve masking, unassigned atoms, enabling
without receipts, terminals exceeding entitlements, custody double counting,
disabling with live rows, missing external-table aggregation, missing lane
binding, missing global-root binding, custody-domain substitution, claimant
column substitution, terminal-domain erasure, cross-domain drain substitution,
and reserve masking of an open claim. Each retained attribution variant names
the affected invariant. The original mutant and attribution YAML bytes and
full solver reports are available for independent replay.

Earlier failures remain archived: the original cvc5 version-string mismatch,
missing ESSO resources, and unavailable Rust tool discovery were resolved
before the passing gates. The initial passing pytest summaries omitted child
solver output; the final capture closes that evidence gap without changing
the tested subjects.

## Preserved evidence and claim ceiling

```text
evidence archive: zenodex-v3-esso-evidence05.tar.gz
archive bytes: 60235832
archive SHA256:
4c701e4d59e4a824dcae1186db111947572a823103829bb3783a9d1d086ec91a
637-file evidence manifest SHA256:
8a1997a3df65d4e7606b71055fbe28f1c9f8878a611967a93574c7c63bbc6220
final capture receipt SHA256:
d822503a91a9114c1ce3bc0b985b157d25a3fc835e7a544a6454ce0cc8f21f54
capture helper SHA256:
d01fe140fee631d0e7d6a13df5755ca011784567d89db71f289eb46db6a45ed9
```

The archive includes the exact sources, job helpers, source/resource archives,
solver runtime, prior failures, successful logs, and full final captures.
Virtual environments and build caches are excluded. After explicit scoped
download authorization, independent local checks verified the archive hash,
all 637 artifact hashes and lengths, all 379 source bindings, all 52 captured
reports, and all 52 YAML copies. Integration owns the durable workspace copy.

These results establish the reported inductive properties for the selected
ESSO models and finite domains under the pinned tools' semantics. They do not
prove that every runtime state projects safely into those models, actual
authorization or datastore refinement, concurrent publication or recovery,
all twelve lane lifecycles, or production value safety. Authority remains
`NONE`; whole-program completion and promotion remain blocked on their
separate obligations.
