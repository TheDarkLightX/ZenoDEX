# Economic command intent authentication V2

Scope: an isolated signed-intent and occurrence check. Authority remains `NONE`.
This extends the existing two-stage signing semantics to V2 command hashes;
historical messages, registries and verification remain unchanged.

## Signed intent and encoding

The user signs before sequencing. The exact intent fields are:

```text
chain_id, deployment_root, profile_root,
command_kind, command_body_hash, route_release_id,
subject_id, grant_root, nonce, consumed_object_ids,
valid_from_height, valid_through_height
```

The intent uses schema `zenodex/economic-command-authentication/v2`, exact V2
ASCII tokens and nonzero roots, unsigned 64-bit nonce/heights, an ordered
height interval, and at most 64 sorted unique consumed-object identifiers.
Command bytes retain their 1 MiB envelope ceiling. `command_body_hash` uses
the existing `authenticated-economic-command-body-v2` domain, including the
actual command's origin field. An old body hash cannot stand in for it.
This authentication layer hashes bounded opaque bytes; it does not decode a
canonical V2 command or establish origin presence. The consuming V2 transition
must recompute the hash of its actual typed command, match the occurrence, and
enforce that command's schema and origin requirements.

The signing message is the existing domain-separator encoding for
`economic-command-intent-authentication-message-v2`, version 2, followed by
canonical V2 JSON with exactly these body keys:

```text
schema, policy_registry_root, authorization_registry_root, authorization_id,
verifier_registry_root, signature_verifier_registry_root,
signature_verifier_release_id, intent, command_body_bytes_digest,
signature_algorithm, signer_key_id, signer_public_key
```

`command_body_bytes_digest` retains its existing raw SHA-256 meaning. It is
distinct from the domain-separated intent body hash. BLS receives the complete
prefixed message bytes without an additional message prehash. The signature
itself is outside the message, preventing a self-referential signing payload.

The message-schema root is `hash_global_v2` in domain
`economic-command-intent-authentication-schema-v2` over the exact descriptor:
`schema`, `message_domain`, `intent_fields`, `message_fields`. The first two
values are the schema and message-domain strings above. The last two are the
field-name tuples in the displayed order. This root identifies the explicit V2
signing contract and must match the selected signature-verifier release.

## Governed preparation and format reuse

Preparation snapshots the exact candidate before checking it. It explicitly
reuses the unchanged `EconomicProfileSnapshotV1`, policy, authorization and
signature-verifier registry formats and their existing content-derived roots.
The message contains those roots. It does not encode a V1 profile as a V2
profile or cast a V2 occurrence into a V1 occurrence.

The profile must be `ACTIVE`; its policy root must select the supplied policy
registry. The command-authentication policy selects the authorization registry,
and the governed route must match the intent. The authorization row matches
command, subject, grant, route and signer-key ID. It must be enabled, match the
public key and algorithm, contain the nonce, and contain the entire signed
height interval. The supplied command bytes must hash to the V2 intent hash.

Signature-release selection uses the existing `ISOLATED_QUALIFICATION` rules:
one eligible `SHADOW` release, no new-production authentication, and the
existing baseline evidence requirements. Its message-schema root must equal
the V2 root above. Reusing a registry format does not permit reusing an old
signing-schema selection. New selected contents produce new registry/profile
identities through the existing hash rules.

Preparation returns owned data and signing bytes; it grants no authority.
The pure occurrence check requires equality of the ten signed fields also
present in the occurrence and a sequenced height inside the signed interval.
Transaction index, operation index and predecessor root remain sequencer
inputs. No second user signature is required for those fields.

## Verification and remaining admission

The shell takes the candidate and occurrence plus configured artifact path,
evidence manifest and timeout. It snapshots and checks the candidate and
occurrence before artifact access. It constructs the sealed BLS verifier
internally through the existing no-backend-injection factory, using the core's
selected release and owned deployment/profile roots. The acquired artifact
bytes are also the executed bytes. The verifier must match that scope and
return exact cryptographic success for the owned key, signature and message.
No caller-provided verifier handle, backend, release, prepared message or
success flag is accepted.

Failures propagate and successful checking returns `None`. Every call checks
again; no reusable authority witness, replay consumption, history or outbox is
created. A later protected operation must check its own exact inputs, or
combine verification and use of the owned snapshot. It cannot treat this
result as permission to use subsequently mutated originals.

The profile's own status is not part of its content-derived ID. Root equality
therefore does not authenticate activation. Trusted profile/status selection,
release evidence and executable honesty remain premises. The Python process,
OS, dynamic loader and native dependencies also remain trusted.

This check does not admit a complete V2 settlement profile. Matching custody
state/statement schemas, module releases and actual guest image, one-ABI route
composition, store-current authority, durable publication, destination effects
and no-bypass remain separate requirements. Genuine BLS checks do not qualify
RISC0 receipts, Tau finality, release activation or full formal-core completion.

## Replay and evidence scope

Run the pure contract, historical compatibility and isolated adapter cases:

```bash
python3 -m pytest -q tests/core/test_economic_command_authentication_v1.py tests/core/test_economic_command_authentication_v2.py tests/integration/test_isolated_economic_command_authentication_v2.py
```

The adapter cases normally use a protocol fixture that independently verifies
BLS signatures with `py_ecc`. They check exact sealed-file acquisition and
protocol inputs, but intercept process execution. One additional test executes
the real sealed Rust verifier when `ZENODEX_BLS_VERIFIER_TEST_BINARY` selects
the measured artifact. Without that variable, that test explicitly skips.

The retained native subject is the unchanged
`zk/economic_command_bls_verifier_v1`, rebuilt with Rust 1.87.0 from the locked,
checksum-verified offline dependency sources. Its 508672-byte release ELF has
SHA-256 `597f1e56fcca8f00bc94805cf020ca0e6f2779ded3b1944d1d699231f55b0eee`.
The test checks that digest before constructing the isolated release. It
accepted a V2 message signed with the public test key and rejected a foreign
key's signature through actual sealed execution. Its dynamically linked loader
and libraries remain part of the trusted execution environment.

```bash
ZENODEX_BLS_VERIFIER_TEST_BINARY=/path/to/measured/verifier python3 -m pytest -q tests/integration/test_isolated_economic_command_authentication_v2.py::test_native_sealed_verifier_accepts_v2_and_rejects_a_foreign_signature
```

The test-hygiene packet `THV1-20260909-command-authentication-v2` pins the
source, independent protocol oracle and declared guard-removal mutants.
The existing mutation ledger requires a passing control before accepting a
killed mutant. CI declares the Python regressions; that declaration does not
claim hosted execution or availability of this separately measured ELF.
