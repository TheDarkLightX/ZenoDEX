# Intent Signatures (BLS12-381)

ZenoDEX supports optional **per-intent signatures** so third parties can batch-settle user intents without requiring the outer transaction sender to equal each intent sender.

## Scheme

- Curve: **BLS12-381**
- Public key: **G1**, 48-byte compressed, `0x`-prefixed hex
- Signature: **G2**, 96-byte compressed, `0x`-prefixed hex
- Library reference: `py_ecc.bls.G2Basic` (matches Tau Testnet conventions)

## Signing Payload

1. Construct the **intent signing dict**:

```json
{
  "module": "TauSwap",
  "version": "0.1",
  "kind": "<IntentKind>",
  "intent_id": "<0x…>",
  "sender_pubkey": "<0x…48 bytes…>",
  "deadline": 123,
  "fields": { "...": "..." },
  "salt": "..." // optional
}
```

Note: intent-specific fields are nested under `"fields"` (they are not flattened at the top level).

2. Encode as **canonical JSON** bytes via `src/state/canonical.py:canonical_json_bytes(...)`.

3. Compute the message digest:

```
msg_hash = SHA256( domain_sep("dex_intent_sig:<chain_id>", v1) || canonical_json_bytes(intent_signing_dict) )
```

Where:
- `domain_sep(...)` is `src/state/canonical.py:domain_sep_bytes(...)`
- `<chain_id>` is an ASCII deployment identifier (e.g. `tau-net-alpha`)

4. Sign:

```
signature = BLS.Sign(sk, msg_hash)
```

Verification uses the same `msg_hash`.

## Test Vectors

See `tests/integration/test_intent_signatures.py` for deterministic keygen + sign/verify coverage.
