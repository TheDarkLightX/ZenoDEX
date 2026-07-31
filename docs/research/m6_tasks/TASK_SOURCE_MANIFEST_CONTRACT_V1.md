# M6 Task Source Manifest Contract V1

Each task packet has one `TASK_<id>_SOURCE_MANIFEST.sha256` file. It is a
standard `sha256sum` ledger with one line per declared artifact:

```text
<64 lowercase hexadecimal SHA-256>  <repository-relative POSIX path>
```

The contract is:

1. Every declared path is relative, normalized, unique, and present at
   verification time.
2. Paths may not contain `..`, backslashes, or a leading slash.
3. The manifest does not hash itself. This avoids a self-referential digest;
   the manifest file is verified through its committed Git blob identity.
4. The ledger is checked with
   `sha256sum --check --strict TASK_<id>_SOURCE_MANIFEST.sha256`.
5. Regeneration uses sorted, deterministic input paths and must reproduce the
   same bytes while the source files are unchanged.
6. A missing, surplus, duplicate, malformed, or mismatched entry rejects the
   packet before its evidence is considered.

The task evidence JSON records the source hashes used to construct the packet.
The manifest records the packet artifacts and schemas needed to validate the
receipt itself.
