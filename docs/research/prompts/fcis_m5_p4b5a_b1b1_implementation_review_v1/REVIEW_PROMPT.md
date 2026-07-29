# B1B-1 repaired exact-head independent review

Review target:

```text
implementation commit: 13f06a4675e4a01cf8d57b6cf2feb1ca3ddad8ef
approved design packet: 1665e788a4c4daf43982262c307d0c04b914d89b
required verdict: APPROVE_B1B1_EXACT_HEAD_UNMOUNTED
               or REVISE_B1B1_EXACT_HEAD
               or REJECT_B1B1_SCOPE_VIOLATION
```

Verify the bundle, external delivery receipt, packet parent relation, base and
target trees, deletion-aware change inventory, metadata, and every source
manifest hash before reviewing claims.

Falsify at least:

1. recursion, depth, node, collection, byte, and UTF-8 escape from admission;
2. Python/Rust resource-bound rejection disagreement;
3. extra or omitted Python/Rust carrier fields and non-injective encoding;
4. aliased, qualified, or novel-path carrier consumers;
5. Rust `lib.rs` authority helpers and hidden public surfaces;
6. premature verifier, migration, state, transition, receipt, bundle, proof,
   publication, or mount symbols;
7. deleted guard or test paths omitted from packet evidence;
8. incomplete Cargo workspace closure;
9. stale, incomplete, or self-inconsistent packet evidence.

Do not repair the target during review. Report exact commands, minimized
witnesses, unrun gates, residual risk, and one permitted verdict.
