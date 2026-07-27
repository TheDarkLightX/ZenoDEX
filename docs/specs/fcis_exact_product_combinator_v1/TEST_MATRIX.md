# FCIS Exact Product Combinator V1 Test Matrix

The executable authority is `tests/state/test_snapshot_combinators.py`.
This file maps contract obligations to exact test names; it is not an
independent proof or claim checker.

| Requirement | Executable binding |
| --- | --- |
| `XPRODUCT-001` canonical heterogeneous list admission | `test_exact_product_admits_canonical_heterogeneous_list_in_order` |
| `XPRODUCT-002` exact source kind and hostile-subclass rejection | `test_exact_product_rejects_wrong_arity_and_subclass_without_hooks` |
| `XPRODUCT-003` exact arity rejection | `test_exact_product_rejects_wrong_arity_and_subclass_without_hooks` |
| `XPRODUCT-004` stable first indexed rejection | `test_exact_product_reports_the_first_indexed_rejection` |
| `XPRODUCT-005` collection and node budgets | `test_exact_product_enforces_collection_and_node_budgets` |
| `XPRODUCT-006` nested ownership and cycle rejection | `test_exact_product_owns_nested_values_and_rejects_cycles` |
| `XPRODUCT-007` closed, exact, acyclic schema configuration | `test_exact_product_schema_is_closed_and_acyclic` |
| `XPRODUCT-008` no implicit map-key authority | `test_exact_product_is_not_a_map_key_schema_in_v1` |
| `XPRODUCT-009` closed-union, validator, and dispatcher wiring | `test_exact_product_is_bound_to_closed_validation_and_dispatch` |
| `XPRODUCT-010` existing combinator compatibility | full `tests/state/test_snapshot_combinators.py` suite |
| `XPRODUCT-011` mounted-state compatibility | full `tests/state` suite plus structural authority profiles |

Mutation review must demonstrate that removing the `SchemaV1` variant,
registry validation branch, runtime dispatch branch, exact source-kind check,
arity check, item-budget check, cycle check, or indexed child path causes at
least one executable binding to fail.
