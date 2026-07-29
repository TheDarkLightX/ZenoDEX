# FCIS M5-P4B5A ATDD subagent packet

This packet turns the approved Revision 3.4 B1B-1 boundary into executable
acceptance work.

Start with:

```bash
python3 -B tools/check_fcis_m5_p4b5a_atdd_contract.py --assigned-id ATDD-B1B1-009
```

Use one prompt:

```text
B1B1_IMPLEMENTATION_PROMPT.md  implement one acceptance slice
B1B1_REVIEW_PROMPT.md          falsify an exact implementation head
B1B2_DESIGN_PROMPT.md          design the next checkpoint without implementing it
```

`ACCEPTANCE_MATRIX.json` is the machine-readable scope and traceability source.
The approved Revision 3.4 document remains normative. This packet adds no
protocol authority.

Read `case_lifecycle` before running a case. The old 45-file Revision 3.4 source
manifest is a base-only precondition. Planned evidence paths are target
interfaces until their owning implementation slice creates them. B1B-2 remains
design-only until a later committed contract revision records all required
approval identities and explicit user implementation authority.
