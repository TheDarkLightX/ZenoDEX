<!-- Keep answers short. Link existing evidence; do not duplicate packets. -->

## Required behavior and scope

What requirement or reproduced defect does this change address? Identify the
baseline commit and intended observable behavior, including rejection and effects.

## Smallest sufficient change

What simpler alternative was considered (including reuse or deletion), and why
was this implementation selected? Identify added or removed concepts, state and
dependencies. Explain any retained complexity that protects an obligation.

## Assurance and review

- Identify source, tests, specifications or independent oracles changed together.
  Explain why test changes preserve the contract, or identify the separately
  authorized behavior change. Retain the relevant negative cases.
- Link exact commands/results and existing evidence packets. Distinguish tests
  that passed, skipped, failed or were not run. Mutation checks compare the
  candidate with its mutants; preservation needs baseline-to-candidate evidence.
- For critical changes, link an independent review of the final source commit.
  Identify unresolved findings and re-review material edits after that review.

Stop when the scoped requirement and applicable checks pass. Reopen it for an
unmet requirement, new counterexample or demonstrated improvement. Checkboxes
and model reviews do not replace required CI checks or repository-owner approval.
