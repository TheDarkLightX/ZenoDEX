# FCIS M5-P4B5A B1B Revision 3.1 ChatGPT review adjudication

**Disposition:** `ACCEPT_BLOCKING_FINDING`

**Superseded verdict:** Gemini returned
`APPROVE_B1B1_REVISION_3_1_UNMOUNTED`.

**Controlling verdict:** ChatGPT returned:

```text
REVISE_BEFORE_B1B1
```

B1B-1 remains blocked.

## 1. Finding accepted

The ChatGPT review found that Revision 3.1 closed the transition variant set
while leaving the ordinary transition's source loose:

```text
advance_ordinary_header_v2(
  pre: FCISAuthorityHeaderV2,
)
```

Revision 3.1 did not require:

```text
pre = exact_pre_state.authority_header
```

The finding is correct. A directly constructed exact header carrying
`H_MALLORY` could satisfy every ordinary-advance equation and produce a
successor carrying `H_MALLORY`, while the bundle retained the legitimate
store-current pre-root for a state carrying `H_GOOD`.

The design therefore retained self-consistency without proving source
provenance.

## 2. Why the Gemini approval does not control

The Gemini review correctly checked that the transition variants were closed
and that ordinary advancement preserved the configuration root relative to its
input header. It did not challenge the provenance of that input header.

The ChatGPT witness is concrete, requires no hash collision, uses an allowed
`OrdinaryAdvanceV2` variant, and changes protocol authority. Under the evidence
ladder, one valid counterexample defeats an approval review.

The Gemini receipt remains historical review evidence. Its approval is
superseded for promotion purposes.

## 3. Counterexample status

| Revision 3 counterexample | Revision 3.1 adjudication |
|---|---|
| Manifest and root changed together | Closed |
| State-bound header and claim changed together | Closed |
| Ordinary successor installs a new configuration root | Still open through a loose pre-header |

## 4. Required closure

Revision 3.2 must:

1. make every non-migration header transition consume the exact V2 pre-state;
2. extract `pre_state.authority_header` internally;
3. derive configuration updates from the same exact state and a freshly
   rebound active configuration;
4. derive transition causes from the original authenticated command and exact
   context;
5. rederive the complete transition from the store's exact current state at
   publication;
6. compare every submitted successor, header, decision, patch, effect, receipt,
   replay update, and root with that rederived candidate;
7. forbid any function that advances or updates a bare header.

## 5. Evidence retained

Permanent mutants:

```text
ordinary advance accepts a directly constructed pre-header
ordinary advance reads bundle.pre_header
committed failure uses a substituted pre-header
configuration update uses a substituted pre-header
configuration update uses active content not rebound to exact_pre_state
commit-time revalidation reads bundle-carried state
current root is checked without full header-transition rederivation
transition cause changes while successor and outer hashes are retained
```

Every mutant must recompute unrelated outer hashes so only the missing
source-binding check can kill it.

## 6. Scope

This adjudication changes documentation only. It authorizes no B1B-1
implementation, migration, committed V2 state, configuration update, state
binding, receipt, bundle, proof input, publication, or mount.

The next action is focused independent review of Revision 3.2.

