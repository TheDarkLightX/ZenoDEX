# Mechanism Design Math Design Recommendations

No production code recommendations are emitted by the current Wave 1 arithmetic
evidence.

Settled so far:

| Obligation | Result | Recommendation |
|---|---|---|
| `O-SS-02` | ceil-rounded fees are superadditive under the bounded Wave 1 split model | no change; splitting does not reduce exact-in fee liability in this model |
| `O-SS-07` | fee dust-carry conserves value with `dust < 3` for the three-way split | no change; keep the dust-carry invariant covered by regression evidence |

Future entries should name the falsified claim, the replay command, and the
specific production surface that would need a separately reviewed change.
