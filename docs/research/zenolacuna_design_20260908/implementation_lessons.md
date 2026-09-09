# ZenoLacuna implementation lessons

The earlier finite prototype is recorded in
[implementation_coverage.md](implementation_coverage.md). The signed project
workflow follows the [release contract](release_contract.md). See the
[usage guide](../../../src/zenolacuna/README.md) for executable commands. The
original design and its reviews remain frozen records of the design stage.

## Findings worth reusing

1. **Composition exposes requirements that component tests omit.** Seven
   deliberately paired XOR codec changes preserve every valid self round trip
   and every reserved-byte sentinel, while both mixed-version paths misdecode
   every valid word. Keep independent old/new compositions in migration
   contracts. This demonstrates a missing compatibility decision in a weakened
   contract; the published codec itself was not found defective.

2. **A value and its meaning need separate runtime evidence.** Independent
   review relabeled the final outcome of an identity integer program as a
   rejection. The first program port incorrectly accepted that label because
   it checked only returned integers. The repaired port accepts only integer
   return observations; interpreting a sentinel as an application rejection
   requires a separate checked adapter. A regression preserves this failure
   family. This was a concrete correctness improvement found during review.

3. **A question must respect the equivalence relation used by the checker.**
   Two source representations with identical complete observations cannot be
   split by a quotient-level question. Ordinary nondeterministic outcomes of
   one interpretation also cannot be presented as conflicting requirements.
   Both cases now have negative evidence, together with overlapping allowed
   sets whose real difference must still yield a witness.

4. **A promising first question can still have an impossible branch.** The
   minimax implementation propagates an unseparable child to infinity. The
   independent oracle enumerates complete decision trees using a different
   representation and no production DP calls. Six targeted process-local
   semantic mutations were killed, including dropped infinity, incomplete
   filtering, weakened witness premises and vacuous positive behavior.

5. **Persisted decisions and runtime checks need an explicit connection.**
   A command that reloads the original task loses the answers in a separate
   run. Program replay must obtain its surviving interpretations and assessed
   candidate from the exact checked revision. A source hash or caller-written
   success report cannot replace that connection. Runtime evidence still needs
   to be distinguished from the local decision journal's model evidence.

6. **Native tools must earn their cost on the particular problem.** The demo
   measures ordinary finite set comparison alongside Tau on the same relation
   pairs, including native process overhead. Its one-question compatibility
   case can also be solved with one suitable fixed question. No productivity,
   question-count, or speed advantage over that baseline is claimed. Tau's
   additional demonstrated role is symbolic projection of a queue precondition,
   cross-checked with a finite graph and independently generated ESSO model.

7. **Pure functions benefit from small, explicit values.** Frozen dataclasses
   work for named boundaries; tuple relations work for compact mathematics.
   A large persistence module was split into workflow, journal encoding and
   filesystem helpers. The workflow module remains the main size hotspot:
   history reconstruction and atomic publication are still kept together under
   one lock/source binding. Further extraction needs to preserve that binding,
   rather than introduce a generic mutable repository abstraction.

8. **Useful local evidence has a conditional ceiling.** The Lean proof says
   which supplied question languages can identify each supplied class under
   faithful answers. It does not establish that real human intent is in that
   set. Solver agreement does not establish a faithful runtime abstraction.
   Simulated decision receipts do not establish real owner consent. These
   premises must remain visible to the developer and their swarm.

9. **Source identity must precede Python execution.** Review reproduced a
   cached-function/source-hash mismatch. A second pass found timestamp-valid
   bytecode and eager package initializers. The project CLI now starts with an
   empty bytecode-cache prefix and seals the transitive local import closure
   before importing application packages. Native ESSO receives the same cache
   treatment. A direct library call retains a whole-process immutable-host
   premise. Hashing a file after importing it cannot repair that premise.

10. **An approval request and its result are different objects.** A signed
    COMPLETE command authorizes verification. It does not sign the solver's
    later success. Project reconstruction must regenerate the result and
    compare exact evidence; a fabricated saved completion flag now fails its
    own signed-history regression. Old bundles remain historical, with an
    externally expected head required when freshness matters.

11. **Crash tests need real payloads at every storage layer.** Answer-only
    interruption tests missed the distinct cases of new source blobs and
    completed runtime evidence. The signed project tests now abort source
    revisions and terminate completion processes before and after commit.
    SQLite supplies transactional recovery under its filesystem premises;
    tests do not prove storage hardware honors fsync.

12. **Delivery order can change errors even when state remains safe.** A stale
    answer originally became a conflicting duplicate after a valid answer
    arrived. Binding duplicate detection to the original answer's parent fixed
    the ambiguity. All six orders of valid, retry and already-stale work now
    preserve the same archive and declared rejection behavior.

## Next candidate: synthesize the missing observation

The next research opportunity is to make the observation boundary itself a
searchable, checked object. Current finite scopes assume the developer supplied
the relevant state and observations. A swarm should be able to propose a small
projection of a real adapter's state and have a deterministic checker either
certify its adequacy for named obligations or produce a missing-state witness.

For a finite concrete state set X, a selected field set F defines `O_F(x)`.
Let `K(x)` be the vector of protected applicability, acceptance, rejection and
effect verdicts. The first exact target is:

```text
For every x,y in X: O_F(x) = O_F(y) implies K(x) = K(y).
```

A violating pair is a concrete counterexample to the proposed abstraction.
Each pair yields the set of fields that distinguish it. Choosing a sufficient
field set becomes a finite hitting-set problem, with positive integer field
costs, an independently replayable coverage certificate and a separately
checked lower bound when claiming minimality. A field set that separates
single states may still lose history correlation, so trace/state-machine
obligations require their own fixed concrete domain.

User story: a developer's swarm proposes a smaller migration model. The checker
finds two queued states with identical proposed observations but different
decoding safety. The swarm proposes retaining message version or replacing it
with a smaller derived equality predicate. The checker verifies the predicate
against the actual finite codec and every declared queue transition before
using the smaller model for synthesis.

Start with the known V1/V2 signal fixtures and the paired-codec queue example.
Compare against keeping every field and ordinary greedy feature selection on
the same held-out omission families. Promotion requires a replayed omission
that the prior projection missed, or a certified smaller sufficient model with
measured verification savings. Include deliberately unobserved authentication,
freshness, queued-version and terminal-effect distinctions as negative controls.

This is a proposed application of established abstraction-refinement and
finite optimization ideas. No foundational novelty, general completeness,
runtime speedup, or patent clearance has been established. A prior-art review
and a source-bound finite implementation are required before promoting it.
