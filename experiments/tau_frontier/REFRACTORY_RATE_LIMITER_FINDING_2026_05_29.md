# Refractory Rate-Limiter Candidate

`refractory_rate_limiter_gate_candidate_v1.tau` is a dual-profile Tau candidate
for bounding repeated runtime requests without Python-side mutable counters.

The first attempted shape used output feedback:

```tau
o1[t]:sbf = i1[t]:sbf & (o1[t-1]:sbf)'
```

Both supported Tau builds accepted the expression, but emitted a short
fixed-point trace rather than one output per input step under the repository
runner. That shape is not promotable as a runtime gate.

The candidate keeps the useful cooldown property with bounded input history:

```tau
o1[t]:sbf = i1[t]:sbf & (i1[t-1]:sbf)'
```

This accepts rising-edge requests only. A sustained high request stream is
rejected until the input goes quiet and then rises again. In both supported Tau
builds, the initial `t < 0` history behaves fail-closed for a high first input,
so a caller that wants the first real request admitted must provide one observed
quiet step first.

Promotion status: candidate only. The recommended Tau proof-plan registry is
already stale on `main`, so promotion should wait until the registry can assign
the spec a profile and rule without increasing semantic-view drift.
