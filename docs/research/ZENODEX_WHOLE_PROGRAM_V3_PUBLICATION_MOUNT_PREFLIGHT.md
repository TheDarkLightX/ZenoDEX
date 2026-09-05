# Isolated publication admission preflight

Date: 2026-09-05. Integration base: `0bb6ac79c3d505c0a01eb0cfd4dfb281c9499ae6`.
Status: bounded measured-port mount implemented and reviewed; raw admission
and allocation mounting remain in progress. Authority: `NONE`.

The isolated publisher must acquire its receipt verifier through the measured
profile-port factory. A caller can currently obtain the exact low-level bound
verifier type by supplying a backend to the public core binder. Requiring that
type alone does not establish that the measured subprocess performs checking.

## Contract and ownership

The invariant is that every public publisher create/open path requires a
factory-minted measured profile-port handle before acquiring writer authority
or creating a journal. The factory fixes the selected profile, deployment,
registry, images and isolated selection purpose. The publisher retains its
existing private bound verifier, genesis verification, current-head CAS,
complete-bundle commit and recovery outcome contracts.

The shell owns acquisition and opaque receipt-port provenance. Core verification
continues to consume explicit values. Neither an immutable candidate nor a
core witness minted through a caller backend establishes shell provenance.
Consequently, a later mandatory command-admission step must reauthenticate raw
signed intent and verify module/coordinator/route receipts through the owned
ports before invoking the derived allocation consumer. This first mount repair
alone does not complete that step or whole publication mediation.

Owned production edit: `src/integration/global_economic_durable_publisher_v1.py`.
The bounded parallel tasks own new profile ports, the concrete BLS backend, and
the pure allocation consumer in separate modules. Existing publisher tests will
use actual measured factory construction over explicitly synthetic ELF files;
only subprocess receipt execution is simulated. They do not qualify cryptography.
Retained genuine receipt replays are a separate evidence lane.

## Preflight answers and retained behavior

The smallest behavior change is at publisher construction and reopening.
There is no wire, journal, economic-policy or root-encoding change. No new
dependency or publication entry point is required. The exact bound verifier
remains internal to existing core verification and authority-root derivation.
The profile-port handle additionally preserves the origin of leaf verification
for the next integration step.

The existing publisher is a large adapter. Its lengthy commit/recovery method
and exception classification are retained because this change does not alter
their ownership. Splitting that path now would enlarge the recovery regression
surface. Typed factory conversion is a small helper shared by create and open.
There is no generic-backend fallback, approval flag or test-only product branch.

## Falsifiers and acceptance evidence

Before repair, retain a regression in which the low-level bound type wraps a
recording backend and reaches publisher construction. After repair, this input
must reject before authority or journal writes at create, open and anchored
open. A forged or copied profile-port object must also reject. A valid measured
handle remains a positive control.

Retain the existing stateful publication tests: exact retry, competing writers,
source replacement from the acquired journal, proof rejection with no economic
change, response loss after commit, restart and monotonic-anchor recovery.
Preserve the backend-method substitution control when relocating the simulated
endpoint in test fixtures. The test fixture must not mint production authority
or bypass the measured factory.

Run scoped pytest, Ruff and mypy first. Broaden to the existing critical gate
after all coupled admission changes pass. Scanner output and review are triage;
the retained no-effect and successful-publication observations decide these
bounded obligations. Production deployment coverage, authenticated initial
ownership, every lane lifecycle and whole-runtime refinement remain open.
