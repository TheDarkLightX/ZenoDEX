/-!
# GlobalSettlementABI V1 — abstract structural core

A machine-checked *structural* core for part of the `GlobalSettlementABI V1`
object graph defined in `src/core/global_settlement_types_v1.py`. Everything
here is an abstraction chosen to be provable; it is deliberately narrower than
the Python ABI, and the gap is spelled out below rather than left implicit.

## The modeled surface

`GlobalEconomicEffectPlanV1` has six fields. This file models two of them, and
only partially:

* `rows` is abstracted as an **ordered accounting journal**
  (`AccountingJournal`), a plain list of `JournalEntry`. This is NOT the
  canonical `rows` tuple. The Python tuple is canonically sorted by
  `EconomicEffectRowV1.key` and validated by `_require_ordered_objects`;
  canonical ordering, deduplication, and per-key aggregation are all outside
  this file. Journal concatenation (`seqPlan`) is append-only and does not
  re-canonicalize, so it does not model runtime plan composition.
* `asset_conservation` is abstracted as two separately stored per-asset
  totals, `authorizedIssue` and `authorizedBurn`. The absolute
  `owned_and_custodied_pre/post_atoms` and `supply_pre/post_atoms` fields are
  represented as `AssetBook` columns rather than as plan fields.

The following are **not modeled at all**, and no theorem here says anything
about them:

* `fee_conservation` (`FeeConservationRowV1`) and `FEE_ALLOCATION` reconciliation;
* `lane_writes` (`LaneWriteV1`) and lane state roots;
* `occurrence_consumptions` and replay/nonce discipline;
* `external_outbox_enqueue` (`ExternalOutboxEnqueueV1`) and destination rules;
* canonical byte encoding, `hash_global_v1`, `effect_plan_root`, and every
  other root or digest;
* canonical ordering, deduplication, and aggregation of rows;
* state-object identity, `pre_state_root` / `post_state_root`, and the fact
  that a `LaneTransitionRejectedV1` returns the exact *root*. This file proves
  the analogous statement about the abstract book and abstract plan only.

## The Outcome analogy, and what it leaves out

`Outcome` is an analogy for `LaneTransitionAcceptedV1` and
`LaneTransitionRejectedV1`. It is much smaller than either.

`LaneTransitionAcceptedV1` has seven fields. Only `effects` has an analogue
here, and only the partial one described above. These five are **not modeled**,
and no theorem mentions them:

* `command_occurrence_id` — command identity and occurrence binding;
* `private_ports_root` — private port commitments;
* `receipt_root` — receipts. Nothing here confers receipt authority;
* `terminal_obligations` (`TerminalObligationV1`) — obligation identity,
  claimant, asset, amount, and `TerminalObligationStatusV1` lifecycle;
* `pre_state_root` / `post_state_root` — these are 32-byte roots, whereas
  `AssetBook` is a per-asset balance function. Equality of books is not
  equality of roots.

`LaneTransitionRejectedV1` has four fields. `code` and the abstract plan have
analogues; `pre_state_root` and `post_state_root` do not, for the same reason.
So `rejected_emits_empty_abstract_plan` is not a full reject no-op claim.

## Token and integer constraints, none of them modeled

`Asset`, `Principal`, and `ControlDomain` are plain `String`. The Python
`_require_token` rejects the empty string, anything above `MAX_TOKEN_BYTES_V1`
UTF-8 bytes, and any character outside printable ASCII `0x21`–`0x7E`. Roots
must additionally be 66 characters, lowercase, `0x`-prefixed 32-byte hex, and
usually nonzero. None of that syntax or size discipline is expressed here: a
`String` in this file may be empty, oversized, or non-ASCII.

Integer widths are likewise unmodeled. Python enforces `MAX_ATOMS_V1` for
`u128` fields, `MIN_DELTA_ATOMS_V1` and `MAX_DELTA_ATOMS_V1` for `i128`
deltas, and `MAX_U64_V1` for counters. `Int` here is unbounded in both
directions.

## Modeling decisions

Every quantity is indexed by asset. Book columns are functions `Asset → Int`
and the issue/burn projections take the asset as an argument, so no operation
adds atoms of unlike assets; `netIssuance_ignores_other_assets` states that as
a theorem.

`authorizedIssue` and `authorizedBurn` are stored separately, exactly as the
Python `AssetConservationRowV1` stores `authorized_issue_atoms` and
`authorized_burn_atoms`. Well-formedness pins each to the journal projection
independently. The net holdings and supply deltas are *derived* from the
difference. Because a net-preserving substitution such as `+1` issue and `+1`
burn leaves the derived deltas unchanged, requiring only the net would be
strictly weaker; `netPreservingSubstitution_not_wellFormed` proves the
strengthened predicate rejects exactly that.

Atom counts are `Int`. The Python fields are `u128`. Non-negativity is
therefore a *separate admission premise* (`NonNegativityAdmitted`), not a
consequence of conservation, and `nonNegativity_premise_is_necessary` exhibits
a well-formed plan that drives a non-negative book negative.

An accepted outcome is correct by construction: `Outcome` is indexed by the
pre-state and its `accepted` constructor carries an `Accepted pre plan post`
proof, so an accepted outcome without admission evidence cannot be written
down. Rejection carries only a code, so the returned book is definitionally
the pre-state and the returned plan is definitionally the empty abstract plan.

## Bounds and arithmetic

`NonNegative` is a **lower bound only**. Upper bounds are not modeled, and
neither is checked `i128` / `u128` arithmetic: the Python ABI enforces
`MAX_ATOMS_V1`, `MIN_DELTA_ATOMS_V1`, and `MAX_DELTA_ATOMS_V1`, and none of
those ceilings, nor any wrap-around or overflow behaviour, is proved here.

## Legal wording

`ControlDomain` and the `custody` effect kind are **uninterpreted labels**
carried over from the ABI's `custody_domain` field and `CUSTODY` enum value.
Nothing in this file reads them, and no statement here asserts custody,
possession, title, control, or any enforceable claim over any asset by any
party. `accountedHoldings` and `accountedSupply` are two ledger columns and
nothing more.

## What is NOT claimed

In addition to the unmodeled surface listed above: no economic-policy
correctness, no refinement between this model and the Python or Rust runtime,
no replay safety, no mounted authority or release-status gating, no production
readiness, and no commutativity of commands, lanes, or plans. `seqPlan` is
proved associative and unital as a full structure identity; it is *not* proved
commutative, and `seqPlan_journal_not_commutative` exhibits a pair whose
journal order differs under exchange.
-/

namespace Proofs
namespace GlobalSettlementCoreV1

/-! ## 1. Lane identifiers

The closed enumeration `LaneIdV1`. `code` reproduces the exact Python string
values and `allLaneIds_codes` pins the canonical order that `ALL_LANE_IDS_V1`
depends on. -/

/-- The twelve ABI V1 settlement lanes. -/
inductive LaneId where
  | assetTransfer
  | spotLiquidity
  | farmIncentives
  | zdexTokenomics
  | zusdMonetary
  | perpsMarket
  | oracleMarket
  | sealedAuction
  | strategyEscrow
  | proofRewards
  | externalCustody
  | governanceMigration
  deriving DecidableEq, Repr

/-- The stable wire string for each lane, matching `LaneIdV1` values. -/
def LaneId.code : LaneId → String
  | .assetTransfer => "ASSET_TRANSFER"
  | .spotLiquidity => "SPOT_LIQUIDITY"
  | .farmIncentives => "FARM_INCENTIVES"
  | .zdexTokenomics => "ZDEX_TOKENOMICS"
  | .zusdMonetary => "ZUSD_MONETARY"
  | .perpsMarket => "PERPS_MARKET"
  | .oracleMarket => "ORACLE_MARKET"
  | .sealedAuction => "SEALED_AUCTION"
  | .strategyEscrow => "STRATEGY_ESCROW"
  | .proofRewards => "PROOF_REWARDS"
  | .externalCustody => "EXTERNAL_CUSTODY"
  | .governanceMigration => "GOVERNANCE_MIGRATION"

/-- Canonical position of each lane, matching `ALL_LANE_IDS_V1.index`. -/
def LaneId.index : LaneId → Nat
  | .assetTransfer => 0
  | .spotLiquidity => 1
  | .farmIncentives => 2
  | .zdexTokenomics => 3
  | .zusdMonetary => 4
  | .perpsMarket => 5
  | .oracleMarket => 6
  | .sealedAuction => 7
  | .strategyEscrow => 8
  | .proofRewards => 9
  | .externalCustody => 10
  | .governanceMigration => 11

/-- The canonical lane order, mirroring `ALL_LANE_IDS_V1`. -/
def allLaneIds : List LaneId :=
  [ .assetTransfer, .spotLiquidity, .farmIncentives, .zdexTokenomics,
    .zusdMonetary, .perpsMarket, .oracleMarket, .sealedAuction,
    .strategyEscrow, .proofRewards, .externalCustody, .governanceMigration ]

/-- Boolean duplicate check, kept self-contained so the enumeration facts do
not depend on any library `Nodup` API. -/
def hasDuplicateLane : List LaneId → Bool
  | [] => false
  | l :: rest => rest.contains l || hasDuplicateLane rest

theorem allLaneIds_length : allLaneIds.length = 12 := rfl

/-- The canonical order, spelled out against the Python string values. -/
theorem allLaneIds_codes :
    allLaneIds.map LaneId.code =
      [ "ASSET_TRANSFER", "SPOT_LIQUIDITY", "FARM_INCENTIVES", "ZDEX_TOKENOMICS",
        "ZUSD_MONETARY", "PERPS_MARKET", "ORACLE_MARKET", "SEALED_AUCTION",
        "STRATEGY_ESCROW", "PROOF_REWARDS", "EXTERNAL_CUSTODY",
        "GOVERNANCE_MIGRATION" ] := rfl

theorem allLaneIds_indices :
    allLaneIds.map LaneId.index = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := rfl

/-- The enumeration is complete: there is no lane outside `allLaneIds`. -/
theorem allLaneIds_complete (l : LaneId) : l ∈ allLaneIds := by
  cases l <;> decide

/-- The enumeration has no repeats. Together with `allLaneIds_length` and
`allLaneIds_complete` this pins the lane set at exactly twelve members. -/
theorem allLaneIds_no_duplicates : hasDuplicateLane allLaneIds = false := by
  decide

theorem LaneId_index_lt_twelve (l : LaneId) : l.index < 12 := by
  cases l <;> decide

theorem LaneId_index_injective {a b : LaneId} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | exact absurd h (by decide)

/-! ## 2. Assets, principals, control-domain tags

These are uninterpreted tokens. `ControlDomain` corresponds to the ABI's
`custody_domain` field and is a label only: nothing in this file reads it, and
no theorem here asserts custody, possession, title, control, or any
enforceable claim over any asset. -/

abbrev Asset := String
abbrev Principal := String
abbrev ControlDomain := String

/-! ## 3. Journal entries

`EconomicEffectKindV1` as a closed enumeration, and the entry shape that
mirrors `EconomicEffectRowV1`'s fields. An entry is a line in an ordered
accounting journal, not a canonical ABI row. -/

/-- The closed set of economic effect kinds. `custody` is a label carried from
the ABI's `CUSTODY` value and carries no custody or possession meaning here. -/
inductive EffectKind where
  | accountMovement
  | issue
  | burn
  | custody
  | liability
  | reserve
  | feeAllocation
  | reward
  | slash
  deriving DecidableEq, Repr

/-- The stable wire string for each kind, matching `EconomicEffectKindV1`. -/
def EffectKind.code : EffectKind → String
  | .accountMovement => "ACCOUNT_MOVEMENT"
  | .issue => "ISSUE"
  | .burn => "BURN"
  | .custody => "CUSTODY"
  | .liability => "LIABILITY"
  | .reserve => "RESERVE"
  | .feeAllocation => "FEE_ALLOCATION"
  | .reward => "REWARD"
  | .slash => "SLASH"

/-- The declaration order of `EconomicEffectKindV1`. -/
def allEffectKinds : List EffectKind :=
  [ .accountMovement, .issue, .burn, .custody, .liability, .reserve,
    .feeAllocation, .reward, .slash ]

theorem allEffectKinds_length : allEffectKinds.length = 9 := rfl

theorem allEffectKinds_complete (k : EffectKind) : k ∈ allEffectKinds := by
  cases k <;> decide

theorem allEffectKinds_codes :
    allEffectKinds.map EffectKind.code =
      [ "ACCOUNT_MOVEMENT", "ISSUE", "BURN", "CUSTODY", "LIABILITY", "RESERVE",
        "FEE_ALLOCATION", "REWARD", "SLASH" ] := rfl

/-- A single line of an ordered accounting journal. The field shape mirrors
`EconomicEffectRowV1`, but a journal is not the canonical `rows` tuple: no
ordering, deduplication, or per-key aggregation is imposed here. -/
structure JournalEntry where
  kind : EffectKind
  principal : Principal
  asset : Asset
  controlDomain : ControlDomain
  deltaAtoms : Int
  deriving DecidableEq, Repr

/-- An ordered accounting journal. Append-only; not canonicalized. -/
abbrev AccountingJournal := List JournalEntry

/-- Entry-level invariants from `EconomicEffectRowV1.__post_init__`: the delta
is nonzero, an issue is strictly positive, and a burn is strictly negative. -/
structure EntryWellFormed (e : JournalEntry) : Prop where
  nonzero : e.deltaAtoms ≠ 0
  issuePositive : e.kind = EffectKind.issue → 0 < e.deltaAtoms
  burnNegative : e.kind = EffectKind.burn → e.deltaAtoms < 0

/-- The sign conventions, restated as a single citable fact. -/
theorem entryWellFormed_sign_conventions {e : JournalEntry} (h : EntryWellFormed e) :
    e.deltaAtoms ≠ 0 ∧
    (e.kind = EffectKind.issue → 0 < e.deltaAtoms) ∧
    (e.kind = EffectKind.burn → e.deltaAtoms < 0) :=
  ⟨h.nonzero, h.issuePositive, h.burnNegative⟩

/-! ## 4. Per-asset issue and burn projections

Each projection is indexed by asset. Entries for other assets contribute zero,
so atoms of unlike assets are never added together. -/

/-- Contribution of one entry to the issued total *for a named asset*. -/
def issuedAtoms (asset : Asset) (e : JournalEntry) : Int :=
  if e.kind = EffectKind.issue ∧ e.asset = asset then e.deltaAtoms else 0

/-- Contribution of one entry to the burned total *for a named asset*. Burn
entries carry a negative delta, so the burned magnitude is its negation,
matching `burn_by_asset[...] - row.delta_atoms` in the Python projection. -/
def burnedAtoms (asset : Asset) (e : JournalEntry) : Int :=
  if e.kind = EffectKind.burn ∧ e.asset = asset then -e.deltaAtoms else 0

/-- Total issue for one asset across a journal. -/
def issuedFor (asset : Asset) : AccountingJournal → Int
  | [] => 0
  | e :: rest => issuedAtoms asset e + issuedFor asset rest

/-- Total burn magnitude for one asset across a journal. -/
def burnedFor (asset : Asset) : AccountingJournal → Int
  | [] => 0
  | e :: rest => burnedAtoms asset e + burnedFor asset rest

/-- Net issuance for one asset: issued minus burned. -/
def netIssuance (asset : Asset) (journal : AccountingJournal) : Int :=
  issuedFor asset journal - burnedFor asset journal

theorem issuedFor_nil (asset : Asset) : issuedFor asset [] = 0 := rfl

theorem burnedFor_nil (asset : Asset) : burnedFor asset [] = 0 := rfl

theorem netIssuance_nil (asset : Asset) : netIssuance asset [] = 0 := rfl

theorem issuedFor_append (asset : Asset) (xs ys : AccountingJournal) :
    issuedFor asset (xs ++ ys) = issuedFor asset xs + issuedFor asset ys := by
  induction xs with
  | nil =>
      simp only [List.nil_append, issuedFor]
      omega
  | cons e rest ih =>
      simp only [List.cons_append, issuedFor, ih]
      omega

theorem burnedFor_append (asset : Asset) (xs ys : AccountingJournal) :
    burnedFor asset (xs ++ ys) = burnedFor asset xs + burnedFor asset ys := by
  induction xs with
  | nil =>
      simp only [List.nil_append, burnedFor]
      omega
  | cons e rest ih =>
      simp only [List.cons_append, burnedFor, ih]
      omega

theorem netIssuance_append (asset : Asset) (xs ys : AccountingJournal) :
    netIssuance asset (xs ++ ys) = netIssuance asset xs + netIssuance asset ys := by
  simp only [netIssuance, issuedFor_append, burnedFor_append]
  omega

/-- An entry for a different asset contributes nothing to that asset's issue
total. This is the formal content of "never sum unlike assets". -/
theorem issuedAtoms_of_other_asset {asset : Asset} {e : JournalEntry}
    (h : e.asset ≠ asset) : issuedAtoms asset e = 0 := by
  simp only [issuedAtoms]
  exact if_neg (fun hc => h hc.2)

theorem burnedAtoms_of_other_asset {asset : Asset} {e : JournalEntry}
    (h : e.asset ≠ asset) : burnedAtoms asset e = 0 := by
  simp only [burnedAtoms]
  exact if_neg (fun hc => h hc.2)

theorem issuedFor_cons_of_other_asset {asset : Asset} {e : JournalEntry}
    {rest : AccountingJournal} (h : e.asset ≠ asset) :
    issuedFor asset (e :: rest) = issuedFor asset rest := by
  simp only [issuedFor, issuedAtoms_of_other_asset h]
  omega

theorem burnedFor_cons_of_other_asset {asset : Asset} {e : JournalEntry}
    {rest : AccountingJournal} (h : e.asset ≠ asset) :
    burnedFor asset (e :: rest) = burnedFor asset rest := by
  simp only [burnedFor, burnedAtoms_of_other_asset h]
  omega

/-- Asset separation, stated on the net projection. -/
theorem netIssuance_ignores_other_assets {asset : Asset} {e : JournalEntry}
    {rest : AccountingJournal} (h : e.asset ≠ asset) :
    netIssuance asset (e :: rest) = netIssuance asset rest := by
  simp only [netIssuance, issuedFor_cons_of_other_asset h,
    burnedFor_cons_of_other_asset h]

/-- Under the entry invariants the issued total is non-negative. This is a
lower bound only; no upper bound and no checked-arithmetic ceiling is proved. -/
theorem issuedFor_nonneg {asset : Asset} {journal : AccountingJournal}
    (h : ∀ e ∈ journal, EntryWellFormed e) : 0 ≤ issuedFor asset journal := by
  induction journal with
  | nil =>
      simp only [issuedFor]
      decide
  | cons e rest ih =>
      have he : EntryWellFormed e := h e List.mem_cons_self
      have hrest : ∀ x ∈ rest, EntryWellFormed x :=
        fun x hx => h x (List.mem_cons_of_mem e hx)
      have hhead : 0 ≤ issuedAtoms asset e := by
        simp only [issuedAtoms]
        split
        · next hc =>
            have hpos := he.issuePositive hc.1
            omega
        · omega
      have htail := ih hrest
      simp only [issuedFor]
      omega

/-- Under the entry invariants the burned magnitude is non-negative. Lower
bound only, as above. -/
theorem burnedFor_nonneg {asset : Asset} {journal : AccountingJournal}
    (h : ∀ e ∈ journal, EntryWellFormed e) : 0 ≤ burnedFor asset journal := by
  induction journal with
  | nil =>
      simp only [burnedFor]
      decide
  | cons e rest ih =>
      have he : EntryWellFormed e := h e List.mem_cons_self
      have hrest : ∀ x ∈ rest, EntryWellFormed x :=
        fun x hx => h x (List.mem_cons_of_mem e hx)
      have hhead : 0 ≤ burnedAtoms asset e := by
        simp only [burnedAtoms]
        split
        · next hc =>
            have hneg := he.burnNegative hc.1
            omega
        · omega
      have htail := ih hrest
      simp only [burnedFor]
      omega

/-! ## 5. Abstract effect plans

An abstract plan carries an ordered journal plus the two separately stored
per-asset totals of `AssetConservationRowV1`. The net holdings and supply
deltas are derived from their difference, so both book columns necessarily
move together; well-formedness is what ties those totals to the journal. -/

/-- An abstract effect plan. This models `rows` (as a non-canonical journal)
and the `authorized_issue_atoms` / `authorized_burn_atoms` totals only. Fee
conservation, lane writes, occurrence consumptions, and the external outbox
are not represented. -/
structure AbstractEffectPlan where
  journal : AccountingJournal
  authorizedIssue : Asset → Int
  authorizedBurn : Asset → Int

/-- Derived per-asset accounted-holdings delta. -/
def AbstractEffectPlan.holdingsDelta (p : AbstractEffectPlan) (a : Asset) : Int :=
  p.authorizedIssue a - p.authorizedBurn a

/-- Derived per-asset accounted-supply delta. -/
def AbstractEffectPlan.supplyDelta (p : AbstractEffectPlan) (a : Asset) : Int :=
  p.authorizedIssue a - p.authorizedBurn a

/-- Both derived deltas are the same expression, by construction. -/
theorem holdingsDelta_eq_supplyDelta (p : AbstractEffectPlan) (a : Asset) :
    p.holdingsDelta a = p.supplyDelta a := rfl

/-- Structure extensionality for abstract plans. -/
theorem AbstractEffectPlan.ext : ∀ {p q : AbstractEffectPlan},
    p.journal = q.journal → p.authorizedIssue = q.authorizedIssue →
    p.authorizedBurn = q.authorizedBurn → p = q
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl, rfl => rfl

/-- Plan well-formedness: each stored total is pinned to the corresponding
journal projection *independently*. Requiring only the net difference would be
strictly weaker; see `netPreservingSubstitution_not_wellFormed`. -/
structure PlanWellFormed (p : AbstractEffectPlan) : Prop where
  issue : ∀ a : Asset, p.authorizedIssue a = issuedFor a p.journal
  burn : ∀ a : Asset, p.authorizedBurn a = burnedFor a p.journal

/-- Entry invariants lifted to a whole plan. -/
def PlanEntriesWellFormed (p : AbstractEffectPlan) : Prop :=
  ∀ e ∈ p.journal, EntryWellFormed e

/-- A well-formed plan's derived deltas agree with the journal's net issuance. -/
theorem wellFormed_holdingsDelta_eq_netIssuance {p : AbstractEffectPlan}
    (h : PlanWellFormed p) (a : Asset) :
    p.holdingsDelta a = netIssuance a p.journal := by
  simp only [AbstractEffectPlan.holdingsDelta, h.issue a, h.burn a, netIssuance]

theorem wellFormed_supplyDelta_eq_netIssuance {p : AbstractEffectPlan}
    (h : PlanWellFormed p) (a : Asset) :
    p.supplyDelta a = netIssuance a p.journal :=
  wellFormed_holdingsDelta_eq_netIssuance h a

/-- The identity plan. This is the empty *abstract* plan: an empty journal and
zero authorized totals. It is not a claim that a Python
`GlobalEconomicEffectPlanV1` is empty in every field. -/
def identityPlan : AbstractEffectPlan where
  journal := []
  authorizedIssue := fun _ => 0
  authorizedBurn := fun _ => 0

/-- The empty abstract plan carried by every rejection. -/
abbrev emptyAbstractPlan : AbstractEffectPlan := identityPlan

/-- Journal-order composition: journals concatenate, authorized totals add per
asset. Append-only; this does not re-canonicalize and does not model runtime
plan composition. -/
def seqPlan (p q : AbstractEffectPlan) : AbstractEffectPlan where
  journal := p.journal ++ q.journal
  authorizedIssue := fun a => p.authorizedIssue a + q.authorizedIssue a
  authorizedBurn := fun a => p.authorizedBurn a + q.authorizedBurn a

theorem identityPlan_journal : identityPlan.journal = [] := rfl

theorem identityPlan_authorizedIssue (a : Asset) :
    identityPlan.authorizedIssue a = 0 := rfl

theorem identityPlan_authorizedBurn (a : Asset) :
    identityPlan.authorizedBurn a = 0 := rfl

theorem identityPlan_holdingsDelta (a : Asset) :
    identityPlan.holdingsDelta a = 0 := rfl

theorem identityPlan_supplyDelta (a : Asset) :
    identityPlan.supplyDelta a = 0 := rfl

/-- The identity plan is well-formed. -/
theorem identityPlan_wellFormed : PlanWellFormed identityPlan :=
  { issue := fun _ => rfl, burn := fun _ => rfl }

theorem identityPlan_entriesWellFormed : PlanEntriesWellFormed identityPlan := by
  intro e he
  simp [identityPlan] at he

/-- Sequential composition preserves well-formedness. -/
theorem seqPlan_wellFormed {p q : AbstractEffectPlan}
    (hp : PlanWellFormed p) (hq : PlanWellFormed q) :
    PlanWellFormed (seqPlan p q) := by
  constructor
  · intro a
    simp only [seqPlan, issuedFor_append, hp.issue a, hq.issue a]
  · intro a
    simp only [seqPlan, burnedFor_append, hp.burn a, hq.burn a]

/-- Sequential composition preserves the entry invariants. -/
theorem seqPlan_entriesWellFormed {p q : AbstractEffectPlan}
    (hp : PlanEntriesWellFormed p) (hq : PlanEntriesWellFormed q) :
    PlanEntriesWellFormed (seqPlan p q) := by
  intro e he
  simp only [seqPlan, List.mem_append] at he
  cases he with
  | inl h => exact hp e h
  | inr h => exact hq e h

/-- Left unit, as a full structure identity. -/
theorem seqPlan_identity_left (p : AbstractEffectPlan) :
    seqPlan identityPlan p = p :=
  AbstractEffectPlan.ext
    (List.nil_append p.journal)
    (funext (fun a => by
      show (0 : Int) + p.authorizedIssue a = p.authorizedIssue a
      omega))
    (funext (fun a => by
      show (0 : Int) + p.authorizedBurn a = p.authorizedBurn a
      omega))

/-- Right unit, as a full structure identity. -/
theorem seqPlan_identity_right (p : AbstractEffectPlan) :
    seqPlan p identityPlan = p :=
  AbstractEffectPlan.ext
    (List.append_nil p.journal)
    (funext (fun a => by
      show p.authorizedIssue a + (0 : Int) = p.authorizedIssue a
      omega))
    (funext (fun a => by
      show p.authorizedBurn a + (0 : Int) = p.authorizedBurn a
      omega))

/-- Associativity, as a full structure identity. Associativity is not
commutativity; see `seqPlan_journal_not_commutative`. -/
theorem seqPlan_assoc (p q r : AbstractEffectPlan) :
    seqPlan (seqPlan p q) r = seqPlan p (seqPlan q r) :=
  AbstractEffectPlan.ext
    (List.append_assoc p.journal q.journal r.journal)
    (funext (fun a => by
      show p.authorizedIssue a + q.authorizedIssue a + r.authorizedIssue a
        = p.authorizedIssue a + (q.authorizedIssue a + r.authorizedIssue a)
      omega))
    (funext (fun a => by
      show p.authorizedBurn a + q.authorizedBurn a + r.authorizedBurn a
        = p.authorizedBurn a + (q.authorizedBurn a + r.authorizedBurn a)
      omega))

/-- Journal order under composition. -/
theorem seqPlan_journal (p q : AbstractEffectPlan) :
    (seqPlan p q).journal = p.journal ++ q.journal := rfl

/-! ## 6. Books

Two distinct accounted columns. `accountedHoldings` corresponds to
`owned_and_custodied_*_atoms` and `accountedSupply` to `supply_*_atoms`. They
are ledger columns; neither asserts custody, possession, or title. -/

/-- Per-asset accounted balances. -/
structure AssetBook where
  accountedHoldings : Asset → Int
  accountedSupply : Asset → Int

/-- The signed gap between the two accounted columns, per asset. -/
def gap (b : AssetBook) (a : Asset) : Int :=
  b.accountedHoldings a - b.accountedSupply a

/-- The property that accounted holdings equal accounted supply, per asset. A
statement about two ledger columns only. -/
def HoldingsMatchSupply (b : AssetBook) : Prop :=
  ∀ a : Asset, b.accountedHoldings a = b.accountedSupply a

/-- Lower bound only: both accounted columns are non-negative. No upper bound
and no checked `i128` / `u128` arithmetic is modeled. -/
def NonNegative (b : AssetBook) : Prop :=
  ∀ a : Asset, 0 ≤ b.accountedHoldings a ∧ 0 ≤ b.accountedSupply a

/-! ## 7. Application -/

/-- The pre/post application relation for an abstract plan. -/
structure Applies (pre : AssetBook) (p : AbstractEffectPlan) (post : AssetBook) : Prop where
  holdings : ∀ a : Asset,
    post.accountedHoldings a = pre.accountedHoldings a + p.holdingsDelta a
  supply : ∀ a : Asset,
    post.accountedSupply a = pre.accountedSupply a + p.supplyDelta a

/-- The canonical post-book produced by applying a plan. -/
def applyPlan (pre : AssetBook) (p : AbstractEffectPlan) : AssetBook where
  accountedHoldings := fun a => pre.accountedHoldings a + p.holdingsDelta a
  accountedSupply := fun a => pre.accountedSupply a + p.supplyDelta a

/-- `applyPlan` inhabits the relation, so `Applies` is never vacuous. -/
theorem applyPlan_applies (pre : AssetBook) (p : AbstractEffectPlan) :
    Applies pre p (applyPlan pre p) := by
  constructor
  · intro a
    rfl
  · intro a
    rfl

/-- The gap between the two accounted columns is invariant under application.

No well-formedness hypothesis is needed: because `holdingsDelta` and
`supplyDelta` are *derived* from the same `authorizedIssue - authorizedBurn`
difference, both columns move together by construction. Well-formedness is
what ties that common movement to the journal, which is
`wellFormed_applies_moves_by_netIssuance`. -/
theorem applies_preserves_gap {pre post : AssetBook} {p : AbstractEffectPlan}
    (happ : Applies pre p post) (a : Asset) : gap post a = gap pre a := by
  have hh := happ.holdings a
  have hs := happ.supply a
  have hd : p.holdingsDelta a = p.supplyDelta a := rfl
  simp only [gap, hh, hs, hd]
  omega

/-- Application preserves the equality of the two accounted columns. -/
theorem applies_preserves_holdingsMatchSupply {pre post : AssetBook}
    {p : AbstractEffectPlan} (happ : Applies pre p post)
    (hmatch : HoldingsMatchSupply pre) : HoldingsMatchSupply post := by
  intro a
  have hgap := applies_preserves_gap happ a
  have hpre := hmatch a
  simp only [gap] at hgap
  omega

/-- For a well-formed plan, both columns move by exactly the journal's net
issuance for that asset. This is the statement with real content: it links
state movement to journal contents. -/
theorem wellFormed_applies_moves_by_netIssuance {pre post : AssetBook}
    {p : AbstractEffectPlan} (hwf : PlanWellFormed p) (happ : Applies pre p post)
    (a : Asset) :
    post.accountedHoldings a = pre.accountedHoldings a + netIssuance a p.journal ∧
    post.accountedSupply a = pre.accountedSupply a + netIssuance a p.journal := by
  have hh := happ.holdings a
  have hs := happ.supply a
  have hdh := wellFormed_holdingsDelta_eq_netIssuance hwf a
  have hds := wellFormed_supplyDelta_eq_netIssuance hwf a
  constructor
  · rw [hh, hdh]
  · rw [hs, hds]

/-! ## 8. Non-negativity as a separate acceptance premise

Conservation alone does not keep balances non-negative. The runtime rejects a
plan whose result would underflow, and that check is an explicit admission
premise here rather than a derived fact. This covers the lower bound only. -/

/-- The admission check: the post-book this plan would produce is non-negative
in both columns for every asset. -/
def NonNegativityAdmitted (pre : AssetBook) (p : AbstractEffectPlan) : Prop :=
  ∀ a : Asset,
    0 ≤ pre.accountedHoldings a + p.holdingsDelta a ∧
    0 ≤ pre.accountedSupply a + p.supplyDelta a

/-- An accepted transition: a well-formed plan with well-formed journal
entries, applied to the pre-book, whose non-negativity was separately
admitted. -/
structure Accepted (pre : AssetBook) (p : AbstractEffectPlan) (post : AssetBook) : Prop where
  planWellFormed : PlanWellFormed p
  entriesWellFormed : PlanEntriesWellFormed p
  applies : Applies pre p post
  nonNegativityAdmitted : NonNegativityAdmitted pre p

/-- Accepted transitions preserve the holdings/supply equality. -/
theorem accepted_preserves_holdingsMatchSupply {pre post : AssetBook}
    {p : AbstractEffectPlan} (hacc : Accepted pre p post)
    (hmatch : HoldingsMatchSupply pre) : HoldingsMatchSupply post :=
  applies_preserves_holdingsMatchSupply hacc.applies hmatch

/-- Non-negativity of the post-book follows *from the admission premise*, and
only from it. -/
theorem accepted_post_nonNegative {pre post : AssetBook} {p : AbstractEffectPlan}
    (hacc : Accepted pre p post) : NonNegative post := by
  intro a
  have hadm := hacc.nonNegativityAdmitted a
  have hh := hacc.applies.holdings a
  have hs := hacc.applies.supply a
  have h1 := hadm.1
  have h2 := hadm.2
  exact ⟨by omega, by omega⟩

/-- Accepted transitions move both columns by the journal's net issuance. -/
theorem accepted_moves_by_netIssuance {pre post : AssetBook}
    {p : AbstractEffectPlan} (hacc : Accepted pre p post) (a : Asset) :
    post.accountedHoldings a = pre.accountedHoldings a + netIssuance a p.journal ∧
    post.accountedSupply a = pre.accountedSupply a + netIssuance a p.journal :=
  wellFormed_applies_moves_by_netIssuance hacc.planWellFormed hacc.applies a

/-! ## 9. Typed rejection and outcomes correct by construction

`Outcome` is indexed by the pre-book, and `accepted` carries an
`Accepted pre plan post` proof, so an accepted outcome that lacks admission
evidence is not expressible. `rejected` carries only a code, so the returned
book is definitionally the pre-book and the returned plan is definitionally
the empty abstract plan. -/

/-- The closed set of rejection codes from `LaneTransitionRejectCodeV1`. -/
inductive RejectCode where
  | unknownCommand
  | disabledFeature
  | releaseMismatch
  | invalidContext
  | invalidState
  | policyReject
  | resourceLimit
  deriving DecidableEq, Repr

/-- The stable wire string for each code. -/
def RejectCode.code : RejectCode → String
  | .unknownCommand => "UNKNOWN_COMMAND"
  | .disabledFeature => "DISABLED_FEATURE"
  | .releaseMismatch => "RELEASE_MISMATCH"
  | .invalidContext => "INVALID_CONTEXT"
  | .invalidState => "INVALID_STATE"
  | .policyReject => "POLICY_REJECT"
  | .resourceLimit => "RESOURCE_LIMIT"

def allRejectCodes : List RejectCode :=
  [ .unknownCommand, .disabledFeature, .releaseMismatch, .invalidContext,
    .invalidState, .policyReject, .resourceLimit ]

theorem allRejectCodes_length : allRejectCodes.length = 7 := rfl

theorem allRejectCodes_complete (c : RejectCode) : c ∈ allRejectCodes := by
  cases c <;> decide

theorem allRejectCodes_codes :
    allRejectCodes.map RejectCode.code =
      [ "UNKNOWN_COMMAND", "DISABLED_FEATURE", "RELEASE_MISMATCH",
        "INVALID_CONTEXT", "INVALID_STATE", "POLICY_REJECT",
        "RESOURCE_LIMIT" ] := rfl

/-- The outcome of a lane transition attempt against a fixed pre-book. The
`accepted` constructor carries its own admission evidence. -/
inductive Outcome (pre : AssetBook) where
  | accepted (plan : AbstractEffectPlan) (post : AssetBook)
      (evidence : Accepted pre plan post)
  | rejected (code : RejectCode)

/-- The book observed after an outcome. -/
def Outcome.postState {pre : AssetBook} : Outcome pre → AssetBook
  | .accepted _ post _ => post
  | .rejected _ => pre

/-- The abstract effect plan emitted by an outcome. -/
def Outcome.effects {pre : AssetBook} : Outcome pre → AbstractEffectPlan
  | .accepted plan _ _ => plan
  | .rejected _ => emptyAbstractPlan

/-- Every rejection returns the exact pre-book. -/
theorem rejected_postState (pre : AssetBook) (c : RejectCode) :
    (Outcome.rejected c : Outcome pre).postState = pre := rfl

/-- Every rejection emits the empty *abstract* plan.

This is a claim about the modeled surface only: the empty journal and zero
authorized issue/burn totals. Fee conservation rows, lane writes, occurrence
consumptions, and external outbox entries are not represented here, so this
does not assert that a Python `GlobalEconomicEffectPlanV1` is empty in every
field. -/
theorem rejected_emits_empty_abstract_plan (pre : AssetBook) (c : RejectCode) :
    (Outcome.rejected c : Outcome pre).effects = emptyAbstractPlan := rfl

theorem rejected_effects_journal (pre : AssetBook) (c : RejectCode) :
    (Outcome.rejected c : Outcome pre).effects.journal = [] := rfl

theorem rejected_effects_authorizedIssue (pre : AssetBook) (c : RejectCode)
    (a : Asset) :
    (Outcome.rejected c : Outcome pre).effects.authorizedIssue a = 0 := rfl

theorem rejected_effects_authorizedBurn (pre : AssetBook) (c : RejectCode)
    (a : Asset) :
    (Outcome.rejected c : Outcome pre).effects.authorizedBurn a = 0 := rfl

/-- Pointwise restatement: no accounted balance moves under a rejection. -/
theorem rejected_preserves_holdings (pre : AssetBook) (c : RejectCode) (a : Asset) :
    ((Outcome.rejected c : Outcome pre).postState).accountedHoldings a
      = pre.accountedHoldings a := rfl

theorem rejected_preserves_supply (pre : AssetBook) (c : RejectCode) (a : Asset) :
    ((Outcome.rejected c : Outcome pre).postState).accountedSupply a
      = pre.accountedSupply a := rfl

/-- Applying the identity plan leaves the book unchanged. -/
theorem applies_identityPlan (pre : AssetBook) : Applies pre identityPlan pre := by
  constructor
  · intro a
    show pre.accountedHoldings a = pre.accountedHoldings a + 0
    omega
  · intro a
    show pre.accountedSupply a = pre.accountedSupply a + 0
    omega

/-- A rejected outcome applies the empty abstract plan to the pre-book. -/
theorem rejected_applies_identity (pre : AssetBook) (c : RejectCode) :
    Applies pre (Outcome.rejected c : Outcome pre).effects
      ((Outcome.rejected c : Outcome pre).postState) :=
  applies_identityPlan pre

/-- Every accepted outcome is correct by construction: it carries plan
well-formedness, entry well-formedness, the application relation between the
pre-book and the recorded post-book, and a non-negative post-book. -/
theorem accepted_outcome_carries_evidence {pre : AssetBook}
    (plan : AbstractEffectPlan) (post : AssetBook) (ev : Accepted pre plan post) :
    PlanWellFormed (Outcome.accepted plan post ev : Outcome pre).effects ∧
    PlanEntriesWellFormed (Outcome.accepted plan post ev : Outcome pre).effects ∧
    Applies pre (Outcome.accepted plan post ev : Outcome pre).effects
      ((Outcome.accepted plan post ev : Outcome pre).postState) ∧
    NonNegative ((Outcome.accepted plan post ev : Outcome pre).postState) :=
  ⟨ev.planWellFormed, ev.entriesWellFormed, ev.applies, accepted_post_nonNegative ev⟩

/-- Every outcome, accepted or rejected, applies its emitted plan to the
pre-book to reach its post-book. -/
theorem outcome_applies {pre : AssetBook} (o : Outcome pre) :
    Applies pre o.effects o.postState := by
  cases o with
  | accepted plan post ev => exact ev.applies
  | rejected c => exact rejected_applies_identity pre c

/-- Every outcome emits a well-formed plan. -/
theorem outcome_effects_wellFormed {pre : AssetBook} (o : Outcome pre) :
    PlanWellFormed o.effects := by
  cases o with
  | accepted plan post ev => exact ev.planWellFormed
  | rejected c => exact identityPlan_wellFormed

/-- Every outcome emits a plan with well-formed journal entries. -/
theorem outcome_effects_entriesWellFormed {pre : AssetBook} (o : Outcome pre) :
    PlanEntriesWellFormed o.effects := by
  cases o with
  | accepted plan post ev => exact ev.entriesWellFormed
  | rejected c => exact identityPlan_entriesWellFormed

/-- From a non-negative pre-book, every outcome yields a non-negative
post-book: accepted ones by their admission evidence, rejected ones because
they return the pre-book unchanged. -/
theorem outcome_postState_nonNegative {pre : AssetBook} (hpre : NonNegative pre)
    (o : Outcome pre) : NonNegative o.postState := by
  cases o with
  | accepted plan post ev => exact accepted_post_nonNegative ev
  | rejected c => exact hpre

/-- From a matched pre-book, every outcome yields a matched post-book. -/
theorem outcome_postState_holdingsMatchSupply {pre : AssetBook}
    (hpre : HoldingsMatchSupply pre) (o : Outcome pre) :
    HoldingsMatchSupply o.postState :=
  applies_preserves_holdingsMatchSupply (outcome_applies o) hpre

/-- Outcomes are exactly accepted or rejected. -/
theorem outcome_dichotomy {pre : AssetBook} (o : Outcome pre) :
    (∃ (plan : AbstractEffectPlan) (post : AssetBook)
        (ev : Accepted pre plan post), o = Outcome.accepted plan post ev) ∨
    (∃ c : RejectCode, o = Outcome.rejected c) := by
  cases o with
  | accepted plan post ev => exact Or.inl ⟨plan, post, ev, rfl⟩
  | rejected c => exact Or.inr ⟨c, rfl⟩

/-! ## 10. Non-vacuity witnesses

One same-asset transfer, one managed issue, one burn, and one two-asset
journal showing that unlike assets stay separate. -/

def zusd : Asset := "ZUSD"
def zdex : Asset := "ZDEX"
def alice : Principal := "alice"
def bob : Principal := "bob"
def treasury : Principal := "treasury"
def ledgerDomain : ControlDomain := "zenoledger:core"

theorem zusd_ne_zdex : zusd ≠ zdex := by decide

/-- A ledger-internal transfer: one debit and one credit of the same asset. -/
def transferJournal : AccountingJournal :=
  [ { kind := .accountMovement, principal := alice, asset := zusd,
      controlDomain := ledgerDomain, deltaAtoms := -100 },
    { kind := .accountMovement, principal := bob, asset := zusd,
      controlDomain := ledgerDomain, deltaAtoms := 100 } ]

def transferPlan : AbstractEffectPlan where
  journal := transferJournal
  authorizedIssue := fun _ => 0
  authorizedBurn := fun _ => 0

/-- A managed issue of 250 atoms to the treasury principal. -/
def issueJournal : AccountingJournal :=
  [ { kind := .issue, principal := treasury, asset := zusd,
      controlDomain := ledgerDomain, deltaAtoms := 250 } ]

def issuePlan : AbstractEffectPlan where
  journal := issueJournal
  authorizedIssue := fun a => if zusd = a then 250 else 0
  authorizedBurn := fun _ => 0

/-- A burn of 70 atoms from the treasury principal. -/
def burnJournal : AccountingJournal :=
  [ { kind := .burn, principal := treasury, asset := zusd,
      controlDomain := ledgerDomain, deltaAtoms := -70 } ]

def burnPlan : AbstractEffectPlan where
  journal := burnJournal
  authorizedIssue := fun _ => 0
  authorizedBurn := fun a => if zusd = a then 70 else 0

theorem transferPlan_journal_ne_nil : transferPlan.journal ≠ [] := by decide

theorem issuePlan_journal_ne_nil : issuePlan.journal ≠ [] := by decide

theorem burnPlan_journal_ne_nil : burnPlan.journal ≠ [] := by decide

theorem transferPlan_entriesWellFormed : PlanEntriesWellFormed transferPlan := by
  intro e he
  simp [transferPlan, transferJournal] at he
  cases he with
  | inl h =>
      subst h
      exact ⟨by decide, by intro hk; exact absurd hk (by decide),
        by intro hk; exact absurd hk (by decide)⟩
  | inr h =>
      subst h
      exact ⟨by decide, by intro hk; exact absurd hk (by decide),
        by intro hk; exact absurd hk (by decide)⟩

theorem issuePlan_entriesWellFormed : PlanEntriesWellFormed issuePlan := by
  intro e he
  simp [issuePlan, issueJournal] at he
  subst he
  exact ⟨by decide, by intro _; decide, by intro hk; exact absurd hk (by decide)⟩

theorem burnPlan_entriesWellFormed : PlanEntriesWellFormed burnPlan := by
  intro e he
  simp [burnPlan, burnJournal] at he
  subst he
  exact ⟨by decide, by intro hk; exact absurd hk (by decide), by intro _; decide⟩

/-- A same-asset transfer authorizes no issue for any asset. -/
theorem transferJournal_issuedFor (a : Asset) : issuedFor a transferJournal = 0 := by
  simp [transferJournal, issuedFor, issuedAtoms]

theorem transferJournal_burnedFor (a : Asset) : burnedFor a transferJournal = 0 := by
  simp [transferJournal, burnedFor, burnedAtoms]

theorem transferPlan_wellFormed : PlanWellFormed transferPlan :=
  { issue := fun a => (transferJournal_issuedFor a).symm
    burn := fun a => (transferJournal_burnedFor a).symm }

theorem issueJournal_issuedFor_zusd : issuedFor zusd issueJournal = 250 := by decide

theorem issueJournal_issuedFor_other {a : Asset} (h : zusd ≠ a) :
    issuedFor a issueJournal = 0 := by
  simp [issueJournal, issuedFor, issuedAtoms, h]

theorem issueJournal_burnedFor (a : Asset) : burnedFor a issueJournal = 0 := by
  simp [issueJournal, burnedFor, burnedAtoms]

theorem issuePlan_wellFormed : PlanWellFormed issuePlan := by
  constructor
  · intro a
    show (if zusd = a then (250 : Int) else 0) = issuedFor a issueJournal
    by_cases h : zusd = a
    · subst h
      rw [if_pos (rfl : zusd = zusd)]
      exact issueJournal_issuedFor_zusd.symm
    · rw [if_neg h]
      exact (issueJournal_issuedFor_other h).symm
  · intro a
    show (0 : Int) = burnedFor a issueJournal
    exact (issueJournal_burnedFor a).symm

theorem burnJournal_issuedFor (a : Asset) : issuedFor a burnJournal = 0 := by
  simp [burnJournal, issuedFor, issuedAtoms]

theorem burnJournal_burnedFor_zusd : burnedFor zusd burnJournal = 70 := by decide

theorem burnJournal_burnedFor_other {a : Asset} (h : zusd ≠ a) :
    burnedFor a burnJournal = 0 := by
  simp [burnJournal, burnedFor, burnedAtoms, h]

theorem burnPlan_wellFormed : PlanWellFormed burnPlan := by
  constructor
  · intro a
    show (0 : Int) = issuedFor a burnJournal
    exact (burnJournal_issuedFor a).symm
  · intro a
    show (if zusd = a then (70 : Int) else 0) = burnedFor a burnJournal
    by_cases h : zusd = a
    · subst h
      rw [if_pos (rfl : zusd = zusd)]
      exact burnJournal_burnedFor_zusd.symm
    · rw [if_neg h]
      exact (burnJournal_burnedFor_other h).symm

/-- A demonstration book holding 1000 atoms of ZUSD in both columns. -/
def demoBook : AssetBook where
  accountedHoldings := fun a => if zusd = a then 1000 else 0
  accountedSupply := fun a => if zusd = a then 1000 else 0

theorem demoBook_holdingsMatchSupply : HoldingsMatchSupply demoBook := by
  intro a
  rfl

theorem demoBook_nonNegative : NonNegative demoBook := by
  intro a
  by_cases h : zusd = a
  · subst h
    exact ⟨by decide, by decide⟩
  · simp only [demoBook, if_neg h]
    exact ⟨by decide, by decide⟩

theorem transferPlan_admitted : NonNegativityAdmitted demoBook transferPlan := by
  intro a
  by_cases h : zusd = a
  · subst h
    exact ⟨by decide, by decide⟩
  · simp only [demoBook, transferPlan, AbstractEffectPlan.holdingsDelta,
      AbstractEffectPlan.supplyDelta, if_neg h]
    exact ⟨by decide, by decide⟩

theorem issuePlan_admitted : NonNegativityAdmitted demoBook issuePlan := by
  intro a
  by_cases h : zusd = a
  · subst h
    exact ⟨by decide, by decide⟩
  · simp only [demoBook, issuePlan, AbstractEffectPlan.holdingsDelta,
      AbstractEffectPlan.supplyDelta, if_neg h]
    exact ⟨by decide, by decide⟩

theorem burnPlan_admitted : NonNegativityAdmitted demoBook burnPlan := by
  intro a
  by_cases h : zusd = a
  · subst h
    exact ⟨by decide, by decide⟩
  · simp only [demoBook, burnPlan, AbstractEffectPlan.holdingsDelta,
      AbstractEffectPlan.supplyDelta, if_neg h]
    exact ⟨by decide, by decide⟩

/-- Witness 1: a transfer is an accepted transition. -/
theorem transfer_accepted :
    Accepted demoBook transferPlan (applyPlan demoBook transferPlan) :=
  { planWellFormed := transferPlan_wellFormed
    entriesWellFormed := transferPlan_entriesWellFormed
    applies := applyPlan_applies demoBook transferPlan
    nonNegativityAdmitted := transferPlan_admitted }

/-- Witness 2: a managed issue is an accepted transition. -/
theorem issue_accepted :
    Accepted demoBook issuePlan (applyPlan demoBook issuePlan) :=
  { planWellFormed := issuePlan_wellFormed
    entriesWellFormed := issuePlan_entriesWellFormed
    applies := applyPlan_applies demoBook issuePlan
    nonNegativityAdmitted := issuePlan_admitted }

/-- Witness 3: a burn is an accepted transition. -/
theorem burn_accepted :
    Accepted demoBook burnPlan (applyPlan demoBook burnPlan) :=
  { planWellFormed := burnPlan_wellFormed
    entriesWellFormed := burnPlan_entriesWellFormed
    applies := applyPlan_applies demoBook burnPlan
    nonNegativityAdmitted := burnPlan_admitted }

/-- The three witnesses as accepted outcomes, which exist only because the
admission evidence above exists. -/
def transferOutcome : Outcome demoBook :=
  .accepted transferPlan (applyPlan demoBook transferPlan) transfer_accepted

def issueOutcome : Outcome demoBook :=
  .accepted issuePlan (applyPlan demoBook issuePlan) issue_accepted

def burnOutcome : Outcome demoBook :=
  .accepted burnPlan (applyPlan demoBook burnPlan) burn_accepted

theorem transferOutcome_nonNegative : NonNegative transferOutcome.postState :=
  outcome_postState_nonNegative demoBook_nonNegative transferOutcome

theorem issueOutcome_nonNegative : NonNegative issueOutcome.postState :=
  outcome_postState_nonNegative demoBook_nonNegative issueOutcome

theorem burnOutcome_nonNegative : NonNegative burnOutcome.postState :=
  outcome_postState_nonNegative demoBook_nonNegative burnOutcome

/-- Concrete post-book values, so the witnesses are visibly non-degenerate. -/
theorem transfer_post_values :
    (applyPlan demoBook transferPlan).accountedHoldings zusd = 1000 ∧
    (applyPlan demoBook transferPlan).accountedSupply zusd = 1000 := by
  constructor
  · rfl
  · rfl

theorem issue_post_values :
    (applyPlan demoBook issuePlan).accountedHoldings zusd = 1250 ∧
    (applyPlan demoBook issuePlan).accountedSupply zusd = 1250 := by
  constructor
  · rfl
  · rfl

theorem burn_post_values :
    (applyPlan demoBook burnPlan).accountedHoldings zusd = 930 ∧
    (applyPlan demoBook burnPlan).accountedSupply zusd = 930 := by
  constructor
  · rfl
  · rfl

/-- Composition of the issue and burn witnesses is well-formed. -/
theorem issueThenBurn_wellFormed : PlanWellFormed (seqPlan issuePlan burnPlan) :=
  seqPlan_wellFormed issuePlan_wellFormed burnPlan_wellFormed

theorem issueThenBurn_netIssuance_zusd :
    netIssuance zusd (seqPlan issuePlan burnPlan).journal = 180 := by decide

/-- A two-asset journal: unlike assets are projected separately and never
summed into a single raw total. -/
def mixedAssetJournal : AccountingJournal :=
  [ { kind := .issue, principal := treasury, asset := zusd,
      controlDomain := ledgerDomain, deltaAtoms := 250 },
    { kind := .issue, principal := treasury, asset := zdex,
      controlDomain := ledgerDomain, deltaAtoms := 40 } ]

theorem mixedAsset_netIssuance_zusd :
    netIssuance zusd mixedAssetJournal = 250 := by decide

theorem mixedAsset_netIssuance_zdex :
    netIssuance zdex mixedAssetJournal = 40 := by decide

/-- Neither per-asset projection equals the raw sum of the two deltas. -/
theorem mixedAsset_no_cross_asset_sum :
    netIssuance zusd mixedAssetJournal ≠ 290 ∧
    netIssuance zdex mixedAssetJournal ≠ 290 := by decide

/-! ## 11. Separate issue and burn totals are strictly stronger than the net

A plan that inflates issue and burn by the same amount leaves the derived
holdings and supply deltas unchanged. Pinning only the net would accept it;
pinning each stored total to its own journal projection does not. -/

/-- The `issuePlan` journal with `+1` added to both authorized totals. Its
derived deltas are identical to `issuePlan`'s. -/
def netPreservingSubstitutionPlan : AbstractEffectPlan where
  journal := issueJournal
  authorizedIssue := fun a => if zusd = a then 251 else 1
  authorizedBurn := fun a => if zusd = a then 1 else 1

/-- The substitution is invisible to the derived net deltas. -/
theorem netPreservingSubstitution_same_holdingsDelta (a : Asset) :
    netPreservingSubstitutionPlan.holdingsDelta a = issuePlan.holdingsDelta a := by
  simp only [netPreservingSubstitutionPlan, issuePlan,
    AbstractEffectPlan.holdingsDelta]
  by_cases h : zusd = a
  · rw [if_pos h, if_pos h, if_pos h]
    omega
  · rw [if_neg h, if_neg h, if_neg h]
    omega

theorem netPreservingSubstitution_same_supplyDelta (a : Asset) :
    netPreservingSubstitutionPlan.supplyDelta a = issuePlan.supplyDelta a :=
  netPreservingSubstitution_same_holdingsDelta a

/-- Yet the strengthened well-formedness predicate rejects it, because the
stored issue total no longer equals the journal's issue projection. -/
theorem netPreservingSubstitution_not_wellFormed :
    ¬ PlanWellFormed netPreservingSubstitutionPlan := by
  intro hcontra
  have h := hcontra.issue zusd
  have hstored : netPreservingSubstitutionPlan.authorizedIssue zusd = 251 := rfl
  have hjournal : issuedFor zusd netPreservingSubstitutionPlan.journal = 250 := by
    decide
  rw [hstored, hjournal] at h
  exact absurd h (by decide)

/-- The burn total is wrong too, independently. -/
theorem netPreservingSubstitution_burn_mismatch :
    netPreservingSubstitutionPlan.authorizedBurn zusd
      ≠ burnedFor zusd netPreservingSubstitutionPlan.journal := by
  decide

/-- Consequence: a net-only well-formedness condition would be strictly
weaker, since this plan satisfies it while failing `PlanWellFormed`. -/
theorem netPreservingSubstitution_separates_net_from_wellFormed :
    (∀ a : Asset,
      netPreservingSubstitutionPlan.holdingsDelta a = issuePlan.holdingsDelta a) ∧
    PlanWellFormed issuePlan ∧
    ¬ PlanWellFormed netPreservingSubstitutionPlan :=
  ⟨netPreservingSubstitution_same_holdingsDelta, issuePlan_wellFormed,
    netPreservingSubstitution_not_wellFormed⟩

/-! ## 12. The non-negativity premise is load-bearing

Conservation is preserved unconditionally, but non-negativity is not. This
countermodel is a well-formed plan with well-formed entries applied to a
non-negative book, whose post-book is negative. -/

/-- A book with only 10 atoms of ZUSD, less than `burnPlan` destroys. -/
def thinBook : AssetBook where
  accountedHoldings := fun a => if zusd = a then 10 else 0
  accountedSupply := fun a => if zusd = a then 10 else 0

theorem thinBook_nonNegative : NonNegative thinBook := by
  intro a
  by_cases h : zusd = a
  · subst h
    exact ⟨by decide, by decide⟩
  · simp only [thinBook, if_neg h]
    exact ⟨by decide, by decide⟩

theorem thinBook_holdingsMatchSupply : HoldingsMatchSupply thinBook := by
  intro a
  rfl

/-- Applying `burnPlan` to `thinBook` drives the accounted-holdings column to
`-60`, so the post-book is not non-negative. -/
theorem thinBook_burn_post_not_nonNegative :
    ¬ NonNegative (applyPlan thinBook burnPlan) := by
  intro hcontra
  have h := (hcontra zusd).1
  have hval : (applyPlan thinBook burnPlan).accountedHoldings zusd = -60 := rfl
  rw [hval] at h
  exact absurd h (by decide)

/-- The countermodel: well-formed plan, non-negative pre-book, negative
post-book. Hence non-negativity is preserved only under the explicit admission
premise, and `thinBook` admits no accepted outcome for `burnPlan`. -/
theorem nonNegativity_premise_is_necessary :
    PlanWellFormed burnPlan ∧
    PlanEntriesWellFormed burnPlan ∧
    NonNegative thinBook ∧
    Applies thinBook burnPlan (applyPlan thinBook burnPlan) ∧
    ¬ NonNegative (applyPlan thinBook burnPlan) :=
  ⟨burnPlan_wellFormed, burnPlan_entriesWellFormed, thinBook_nonNegative,
    applyPlan_applies thinBook burnPlan, thinBook_burn_post_not_nonNegative⟩

/-- Conservation still holds in the countermodel: the plan is inadmissible,
not unsound. -/
theorem countermodel_still_conserves :
    HoldingsMatchSupply (applyPlan thinBook burnPlan) :=
  applies_preserves_holdingsMatchSupply
    (applyPlan_applies thinBook burnPlan) thinBook_holdingsMatchSupply

/-- The admission premise genuinely fails here, so no `Accepted thinBook
burnPlan _` proof exists and no accepted `Outcome thinBook` can carry it. -/
theorem thinBook_burn_not_admitted :
    ¬ NonNegativityAdmitted thinBook burnPlan := by
  intro hcontra
  have h := (hcontra zusd).1
  have hval : thinBook.accountedHoldings zusd + burnPlan.holdingsDelta zusd
      = -60 := rfl
  rw [hval] at h
  exact absurd h (by decide)

theorem thinBook_burn_no_accepted_evidence :
    ¬ Accepted thinBook burnPlan (applyPlan thinBook burnPlan) := by
  intro hcontra
  exact thinBook_burn_not_admitted hcontra.nonNegativityAdmitted

/-! ## 13. Journal order is not commutative

The journal records order. Exchanging two plans yields a different journal.
The derived per-asset totals of these two particular plans do coincide, since
integer addition commutes; that is an arithmetic fact about `Int` and is not a
statement about command ordering, lane scheduling, or runtime execution. -/

theorem seqPlan_journal_not_commutative :
    (seqPlan issuePlan burnPlan).journal ≠ (seqPlan burnPlan issuePlan).journal := by
  intro h
  simp only [seqPlan, issuePlan, burnPlan, issueJournal, burnJournal,
    List.cons_append, List.nil_append, List.cons.injEq,
    JournalEntry.mk.injEq] at h
  exact absurd h.1.1 (by decide)

/-! ## 14. Source comparison

Executable comparison output lives in `Proofs.GlobalSettlementCoreV1Challenge`,
which derives every emitted field by evaluating the definitions above rather
than by restating them as literals. That module also binds the intended
signatures of the theorems in this file, so a weakening here fails to compile
there. -/

end GlobalSettlementCoreV1
end Proofs
