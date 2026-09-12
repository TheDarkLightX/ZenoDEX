import Std

/-!
# Current perps margin account transition

This model follows `perps_margin_module_v1.py` and `perps_margin.rs`, including
ordered policy/account/oracle guards and quote-e8 (not base-e8) maintenance.
The input view selects one account and the account count from a decoded market.
Selection, complete-state reconstruction, canonical hashing and authentication
are refinement obligations, not assumptions of cryptographic authority here.
The runtime differential gate compares complete Python/Rust outputs separately.
-/

namespace ZenoDEX.PerpsMarginTransitionV1

def maxAtoms : Nat := 2 ^ 128 - 1
def maxDelta : Nat := 2 ^ 127 - 1
def maxNonce : Nat := 2 ^ 64 - 1

inductive Kind where
  | deposit | withdraw | close | unknown
  deriving DecidableEq, Repr

inductive MarketStatus where
  | active | drainOnly | halted
  deriving DecidableEq, Repr

inductive Reject where
  | releaseMismatch | unknownCommand | haltedMarket | marketDrainOnly
  | marketMismatch | assetMismatch | unauthorizedSubject | unexpectedOracleAuthority
  | accountMissing | accountLimit | accountOwnerMismatch | accountClosed
  | nonceOverflow | nonceMismatch | oracleAuthorityMissing | oraclePriceMismatch
  | invalidCloseAmount | positionOpen | collateralRemains | zeroAmount
  | effectDeltaOverflow | balanceOverflow | insufficientCollateral
  | arithmeticOverflow | maintenanceBreach
  deriving DecidableEq, Repr

structure Account where
  id : String
  owner : String
  position : Int
  entryPrice : Nat
  collateral : Nat
  nonce : Nat
  closed : Bool
  deriving DecidableEq, Repr

structure Command where
  kind : Kind
  accountId : String
  market : String
  owner : String
  asset : String
  amount : Nat
  nonce : Nat
  deriving DecidableEq, Repr

structure Market where
  release : String
  id : String
  asset : String
  price : Nat
  maintenanceBps : Nat
  depegBps : Nat
  status : MarketStatus
  accountCount : Nat
  deriving DecidableEq, Repr

structure Context where
  release : String
  subject : String
  hasOracle : Bool
  oraclePrice : Nat
  deriving DecidableEq, Repr

def commonReject (ctx : Context) (m : Market) (c : Command) : Option Reject :=
  if ctx.release != m.release then some .releaseMismatch
  else if c.kind == .unknown then some .unknownCommand
  else if m.status == .halted then some .haltedMarket
  else if m.status == .drainOnly && c.kind == .deposit then some .marketDrainOnly
  else if c.market != m.id then some .marketMismatch
  else if c.asset != m.asset then some .assetMismatch
  else if c.owner != ctx.subject then some .unauthorizedSubject
  else if c.kind != .withdraw && ctx.hasOracle then some .unexpectedOracleAuthority
  else none

def prepareAccount (m : Market) (c : Command) (pre : Option Account) : Except Reject Account :=
  if pre.isNone && c.kind != .deposit then .error .accountMissing
  else if pre.isNone && m.accountCount >= 64 then .error .accountLimit
  else
    let a := pre.getD ⟨c.accountId, c.owner, 0, 0, 0, 0, false⟩
    if a.owner != c.owner then .error .accountOwnerMismatch
    else if a.closed then .error .accountClosed
    else if a.nonce == maxNonce then .error .nonceOverflow
    else if c.nonce != a.nonce + 1 then .error .nonceMismatch
    else .ok a

def oracleReject (ctx : Context) (m : Market) (c : Command) (a : Account) : Option Reject :=
  if c.kind != .withdraw then none
  else if a.position == 0 then
    if ctx.hasOracle then some .unexpectedOracleAuthority else none
  else if !ctx.hasOracle then some .oracleAuthorityMissing
  else if ctx.oraclePrice != m.price then some .oraclePriceMismatch
  else none

/-- Quotient and remainder avoid the overflowing `n + 9999` idiom. -/
def ceilQuote (n : Nat) : Nat :=
  n / 10000 + if n % 10000 == 0 then 0 else 1

def maintenance (m : Market) (a : Account) : Nat :=
  ceilQuote (a.position.natAbs * m.price * (m.maintenanceBps + m.depegBps))

/-- This is the least integer quote amount covering the exact raw numerator. -/
theorem ceilQuote_exact (n : Nat) :
    n ≤ 10000 * ceilQuote n ∧ 10000 * ceilQuote n < n + 10000 := by
  have hdiv := Nat.div_add_mod n 10000
  have hmod := Nat.mod_lt n (by decide : 0 < 10000)
  unfold ceilQuote
  split <;> simp_all <;> omega

theorem ceilQuote_minimal (n k : Nat) (h : n ≤ 10000 * k) : ceilQuote n ≤ k := by
  have := (ceilQuote_exact n).2
  omega

def postAccount (m : Market) (c : Command) (a : Account) : Except Reject Account :=
  if c.kind = .close then
    if c.amount != 0 then .error .invalidCloseAmount
    else if a.position != 0 then .error .positionOpen
    else if a.collateral != 0 then .error .collateralRemains
    else .ok { a with nonce := c.nonce, closed := true }
  else if c.amount == 0 then .error .zeroAmount
  else if c.amount > maxDelta then .error .effectDeltaOverflow
  else if c.kind = .deposit then
    if a.collateral + c.amount > maxAtoms then .error .balanceOverflow
    else .ok { a with collateral := a.collateral + c.amount, nonce := c.nonce }
  else if c.amount > a.collateral then .error .insufficientCollateral
  else if a.position.natAbs * m.price * (m.maintenanceBps + m.depegBps) > maxAtoms then
    .error .arithmeticOverflow
  else if a.position != 0 && a.collateral - c.amount < maintenance m a then
    .error .maintenanceBreach
  else .ok { a with collateral := a.collateral - c.amount, nonce := c.nonce }

def step (ctx : Context) (m : Market) (c : Command) (pre : Option Account) : Except Reject Account :=
  match commonReject ctx m c with
  | some code => .error code
  | none => match prepareAccount m c pre with
    | .error code => .error code
    | .ok a => match oracleReject ctx m c a with
      | some code => .error code
      | none => postAccount m c a

/-- A rejected attempt retains the selected account, including its nonce. -/
def advance (ctx : Context) (m : Market) (c : Command) (pre : Option Account) : Option Account :=
  match step ctx m c pre with
  | .error _ => pre
  | .ok a => some a

/-- The outer market lookup must supply the account targeted by this command. -/
def Selected (c : Command) (pre : Option Account) : Prop :=
  ∀ a, pre = some a → a.id = c.accountId

def accountDelta (c : Command) : Int :=
  match c.kind with
  | .close => 0
  | .deposit => -(Int.ofNat c.amount)
  | _ => Int.ofNat c.amount

def custodyDelta (c : Command) : Int := -accountDelta c
def liabilityDelta (c : Command) : Int := custodyDelta c

theorem rejected_is_exact_noop (ctx m c pre code) (h : step ctx m c pre = .error code) :
    advance ctx m c pre = pre := by simp [advance, h]

theorem physical_effect_conservation (c : Command) : accountDelta c + custodyDelta c = 0 := by
  simp only [custodyDelta]; omega

theorem liability_tracks_custody (c : Command) : liabilityDelta c = custodyDelta c := rfl

theorem prepared_account_owner_and_nonce (m c pre a)
    (h : prepareAccount m c pre = .ok a) :
    a.owner = c.owner ∧ a.closed = false ∧ a.nonce ≠ maxNonce ∧ c.nonce = a.nonce + 1 := by
  unfold prepareAccount at h
  repeat' (split at h <;> try simp_all)

theorem post_preserves_identity_and_position (m c a b)
    (h : postAccount m c a = .ok b) :
    b.id = a.id ∧ b.owner = a.owner ∧ b.position = a.position ∧
    b.entryPrice = a.entryPrice ∧ b.nonce = c.nonce := by
  unfold postAccount at h
  repeat' (split at h <;> try simp_all)
  all_goals cases h; simp_all

theorem close_is_flat_empty_terminal (m c a b) (hc : c.kind = .close)
    (h : postAccount m c a = .ok b) :
    b.closed = true ∧ b.position = 0 ∧ b.collateral = 0 ∧ c.amount = 0 := by
  simp only [postAccount, hc] at h
  repeat' (split at h <;> try simp_all)
  all_goals cases h; simp_all

theorem deposit_exact (m c a b) (hc : c.kind = .deposit)
    (h : postAccount m c a = .ok b) :
    b.collateral = a.collateral + c.amount ∧ b.collateral ≤ maxAtoms ∧
    0 < c.amount ∧ c.amount ≤ maxDelta := by
  simp only [postAccount, hc] at h
  repeat' (split at h <;> try simp_all)
  all_goals cases h; simp_all
  omega

theorem withdraw_exact_and_covered (m c a b) (hc : c.kind = .withdraw)
    (h : postAccount m c a = .ok b) :
    b.collateral + c.amount = a.collateral ∧ 0 < c.amount ∧ c.amount ≤ maxDelta ∧
    (a.position ≠ 0 → maintenance m a ≤ b.collateral) := by
  simp only [postAccount, hc] at h
  repeat' (split at h <;> try simp_all)
  all_goals cases h; simp_all
  omega

theorem accepted_exposes_guards (ctx m c pre b) (h : step ctx m c pre = .ok b) :
    commonReject ctx m c = none ∧ ∃ a, prepareAccount m c pre = .ok a ∧
    oracleReject ctx m c a = none ∧ postAccount m c a = .ok b := by
  unfold step at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all

theorem accepted_subject_owns_account (ctx m c pre b) (h : step ctx m c pre = .ok b) :
    b.owner = c.owner ∧ c.owner = ctx.subject := by
  obtain ⟨hp, a, ha, _, hb⟩ := accepted_exposes_guards ctx m c pre b h
  have ho := (prepared_account_owner_and_nonce m c pre a ha).1
  have hi := (post_preserves_identity_and_position m c a b hb).2.1
  have hs : c.owner = ctx.subject := by
    unfold commonReject at hp
    repeat' (split at hp <;> try simp_all)
  exact ⟨hi.trans ho, hs⟩

theorem closed_cannot_accept (ctx m c a b) (hc : a.closed = true) :
    step ctx m c (some a) ≠ .ok b := by
  intro h
  obtain ⟨_, p, hp, _, _⟩ := accepted_exposes_guards ctx m c (some a) b h
  simp [prepareAccount, hc] at hp
  split at hp <;> simp_all

theorem closed_is_absorbing (ctx m c a) (hc : a.closed = true) :
    advance ctx m c (some a) = some a := by
  unfold advance
  split
  · rfl
  · rename_i b h
    exact False.elim (closed_cannot_accept ctx m c a b hc h)

def run (inputs : List (Context × Market × Command)) (pre : Option Account) : Option Account :=
  inputs.foldl (fun a (ctx, m, c) => advance ctx m c a) pre

theorem fixed_account_closed_history_is_absorbing (inputs : List (Context × Market × Command))
    (a : Account) (hc : a.closed = true)
    (ht : ∀ x ∈ inputs, x.2.2.accountId = a.id) : run inputs (some a) = some a := by
  induction inputs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨ctx, m, c⟩
    have htail : ∀ x ∈ xs, x.2.2.accountId = a.id := by
      intro x hx
      exact ht x (List.mem_cons_of_mem _ hx)
    simpa [run, List.foldl_cons, closed_is_absorbing ctx m c a hc] using ih htail

theorem accepted_close_is_exact_tombstone (ctx m c a b)
    (hselected : Selected c (some a)) (hkind : c.kind = .close)
    (h : step ctx m c (some a) = .ok b) :
    a.closed = false ∧ a.position = 0 ∧ a.collateral = 0 ∧ c.amount = 0 ∧
    c.nonce = a.nonce + 1 ∧ b = { a with nonce := c.nonce, closed := true } ∧
    a.id = c.accountId ∧ b.owner = ctx.subject := by
  obtain ⟨_, p, hp, _, hb⟩ := accepted_exposes_guards ctx m c (some a) b h
  have heq : p = a := by
    simp only [prepareAccount] at hp
    repeat' (split at hp <;> try simp_all)
  subst p
  have guards := prepared_account_owner_and_nonce m c (some a) a hp
  have owner := accepted_subject_owns_account ctx m c (some a) b h
  have id := hselected a rfl
  simp only [postAccount, hkind] at hb
  repeat' (split at hb <;> try simp_all)

/-- Subject-selected commands for a flat-account drain; no new protocol command. -/
def drainCommand (m : Market) (a : Account) : Command :=
  ⟨.withdraw, a.id, m.id, a.owner, m.asset, a.collateral, a.nonce + 1⟩

def closeCommand (m : Market) (a : Account) : Command :=
  ⟨.close, a.id, m.id, a.owner, m.asset, 0, a.nonce + 2⟩

/-- A subject-matching flat account can drain and close without an Oracle in either
active or drain-only mode. The amount and two remaining nonce slots are explicit
resource premises; this is not whole-market or position closeout. -/
theorem flat_account_can_drain_and_close (ctx : Context) (m : Market) (a : Account)
    (hr : ctx.release = m.release) (hs : ctx.subject = a.owner)
    (hm : m.status ≠ .halted) (ho : ctx.hasOracle = false)
    (hc : a.closed = false) (hp : a.position = 0)
    (ha : 0 < a.collateral) (hb : a.collateral ≤ maxDelta)
    (hn : a.nonce + 2 ≤ maxNonce) :
    run [(ctx, m, drainCommand m a), (ctx, m, closeCommand m a)] (some a) =
      some { a with collateral := 0, nonce := a.nonce + 2, closed := true } := by
  have hn0 : a.nonce ≠ maxNonce := by omega
  have hn1 : a.nonce + 1 ≠ maxNonce := by omega
  have hdelta : ¬ maxDelta < a.collateral := by omega
  simp [run, advance, step, commonReject, prepareAccount, oracleReject, postAccount,
    drainCommand, closeCommand, maintenance, ceilQuote, hr, hs, hm, ho, hc, hp,
    Nat.ne_of_gt ha, hdelta, hn0, hn1, maxAtoms]

end ZenoDEX.PerpsMarginTransitionV1
