import Std

/-!
# Current perps margin account transition

This model follows `perps_margin_module_v1.py` and `perps_margin.rs`, including
ordered policy/account/oracle guards and quote-e8 (not base-e8) maintenance.
The complete-market layer derives the selected account and count from its owned
list and preserves structural/numeric admission. Runtime correspondence is
checked on a finite corpus; canonical hashing and authentication remain separate
refinement obligations. This model confers no cryptographic authority.
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

/-! Complete market materialization. Counts and selected accounts are derived
from the owned list. String syntax, canonical bytes and authentication remain
separate decoding/refinement obligations. -/

structure MarketState where
  release : String
  id : String
  asset : String
  price : Nat
  maintenanceBps : Nat
  depegBps : Nat
  maxPosition : Nat
  status : MarketStatus
  accounts : List Account
  deriving DecidableEq, Repr

def MarketState.view (s : MarketState) : Market :=
  ⟨s.release, s.id, s.asset, s.price, s.maintenanceBps, s.depegBps,
    s.status, s.accounts.length⟩

def lookupAccount (id : String) (accounts : List Account) : Option Account :=
  accounts.find? (fun a => a.id == id)

/-- Ordered upsert represents the runtimes' unique-key map replacement. -/
def putAccount (a : Account) : List Account → List Account
  | [] => [a]
  | x :: xs =>
    if a.id = x.id then a :: xs
    else if a.id < x.id then a :: x :: xs
    else x :: putAccount a xs

def OrderedAccounts (accounts : List Account) : Prop :=
  accounts.Pairwise (fun a b => a.id < b.id)

def stepMarket (ctx : Context) (s : MarketState) (c : Command) : Except Reject MarketState :=
  match step ctx s.view c (lookupAccount c.accountId s.accounts) with
  | .error code => .error code
  | .ok a => .ok { s with accounts := putAccount a s.accounts }

def advanceMarket (ctx : Context) (s : MarketState) (c : Command) : MarketState :=
  match stepMarket ctx s c with
  | .error _ => s
  | .ok post => post

theorem lookup_selected (id accounts a) (h : lookupAccount id accounts = some a) :
    a ∈ accounts ∧ a.id = id := by
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem lookup_none (id accounts) :
    lookupAccount id accounts = none ↔ ∀ a ∈ accounts, a.id ≠ id := by
  simp [lookupAccount]

theorem mem_put (a x : Account) (accounts : List Account) :
    x ∈ putAccount a accounts → x = a ∨ x ∈ accounts := by
  induction accounts with
  | nil => simp [putAccount]
  | cons b bs ih =>
    simp only [putAccount]
    split
    · simp only [List.mem_cons]; grind
    · split
      · simp only [List.mem_cons]; grind
      · simp only [List.mem_cons]; grind

theorem lookup_put_self (a : Account) (accounts : List Account) :
    lookupAccount a.id (putAccount a accounts) = some a := by
  induction accounts with
  | nil => simp [putAccount, lookupAccount]
  | cons b bs ih =>
    simp only [putAccount]
    split
    · simp [lookupAccount]
    · rename_i hne
      split
      · simp [lookupAccount]
      · simpa [lookupAccount, Ne.symm hne] using ih

theorem lookup_put_other (a : Account) (accounts : List Account) (id : String)
    (hne : id ≠ a.id) :
    lookupAccount id (putAccount a accounts) = lookupAccount id accounts := by
  induction accounts with
  | nil => simp [putAccount, lookupAccount, Ne.symm hne]
  | cons b bs ih =>
    simp only [putAccount]
    split
    · rename_i heq
      simp [lookupAccount, Ne.symm hne, ← heq]
    · split
      · simp [lookupAccount, Ne.symm hne]
      · simp only [lookupAccount, List.find?_cons] at *
        rw [ih]

theorem put_ordered (a : Account) (accounts : List Account)
    (h : OrderedAccounts accounts) : OrderedAccounts (putAccount a accounts) := by
  induction accounts with
  | nil => simp [putAccount, OrderedAccounts]
  | cons b bs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    simp only [putAccount]
    split
    · rename_i heq
      exact List.pairwise_cons.mpr ⟨by simpa [heq] using hhead, htail⟩
    · rename_i hne
      split
      · rename_i hlt
        apply List.pairwise_cons.mpr
        exact ⟨by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hlt
          · exact String.lt_trans hlt (hhead x hx), h⟩
      · rename_i hnlt
        have hba : b.id < a.id := by
          apply String.not_le.mp
          intro hab
          exact hne (String.le_antisymm hab (String.not_lt.mp hnlt))
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih htail⟩
        intro x hx
        rcases mem_put a x bs hx with rfl | hx
        · exact hba
        · exact hhead x hx

theorem lookup_before_head (a b : Account) (bs : List Account)
    (h : OrderedAccounts (b :: bs)) (hlt : a.id < b.id) :
    lookupAccount a.id (b :: bs) = none := by
  apply (lookup_none _ _).mpr
  intro x hx heq
  have hax : a.id < x.id := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hlt
    · exact String.lt_trans hlt ((List.pairwise_cons.mp h).1 x hx)
  exact String.lt_irrefl a.id (heq ▸ hax)

theorem put_length (a : Account) (accounts : List Account)
    (h : OrderedAccounts accounts) :
    (putAccount a accounts).length = accounts.length +
      if (lookupAccount a.id accounts).isNone then 1 else 0 := by
  induction accounts with
  | nil => simp [putAccount, lookupAccount]
  | cons b bs ih =>
    simp only [putAccount]
    split
    · rename_i heq
      simp [lookupAccount, ← heq]
    · rename_i hne
      split
      · rename_i hlt
        simp [lookup_before_head a b bs h hlt]
      · have hi := ih (List.pairwise_cons.mp h).2
        simp [lookupAccount, Ne.symm hne] at hi ⊢
        omega

/-- Existing contributions are replaced exactly; a new flat account adds zero. -/
theorem put_weight (weight : Account → Nat) (a : Account) (accounts : List Account)
    (h : OrderedAccounts accounts)
    (hw : weight a = ((lookupAccount a.id accounts).map weight).getD 0) :
    ((putAccount a accounts).map weight).sum = (accounts.map weight).sum := by
  induction accounts with
  | nil => simpa [lookupAccount, putAccount] using hw
  | cons b bs ih =>
    simp only [putAccount]
    split
    · rename_i heq
      simp [lookupAccount, ← heq] at hw
      simp [hw]
    · rename_i hne
      split
      · rename_i hlt
        rw [lookup_before_head a b bs h hlt] at hw
        simpa using hw
      · have hi := ih (List.pairwise_cons.mp h).2 (by
          simpa [lookupAccount, Ne.symm hne] using hw)
        simp [hi]

structure AccountAdmitted (price maxPosition : Nat) (a : Account) : Prop where
  positionLower : -(Int.ofNat (maxDelta + 1)) ≤ a.position
  positionUpper : a.position ≤ Int.ofNat maxDelta
  positionBound : a.position.natAbs ≤ maxPosition
  entryBound : a.entryPrice ≤ maxAtoms
  collateralBound : a.collateral ≤ maxAtoms
  nonceBound : a.nonce ≤ maxNonce
  flatEntry : a.position = 0 ↔ a.entryPrice = 0
  entryIndex : a.position ≠ 0 → a.entryPrice = price
  closedEmpty : a.closed = true → a.position = 0 ∧ a.collateral = 0

def positiveGross (accounts : List Account) : Nat :=
  (accounts.map (fun a => a.position.toNat)).sum

def negativeGross (accounts : List Account) : Nat :=
  (accounts.map (fun a => (-a.position).toNat)).sum

/-- Structural/numeric runtime admission. Token/root syntax and decoding are
outside this predicate; no stronger initial solvency rule is invented here. -/
structure MarketAdmitted (s : MarketState) : Prop where
  ordered : OrderedAccounts s.accounts
  count : s.accounts.length ≤ 64
  pricePositive : 0 < s.price
  priceBound : s.price ≤ maxAtoms
  maintenancePositive : 0 < s.maintenanceBps
  riskBound : s.maintenanceBps + s.depegBps ≤ 10000
  maxPositionPositive : 0 < s.maxPosition
  maxPositionBound : s.maxPosition ≤ maxAtoms
  envelope : s.maxPosition * s.price * (s.maintenanceBps + s.depegBps) ≤ maxAtoms
  accountsValid : ∀ a ∈ s.accounts, AccountAdmitted s.price s.maxPosition a
  positiveBound : positiveGross s.accounts ≤ maxAtoms
  negativeBound : negativeGross s.accounts ≤ maxAtoms
  balanced : positiveGross s.accounts = negativeGross s.accounts

theorem prepared_exact (m c pre a) (h : prepareAccount m c pre = .ok a) :
    a = pre.getD ⟨c.accountId, c.owner, 0, 0, 0, 0, false⟩ := by
  unfold prepareAccount at h
  repeat' (split at h <;> try simp_all)

theorem prepared_missing_room (m c a) (h : prepareAccount m c none = .ok a) :
    m.accountCount < 64 := by
  unfold prepareAccount at h
  repeat' (split at h <;> try simp_all)

theorem prepared_admitted (s : MarketState) (c : Command) (a : Account)
    (hs : MarketAdmitted s)
    (h : prepareAccount s.view c (lookupAccount c.accountId s.accounts) = .ok a) :
    AccountAdmitted s.price s.maxPosition a := by
  have heq := prepared_exact _ _ _ _ h
  cases hl : lookupAccount c.accountId s.accounts with
  | some pre =>
    simp [hl] at heq
    subst a
    exact hs.accountsValid pre (lookup_selected _ _ _ hl).1
  | none =>
    simp [hl] at heq
    subst a
    constructor <;> simp [maxDelta, maxAtoms, maxNonce]

theorem post_account_admitted (s : MarketState) (c : Command) (a b : Account)
    (ha : AccountAdmitted s.price s.maxPosition a) (ho : a.closed = false)
    (hn : c.nonce ≤ maxNonce)
    (h : postAccount s.view c a = .ok b) : AccountAdmitted s.price s.maxPosition b := by
  rcases ha with ⟨hlo, hhi, habs, he, hc, _, hf, hi, hclosed⟩
  unfold postAccount at h
  repeat' (split at h <;> try simp_all)
  all_goals cases h; constructor <;> simp_all
  all_goals omega

theorem accepted_account_facts (ctx : Context) (s : MarketState) (c : Command) (b : Account)
    (h : step ctx s.view c (lookupAccount c.accountId s.accounts) = .ok b) :
    b.id = c.accountId ∧
    b.position = ((lookupAccount c.accountId s.accounts).map Account.position).getD 0 ∧
    ((lookupAccount c.accountId s.accounts).isNone = true → s.accounts.length < 64) := by
  obtain ⟨_, a, hp, _, hb⟩ := accepted_exposes_guards _ _ _ _ _ h
  have hi := post_preserves_identity_and_position _ _ _ _ hb
  have he := prepared_exact _ _ _ _ hp
  cases hl : lookupAccount c.accountId s.accounts with
  | none =>
    simp [hl] at he
    subst a
    have hroom := prepared_missing_room _ _ _ (hl ▸ hp)
    simpa [MarketState.view] using And.intro hi.1 (And.intro hi.2.2.1 hroom)
  | some pre =>
    have hid := (lookup_selected _ _ _ hl).2
    simp [hl] at he
    subst a
    simp [hi.1, hid, hi.2.2.1]

theorem accepted_account_admitted (ctx s c b) (hs : MarketAdmitted s)
    (h : step ctx s.view c (lookupAccount c.accountId s.accounts) = .ok b) :
    AccountAdmitted s.price s.maxPosition b := by
  obtain ⟨_, a, hp, _, hb⟩ := accepted_exposes_guards _ _ _ _ _ h
  have ha := prepared_admitted s c a hs hp
  have hg := prepared_account_owner_and_nonce _ _ _ _ hp
  have hn : c.nonce ≤ maxNonce := by have := ha.nonceBound; omega
  exact post_account_admitted s c a b ha hg.2.1 hn hb

theorem accepted_market_materialization (ctx s c post) (h : stepMarket ctx s c = .ok post) :
    ∃ a, step ctx s.view c (lookupAccount c.accountId s.accounts) = .ok a ∧
      post = { s with accounts := putAccount a s.accounts } := by
  unfold stepMarket at h
  split at h <;> simp_all

/-- Every sibling is observed by its own key, including accounts absent before. -/
theorem accepted_market_lookup_frame (ctx s c post) (h : stepMarket ctx s c = .ok post) :
    ∃ a, lookupAccount c.accountId post.accounts = some a ∧ a.owner = ctx.subject ∧
      ∀ id, id ≠ c.accountId → lookupAccount id post.accounts = lookupAccount id s.accounts := by
  obtain ⟨a, ha, rfl⟩ := accepted_market_materialization _ _ _ _ h
  have hf := accepted_account_facts _ _ _ _ ha
  have ho := accepted_subject_owns_account _ _ _ _ _ ha
  refine ⟨a, ?_, ho.1.trans ho.2, ?_⟩
  · simpa [← hf.1] using lookup_put_self a s.accounts
  · intro id hne
    exact lookup_put_other a s.accounts id (by simpa [hf.1] using hne)

theorem accepted_market_gross (ctx s c post) (hs : MarketAdmitted s)
    (h : stepMarket ctx s c = .ok post) :
    positiveGross post.accounts = positiveGross s.accounts ∧
    negativeGross post.accounts = negativeGross s.accounts := by
  obtain ⟨a, ha, rfl⟩ := accepted_market_materialization _ _ _ _ h
  obtain ⟨hid, hp, _⟩ := accepted_account_facts _ _ _ _ ha
  constructor
  · apply put_weight _ _ _ hs.ordered
    cases hl : lookupAccount c.accountId s.accounts <;> simp_all
  · apply put_weight _ _ _ hs.ordered
    cases hl : lookupAccount c.accountId s.accounts <;> simp_all

theorem accepted_market_admitted (ctx s c post) (hs : MarketAdmitted s)
    (h : stepMarket ctx s c = .ok post) : MarketAdmitted post := by
  have hg := accepted_market_gross ctx s c post hs h
  obtain ⟨a, ha, rfl⟩ := accepted_market_materialization _ _ _ _ h
  have hf := accepted_account_facts _ _ _ _ ha
  have hva := accepted_account_admitted _ _ _ _ hs ha
  have hlen := put_length a s.accounts hs.ordered
  have hn : (putAccount a s.accounts).length ≤ 64 := by
    rw [hf.1] at hlen
    cases he : (lookupAccount c.accountId s.accounts).isNone with
    | false =>
      simp only [he, Bool.false_eq_true, if_false, Nat.add_zero] at hlen
      simpa only [hlen] using hs.count
    | true =>
      have hr := hf.2.2 he
      simp only [he, if_true] at hlen
      omega
  exact ⟨put_ordered a s.accounts hs.ordered, hn, hs.pricePositive, hs.priceBound,
    hs.maintenancePositive, hs.riskBound, hs.maxPositionPositive, hs.maxPositionBound,
    hs.envelope, by
      intro x hx
      rcases mem_put a x s.accounts hx with rfl | hx
      · exact hva
      · exact hs.accountsValid x hx,
    hg.1 ▸ hs.positiveBound, hg.2 ▸ hs.negativeBound, by simpa [hg.1, hg.2] using hs.balanced⟩

theorem rejected_market_exact (ctx s c code) (h : stepMarket ctx s c = .error code) :
    advanceMarket ctx s c = s := by simp [advanceMarket, h]

def runMarket (inputs : List (Context × Command)) (s : MarketState) : MarketState :=
  inputs.foldl (fun pre (ctx, c) => advanceMarket ctx pre c) s

theorem market_history_admitted (inputs : List (Context × Command)) (s : MarketState)
    (hs : MarketAdmitted s) : MarketAdmitted (runMarket inputs s) := by
  induction inputs generalizing s with
  | nil => exact hs
  | cons input rest ih =>
    rcases input with ⟨ctx, c⟩
    change MarketAdmitted (runMarket rest (advanceMarket ctx s c))
    apply ih
    unfold advanceMarket
    split
    · exact hs
    · exact accepted_market_admitted _ _ _ _ hs (by assumption)

/-- The constructor's maximum-position envelope covers every admitted account,
so the multiplication cannot overflow a u128 in the withdrawal calculation. -/
theorem admitted_maintenance_numerator (s : MarketState) (a : Account)
    (hs : MarketAdmitted s) (ha : a ∈ s.accounts) :
    a.position.natAbs * s.price * (s.maintenanceBps + s.depegBps) ≤ maxAtoms := by
  have hp := (hs.accountsValid a ha).positionBound
  exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right s.price hp)) hs.envelope

theorem closed_account_survives_market_step (ctx : Context) (s : MarketState) (c : Command)
    (a : Account) (hl : lookupAccount a.id s.accounts = some a) (hc : a.closed = true) :
    lookupAccount a.id (advanceMarket ctx s c).accounts = some a := by
  cases h : stepMarket ctx s c with
  | error code => simp [advanceMarket, h, hl]
  | ok post =>
    simp only [advanceMarket, h]
    by_cases hid : c.accountId = a.id
    · obtain ⟨b, hb, _⟩ := accepted_market_materialization _ _ _ _ h
      have hbad : step ctx s.view c (some a) = .ok b := by simpa only [hid, hl] using hb
      exact False.elim (closed_cannot_accept ctx s.view c a b hc hbad)
    · obtain ⟨_, _, _, hf⟩ := accepted_market_lookup_frame _ _ _ _ h
      exact (hf a.id (Ne.symm hid)).trans hl

/-- A closed account survives arbitrary subsequent market commands, even those
targeting other accounts. No caller-selected-account premise remains. -/
theorem market_closed_history_is_absorbing (inputs : List (Context × Command))
    (s : MarketState) (a : Account) (hl : lookupAccount a.id s.accounts = some a)
    (hc : a.closed = true) : lookupAccount a.id (runMarket inputs s).accounts = some a := by
  induction inputs generalizing s with
  | nil => exact hl
  | cons input rest ih =>
    rcases input with ⟨ctx, c⟩
    exact ih (advanceMarket ctx s c) (closed_account_survives_market_step ctx s c a hl hc)

end ZenoDEX.PerpsMarginTransitionV1
