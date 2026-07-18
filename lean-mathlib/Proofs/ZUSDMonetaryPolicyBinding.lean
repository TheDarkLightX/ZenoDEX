import Mathlib.Tactic

/-!
# Committed zUSD monetary policy binding

This module formalizes the equality kernel used to bind runtime configuration
to the policy committed in zUSD monetary state.  A decision is matched exactly
when all ten authority/economic fields agree.  A mismatch decision carries a
nonempty, duplicate-free list drawn from the canonical field order.

The model proves the pure comparison contract.  Runtime parsing, canonical
hex validation, state serialization, signature binding, and atomic shell commit
remain separate refinement obligations.
-/

namespace ZenoDEX.ZUSDMonetaryPolicyBinding

structure Policy where
  chainId : Nat
  canonicalZUSDAsset : Nat
  oraclePubkey : Option Nat
  liquidationGasCompFixedCollateralE8 : Nat
  liquidationGasCompBps : Nat
  borrowFeeFloorBps : Nat
  borrowFeeMaxBps : Nat
  hostProtocolFeeShareBps : Nat
  feeStakeAssetId : Option Nat
  stakingActivationDelayEpochs : Nat
  deriving DecidableEq, Repr

inductive Field where
  | chainId
  | canonicalZUSDAsset
  | oraclePubkey
  | liquidationGasCompFixedCollateralE8
  | liquidationGasCompBps
  | borrowFeeFloorBps
  | borrowFeeMaxBps
  | hostProtocolFeeShareBps
  | feeStakeAssetId
  | stakingActivationDelayEpochs
  deriving DecidableEq, Repr

def allFields : List Field :=
  [
    .chainId,
    .canonicalZUSDAsset,
    .oraclePubkey,
    .liquidationGasCompFixedCollateralE8,
    .liquidationGasCompBps,
    .borrowFeeFloorBps,
    .borrowFeeMaxBps,
    .hostProtocolFeeShareBps,
    .feeStakeAssetId,
    .stakingActivationDelayEpochs
  ]

def Field.differs (committed configured : Policy) : Field → Bool
  | .chainId => committed.chainId != configured.chainId
  | .canonicalZUSDAsset =>
      committed.canonicalZUSDAsset != configured.canonicalZUSDAsset
  | .oraclePubkey => committed.oraclePubkey != configured.oraclePubkey
  | .liquidationGasCompFixedCollateralE8 =>
      committed.liquidationGasCompFixedCollateralE8 !=
        configured.liquidationGasCompFixedCollateralE8
  | .liquidationGasCompBps =>
      committed.liquidationGasCompBps != configured.liquidationGasCompBps
  | .borrowFeeFloorBps =>
      committed.borrowFeeFloorBps != configured.borrowFeeFloorBps
  | .borrowFeeMaxBps =>
      committed.borrowFeeMaxBps != configured.borrowFeeMaxBps
  | .hostProtocolFeeShareBps =>
      committed.hostProtocolFeeShareBps != configured.hostProtocolFeeShareBps
  | .feeStakeAssetId => committed.feeStakeAssetId != configured.feeStakeAssetId
  | .stakingActivationDelayEpochs =>
      committed.stakingActivationDelayEpochs !=
        configured.stakingActivationDelayEpochs

def mismatches (committed configured : Policy) : List Field :=
  allFields.filter (Field.differs committed configured)

inductive Decision where
  | matched
  | mismatch (fields : {xs : List Field // xs ≠ []})
  deriving Repr

def decide (committed configured : Policy) : Decision :=
  if h : mismatches committed configured = [] then
    .matched
  else
    .mismatch ⟨mismatches committed configured, h⟩

def Decision.isMatched : Decision → Bool
  | .matched => true
  | .mismatch _ => false

theorem mismatches_eq_nil_iff (committed configured : Policy) :
    mismatches committed configured = [] ↔ committed = configured := by
  constructor
  · intro h
    simp [mismatches, allFields, Field.differs] at h
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    cases committed
    cases configured
    simp_all
  · intro h
    subst configured
    simp [mismatches, allFields, Field.differs]

theorem decide_is_matched_iff (committed configured : Policy) :
    (decide committed configured).isMatched = true ↔ committed = configured := by
  rw [← mismatches_eq_nil_iff]
  by_cases h : mismatches committed configured = []
  · simp [decide, h, Decision.isMatched]
  · simp [decide, h, Decision.isMatched]

theorem decide_self_is_matched (policy : Policy) :
    (decide policy policy).isMatched = true := by
  simp [decide_is_matched_iff]

theorem mismatch_fields_are_canonical
    (committed configured : Policy)
    (field : Field)
    (h : field ∈ mismatches committed configured) :
    field ∈ allFields := by
  exact (List.mem_filter.mp h).1

theorem mismatches_preserve_canonical_order
    (committed configured : Policy) :
    List.Sublist (mismatches committed configured) allFields := by
  exact List.filter_sublist

theorem mismatches_nodup (committed configured : Policy) :
    (mismatches committed configured).Nodup := by
  apply List.Nodup.filter
  simp [allFields]

def Field.toNat : Field → Nat
  | .chainId => 0
  | .canonicalZUSDAsset => 1
  | .oraclePubkey => 2
  | .liquidationGasCompFixedCollateralE8 => 3
  | .liquidationGasCompBps => 4
  | .borrowFeeFloorBps => 5
  | .borrowFeeMaxBps => 6
  | .hostProtocolFeeShareBps => 7
  | .feeStakeAssetId => 8
  | .stakingActivationDelayEpochs => 9

def basePolicy : Policy :=
  {
    chainId := 0
    canonicalZUSDAsset := 0
    oraclePubkey := none
    liquidationGasCompFixedCollateralE8 := 0
    liquidationGasCompBps := 0
    borrowFeeFloorBps := 0
    borrowFeeMaxBps := 0
    hostProtocolFeeShareBps := 0
    feeStakeAssetId := none
    stakingActivationDelayEpochs := 0
  }

/- These named one-field projections bind each semantic policy field to the
canonical mismatch constructor.  They prevent an implementation and its
numeric diagnostic encoding from drifting together while retaining a vacuous
exhaustive mask result. -/
theorem chain_id_only_projection :
    mismatches basePolicy { basePolicy with chainId := 1 } = [.chainId] := by
  decide

theorem canonical_zusd_asset_only_projection :
    mismatches basePolicy { basePolicy with canonicalZUSDAsset := 1 } =
      [.canonicalZUSDAsset] := by
  decide

theorem oracle_pubkey_only_projection :
    mismatches basePolicy { basePolicy with oraclePubkey := some 1 } =
      [.oraclePubkey] := by
  decide

theorem liquidation_gas_comp_fixed_only_projection :
    mismatches basePolicy
        { basePolicy with liquidationGasCompFixedCollateralE8 := 1 } =
      [.liquidationGasCompFixedCollateralE8] := by
  decide

theorem liquidation_gas_comp_bps_only_projection :
    mismatches basePolicy { basePolicy with liquidationGasCompBps := 1 } =
      [.liquidationGasCompBps] := by
  decide

theorem borrow_fee_floor_only_projection :
    mismatches basePolicy { basePolicy with borrowFeeFloorBps := 1 } =
      [.borrowFeeFloorBps] := by
  decide

theorem borrow_fee_max_only_projection :
    mismatches basePolicy { basePolicy with borrowFeeMaxBps := 1 } =
      [.borrowFeeMaxBps] := by
  decide

theorem host_protocol_fee_share_only_projection :
    mismatches basePolicy { basePolicy with hostProtocolFeeShareBps := 1 } =
      [.hostProtocolFeeShareBps] := by
  decide

theorem fee_stake_asset_only_projection :
    mismatches basePolicy { basePolicy with feeStakeAssetId := some 1 } =
      [.feeStakeAssetId] := by
  decide

theorem staking_activation_delay_only_projection :
    mismatches basePolicy { basePolicy with stakingActivationDelayEpochs := 1 } =
      [.stakingActivationDelayEpochs] := by
  decide

def policyForMask (mask : Nat) : Policy :=
  {
    chainId := if mask.testBit 0 then 1 else 0
    canonicalZUSDAsset := if mask.testBit 1 then 1 else 0
    oraclePubkey := if mask.testBit 2 then some 1 else none
    liquidationGasCompFixedCollateralE8 := if mask.testBit 3 then 1 else 0
    liquidationGasCompBps := if mask.testBit 4 then 1 else 0
    borrowFeeFloorBps := if mask.testBit 5 then 1 else 0
    borrowFeeMaxBps := if mask.testBit 6 then 1 else 0
    hostProtocolFeeShareBps := if mask.testBit 7 then 1 else 0
    feeStakeAssetId := if mask.testBit 8 then some 1 else none
    stakingActivationDelayEpochs := if mask.testBit 9 then 1 else 0
  }

def mismatchMask (committed configured : Policy) : Nat :=
  (mismatches committed configured).foldl
    (fun mask field => mask + 2 ^ field.toNat)
    0

def exhaustiveMismatchMasks : List Nat :=
  (List.range 1024).map (fun mask => mismatchMask basePolicy (policyForMask mask))

def exhaustiveMismatchMaskCSV : String :=
  String.intercalate "," (exhaustiveMismatchMasks.map toString)

end ZenoDEX.ZUSDMonetaryPolicyBinding
