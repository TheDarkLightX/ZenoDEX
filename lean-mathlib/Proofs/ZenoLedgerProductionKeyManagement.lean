/-!
ZenoLedger production key-management admission boundary.

This proof file models the abstract safety contract for privileged production
actions. It does not prove cryptographic signature soundness, hardware wallet
correctness, social independence, or legal custody. It proves the local
admission shape: admitted production actions imply role authorization, threshold
quorum, distinct custodian quorum, non-revoked/non-expired signers, required
hardware backing, required timelock, break-glass scope, production key
separation, and a transparency receipt.
-/

namespace Proofs.ZenoLedgerProductionKeyManagement

structure ProductionKeyAdmission where
  productionEnvironment : Bool
  roleAuthorized : Bool
  quorumMet : Bool
  thresholdAtLeastTwoForCritical : Bool
  distinctCustodiansMet : Bool
  noRevokedSigner : Bool
  noExpiredSigner : Bool
  hardwareBackedIfRequired : Bool
  timelockSatisfiedIfRequired : Bool
  breakGlassScopeOk : Bool
  productionKeysOnly : Bool
  transparencyReceiptBound : Bool
deriving DecidableEq, Repr

def Safe (a : ProductionKeyAdmission) : Prop :=
  a.productionEnvironment = true ∧
  a.roleAuthorized = true ∧
  a.quorumMet = true ∧
  a.thresholdAtLeastTwoForCritical = true ∧
  a.distinctCustodiansMet = true ∧
  a.noRevokedSigner = true ∧
  a.noExpiredSigner = true ∧
  a.hardwareBackedIfRequired = true ∧
  a.timelockSatisfiedIfRequired = true ∧
  a.breakGlassScopeOk = true ∧
  a.productionKeysOnly = true ∧
  a.transparencyReceiptBound = true

def Admitted (a : ProductionKeyAdmission) : Prop :=
  Safe a

def NoSingleKeyAuthority (a : ProductionKeyAdmission) : Prop :=
  a.thresholdAtLeastTwoForCritical = true ∧
  a.distinctCustodiansMet = true

inductive ProductionRole where
  | treasury
  | config
  | validator
  | verifier
  | oracle
  | release
  | emergency
deriving DecidableEq, Repr

inductive ProductionAction where
  | protocolTreasurySpend
  | daoTreasuryGrant
  | publicNetworkConfigUpdate
  | validatorSetUpdate
  | verifierRegistryUpdate
  | oracleReporterRegistryUpdate
  | releaseArtifactPublish
  | emergencyPause
  | emergencyUnpause
deriving DecidableEq, Repr

def RequiredRole : ProductionAction → ProductionRole
  | ProductionAction.protocolTreasurySpend => ProductionRole.treasury
  | ProductionAction.daoTreasuryGrant => ProductionRole.treasury
  | ProductionAction.publicNetworkConfigUpdate => ProductionRole.config
  | ProductionAction.validatorSetUpdate => ProductionRole.validator
  | ProductionAction.verifierRegistryUpdate => ProductionRole.verifier
  | ProductionAction.oracleReporterRegistryUpdate => ProductionRole.oracle
  | ProductionAction.releaseArtifactPublish => ProductionRole.release
  | ProductionAction.emergencyPause => ProductionRole.emergency
  | ProductionAction.emergencyUnpause => ProductionRole.config

def RoleAuthorizes (role : ProductionRole) (action : ProductionAction) : Prop :=
  role = RequiredRole action

def RequiresTimelock : ProductionAction → Prop
  | ProductionAction.protocolTreasurySpend => True
  | ProductionAction.daoTreasuryGrant => True
  | ProductionAction.publicNetworkConfigUpdate => True
  | ProductionAction.validatorSetUpdate => True
  | ProductionAction.verifierRegistryUpdate => True
  | ProductionAction.oracleReporterRegistryUpdate => True
  | ProductionAction.releaseArtifactPublish => False
  | ProductionAction.emergencyPause => False
  | ProductionAction.emergencyUnpause => True

theorem admitted_safe
    (a : ProductionKeyAdmission)
    (hadmit : Admitted a) :
    Safe a := by
  exact hadmit

theorem admitted_quorum_met
    (a : ProductionKeyAdmission)
    (hadmit : Admitted a) :
    a.quorumMet = true := by
  rcases admitted_safe a hadmit with
    ⟨_, _, hquorum, _, _, _, _, _, _, _, _, _⟩
  exact hquorum

theorem admitted_no_single_key_authority
    (a : ProductionKeyAdmission)
    (hadmit : Admitted a) :
    NoSingleKeyAuthority a := by
  rcases admitted_safe a hadmit with
    ⟨_, _, _, hthreshold, hdistinct, _, _, _, _, _, _, _⟩
  exact ⟨hthreshold, hdistinct⟩

theorem admitted_no_revoked_signer
    (a : ProductionKeyAdmission)
    (hadmit : Admitted a) :
    a.noRevokedSigner = true := by
  rcases admitted_safe a hadmit with
    ⟨_, _, _, _, _, hrevoked, _, _, _, _, _, _⟩
  exact hrevoked

theorem admitted_no_expired_signer
    (a : ProductionKeyAdmission)
    (hadmit : Admitted a) :
    a.noExpiredSigner = true := by
  rcases admitted_safe a hadmit with
    ⟨_, _, _, _, _, _, hexpired, _, _, _, _, _⟩
  exact hexpired

theorem admitted_production_keys_only
    (a : ProductionKeyAdmission)
    (hadmit : Admitted a) :
    a.productionKeysOnly = true := by
  rcases admitted_safe a hadmit with
    ⟨_, _, _, _, _, _, _, _, _, _, hprodKeys, _⟩
  exact hprodKeys

theorem admitted_transparency_receipt_bound
    (a : ProductionKeyAdmission)
    (hadmit : Admitted a) :
    a.transparencyReceiptBound = true := by
  rcases admitted_safe a hadmit with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hreceipt⟩
  exact hreceipt

theorem rejects_non_production_environment
    (a : ProductionKeyAdmission)
    (hnonprod : a.productionEnvironment = false) :
    ¬ Admitted a := by
  intro hadmit
  rcases admitted_safe a hadmit with
    ⟨hprod, _, _, _, _, _, _, _, _, _, _, _⟩
  rw [hnonprod] at hprod
  cases hprod

theorem rejects_missing_quorum
    (a : ProductionKeyAdmission)
    (hquorumMissing : a.quorumMet = false) :
    ¬ Admitted a := by
  intro hadmit
  have hquorum := admitted_quorum_met a hadmit
  rw [hquorumMissing] at hquorum
  cases hquorum

theorem rejects_single_key_authority
    (a : ProductionKeyAdmission)
    (hsingle : a.thresholdAtLeastTwoForCritical = false) :
    ¬ Admitted a := by
  intro hadmit
  have hnosingle := admitted_no_single_key_authority a hadmit
  have hthreshold := hnosingle.1
  rw [hsingle] at hthreshold
  cases hthreshold

theorem rejects_same_custodian_quorum
    (a : ProductionKeyAdmission)
    (hsameCustodian : a.distinctCustodiansMet = false) :
    ¬ Admitted a := by
  intro hadmit
  have hnosingle := admitted_no_single_key_authority a hadmit
  have hdistinct := hnosingle.2
  rw [hsameCustodian] at hdistinct
  cases hdistinct

theorem rejects_revoked_signer
    (a : ProductionKeyAdmission)
    (hrevoked : a.noRevokedSigner = false) :
    ¬ Admitted a := by
  intro hadmit
  have hnoRevoked := admitted_no_revoked_signer a hadmit
  rw [hrevoked] at hnoRevoked
  cases hnoRevoked

theorem rejects_expired_signer
    (a : ProductionKeyAdmission)
    (hexpired : a.noExpiredSigner = false) :
    ¬ Admitted a := by
  intro hadmit
  have hnoExpired := admitted_no_expired_signer a hadmit
  rw [hexpired] at hnoExpired
  cases hnoExpired

theorem rejects_software_key_when_hardware_required
    (a : ProductionKeyAdmission)
    (hhardware : a.hardwareBackedIfRequired = false) :
    ¬ Admitted a := by
  intro hadmit
  rcases admitted_safe a hadmit with
    ⟨_, _, _, _, _, _, _, hhardwareOk, _, _, _, _⟩
  rw [hhardware] at hhardwareOk
  cases hhardwareOk

theorem rejects_missing_timelock_when_required
    (a : ProductionKeyAdmission)
    (htimelock : a.timelockSatisfiedIfRequired = false) :
    ¬ Admitted a := by
  intro hadmit
  rcases admitted_safe a hadmit with
    ⟨_, _, _, _, _, _, _, _, htimelockOk, _, _, _⟩
  rw [htimelock] at htimelockOk
  cases htimelockOk

theorem rejects_break_glass_scope_violation
    (a : ProductionKeyAdmission)
    (hscope : a.breakGlassScopeOk = false) :
    ¬ Admitted a := by
  intro hadmit
  rcases admitted_safe a hadmit with
    ⟨_, _, _, _, _, _, _, _, _, hscopeOk, _, _⟩
  rw [hscope] at hscopeOk
  cases hscopeOk

theorem rejects_testnet_key_for_production
    (a : ProductionKeyAdmission)
    (htestnet : a.productionKeysOnly = false) :
    ¬ Admitted a := by
  intro hadmit
  have hprodKeys := admitted_production_keys_only a hadmit
  rw [htestnet] at hprodKeys
  cases hprodKeys

theorem rejects_missing_transparency_receipt
    (a : ProductionKeyAdmission)
    (hreceipt : a.transparencyReceiptBound = false) :
    ¬ Admitted a := by
  intro hadmit
  have hbound := admitted_transparency_receipt_bound a hadmit
  rw [hreceipt] at hbound
  cases hbound

theorem admits_safe_production_key_action
    (a : ProductionKeyAdmission)
    (hprod : a.productionEnvironment = true)
    (hrole : a.roleAuthorized = true)
    (hquorum : a.quorumMet = true)
    (hthreshold : a.thresholdAtLeastTwoForCritical = true)
    (hdistinct : a.distinctCustodiansMet = true)
    (hrevoked : a.noRevokedSigner = true)
    (hexpired : a.noExpiredSigner = true)
    (hhardware : a.hardwareBackedIfRequired = true)
    (htimelock : a.timelockSatisfiedIfRequired = true)
    (hscope : a.breakGlassScopeOk = true)
    (hprodKeys : a.productionKeysOnly = true)
    (hreceipt : a.transparencyReceiptBound = true) :
    Admitted a := by
  unfold Admitted Safe
  exact ⟨
    hprod,
    hrole,
    hquorum,
    hthreshold,
    hdistinct,
    hrevoked,
    hexpired,
    hhardware,
    htimelock,
    hscope,
    hprodKeys,
    hreceipt
  ⟩

theorem treasury_spend_admitted_no_single_key
    (a : ProductionKeyAdmission)
    (_hrole : RoleAuthorizes ProductionRole.treasury ProductionAction.protocolTreasurySpend)
    (hadmit : Admitted a) :
    NoSingleKeyAuthority a := by
  exact admitted_no_single_key_authority a hadmit

theorem config_update_admitted_requires_timelock
    (a : ProductionKeyAdmission)
    (_htimelockedAction : RequiresTimelock ProductionAction.publicNetworkConfigUpdate)
    (hadmit : Admitted a) :
    a.timelockSatisfiedIfRequired = true := by
  rcases admitted_safe a hadmit with
    ⟨_, _, _, _, _, _, _, _, htimelock, _, _, _⟩
  exact htimelock

theorem emergency_pause_admitted_does_not_authorize_unpause
    (_hpause : RoleAuthorizes ProductionRole.emergency ProductionAction.emergencyPause) :
    ¬ RoleAuthorizes ProductionRole.emergency ProductionAction.emergencyUnpause := by
  intro hunpause
  unfold RoleAuthorizes RequiredRole at hunpause
  cases hunpause

theorem revoked_key_cannot_be_counted
    (a : ProductionKeyAdmission)
    (hrevoked : a.noRevokedSigner = false) :
    ¬ Admitted a := by
  exact rejects_revoked_signer a hrevoked

theorem production_action_excludes_testnet_key
    (a : ProductionKeyAdmission)
    (htestnet : a.productionKeysOnly = false) :
    ¬ Admitted a := by
  exact rejects_testnet_key_for_production a htestnet

end Proofs.ZenoLedgerProductionKeyManagement
