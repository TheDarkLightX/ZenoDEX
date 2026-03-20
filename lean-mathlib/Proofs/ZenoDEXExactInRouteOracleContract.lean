import Proofs.ZenoDEXExactInRouteCertificate

/-!
# ZenoDEX Exact-In Route Oracle Contract

This file formalizes the deterministic shell around the pool-snapshot-bound
exact-in oracle contract used by the integration boundary.

It proves:

- the oracle contract is a deterministic rebuild from
  `(candidate stream, binding bit, runtime choice, route metadata)`,
- verifier success is equivalent to equality with the canonical rebuilt
  contract,
- the `runtimeMatchesCanonical` bit is exactly the statement that the runtime
  choice equals the canonical winner,
- the verifying contract is unique for fixed inputs.

This proof does **not** claim end-to-end equivalence between the Python
route-key projection and the abstract ranked candidate model. It only proves
the shell around the exact-in oracle contract that packages that ranked
certificate together with the runtime winner.
-/

namespace TauSwap
namespace Routing
namespace ExactInRouteOracleContract

open ExactInRouteCertificate

structure Inputs where
  amountIn : Nat
  enableMixedDirectTwoHopSplit : Bool
  first : Candidate
  rest : List Candidate
  bindingOk : Bool
  runtimeChoice : Candidate
deriving DecidableEq, Repr

def canonicalWinner (inputs : Inputs) : Candidate :=
  let certificate := buildCertificate inputs.first inputs.rest inputs.bindingOk
  {
    candidateIndex := certificate.winnerIndex
    routeKeyRank := certificate.winnerKey
  }

structure Contract where
  amountIn : Nat
  enableMixedDirectTwoHopSplit : Bool
  runtimeChoice : Candidate
  canonicalWinner : Candidate
  runtimeMatchesCanonical : Bool
  candidateCount : Nat
  certificate : Certificate
deriving DecidableEq, Repr

def buildContract (inputs : Inputs) : Contract :=
  let certificate := buildCertificate inputs.first inputs.rest inputs.bindingOk
  let winner : Candidate :=
    {
      candidateIndex := certificate.winnerIndex
      routeKeyRank := certificate.winnerKey
    }
  {
    amountIn := inputs.amountIn
    enableMixedDirectTwoHopSplit := inputs.enableMixedDirectTwoHopSplit
    runtimeChoice := inputs.runtimeChoice
    canonicalWinner := winner
    runtimeMatchesCanonical := decide (inputs.runtimeChoice = winner)
    candidateCount := inputs.rest.length + 1
    certificate := certificate
  }

def verifyContract (inputs : Inputs) (contract : Contract) : Prop :=
  contract = buildContract inputs

theorem verifyContract_iff
    (inputs : Inputs)
    (contract : Contract) :
    verifyContract inputs contract ↔
      contract = buildContract inputs := by
  rfl

theorem verifyContract_of_build
    (inputs : Inputs) :
    verifyContract inputs (buildContract inputs) := by
  rfl

theorem verifyingContract_unique
    (inputs : Inputs)
    {contract : Contract}
    (hVerify : verifyContract inputs contract) :
    contract = buildContract inputs := by
  exact hVerify

theorem canonicalWinner_eq
    (inputs : Inputs) :
    (buildContract inputs).canonicalWinner = canonicalWinner inputs := by
  simp [buildContract, canonicalWinner]

theorem runtimeMatchesCanonical_iff
    (inputs : Inputs) :
    (buildContract inputs).runtimeMatchesCanonical = true ↔
      inputs.runtimeChoice = canonicalWinner inputs := by
  simp [buildContract, canonicalWinner]

theorem runtimeMismatch_iff
    (inputs : Inputs) :
    (buildContract inputs).runtimeMatchesCanonical = false ↔
      inputs.runtimeChoice ≠ canonicalWinner inputs := by
  simp [buildContract, canonicalWinner]

theorem candidateCount_eq
    (inputs : Inputs) :
    (buildContract inputs).candidateCount = inputs.rest.length + 1 := by
  simp [buildContract]

theorem certificate_eq_route_certificate_build
    (inputs : Inputs) :
    (buildContract inputs).certificate =
      buildCertificate inputs.first inputs.rest inputs.bindingOk := by
  simp [buildContract]

end ExactInRouteOracleContract
end Routing
end TauSwap
