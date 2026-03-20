/-!
# ZenoDEX Settlement Price History Certificate

This file formalizes the deterministic shell around the settlement price-history
packet embedded in replay-bound settlement certificates.

It proves:

- the packet is a deterministic rebuild from the `(price_pp, price_prev,
  price_curr)` tuple,
- verifier success is equivalent to equality with the canonical rebuilt packet,
- the verifying packet is unique for a fixed price trace.

As with the other shell proofs in this repo, the packet hash is modeled as a
deterministic input rather than concrete JSON or SHA256 behavior.
-/

namespace TauSwap
namespace Settlement
namespace PriceHistoryCertificate

structure Inputs where
  pricePP : Nat
  pricePrev : Nat
  priceCurr : Nat
  priceTraceHash : Nat
deriving DecidableEq, Repr

structure Certificate where
  pricePP : Nat
  pricePrev : Nat
  priceCurr : Nat
  priceTraceHash : Nat
deriving DecidableEq, Repr

def buildCertificate (inputs : Inputs) : Certificate :=
  {
    pricePP := inputs.pricePP
    pricePrev := inputs.pricePrev
    priceCurr := inputs.priceCurr
    priceTraceHash := inputs.priceTraceHash
  }

def verifyCertificate (inputs : Inputs) (certificate : Certificate) : Prop :=
  certificate = buildCertificate inputs

theorem verifyCertificate_iff
    (inputs : Inputs)
    (certificate : Certificate) :
    verifyCertificate inputs certificate ↔
      certificate = buildCertificate inputs := by
  rfl

theorem verifyCertificate_of_build
    (inputs : Inputs) :
    verifyCertificate inputs (buildCertificate inputs) := by
  rfl

theorem verifyingCertificate_unique
    (inputs : Inputs)
    {certificate : Certificate}
    (hVerify : verifyCertificate inputs certificate) :
    certificate = buildCertificate inputs := by
  exact hVerify

end PriceHistoryCertificate
end Settlement
end TauSwap
