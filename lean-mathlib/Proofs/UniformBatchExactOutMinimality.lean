import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Basic
import Proofs.CpmmSwapV8ExactOutMinimality

/-!
# UPBA v3 exact-out minimal input

This file proves the integer rounding contract used by the UPBA v3 exact-out
certificate verifier.

For a fixed positive uniform price ratio and a fee below 100%, the runtime
computes:

```text
required_net = ceil(amount_out * price_den / price_num)
gross_input  = ceil(required_net * 10000 / (10000 - fee_bps))
```

The theorem `minimalGrossForOut_satisfies_and_minimal` proves that this gross
input is sufficient and minimal for the fixed uniform price. The proof is
integer-only and has no tolerance parameter.
-/

namespace UniformBatchExactOutMinimality

def BPS_DENOM : Nat := 10000

def feeDen (feeBps : Nat) : Nat :=
  BPS_DENOM - feeBps

def uniformOut (netIn priceNum priceDen : Nat) : Nat :=
  (netIn * priceNum) / priceDen

def feeTotal (gross feeBps : Nat) : Nat :=
  (gross * feeBps) ⌈/⌉ BPS_DENOM

def netAfterFee (gross feeBps : Nat) : Nat :=
  gross - feeTotal gross feeBps

def requiredNetForOut (amountOut priceNum priceDen : Nat) : Nat :=
  (amountOut * priceDen) ⌈/⌉ priceNum

def minimalGrossForNet (requiredNet feeBps : Nat) : Nat :=
  (requiredNet * BPS_DENOM) ⌈/⌉ feeDen feeBps

def minimalGrossForOut (amountOut priceNum priceDen feeBps : Nat) : Nat :=
  minimalGrossForNet (requiredNetForOut amountOut priceNum priceDen) feeBps

lemma feeDen_pos {feeBps : Nat} (hFee : feeBps < BPS_DENOM) :
    0 < feeDen feeBps := by
  exact Nat.sub_pos_of_lt hFee

lemma netAfterFee_eq_floor_discount (gross feeBps : Nat) :
    netAfterFee gross feeBps =
      (gross * feeDen feeBps) / BPS_DENOM := by
  have hBPS : 0 < BPS_DENOM := by decide
  have h :=
    TauSwap.CPMM.V8.net_actual_eq_floor_mul
      gross
      feeBps
      BPS_DENOM
      hBPS
  simpa [netAfterFee, feeTotal, feeDen, BPS_DENOM] using h

theorem requiredNetForOut_satisfies
    {amountOut priceNum priceDen : Nat}
    (hPriceNum : 0 < priceNum)
    (hPriceDen : 0 < priceDen) :
    amountOut <=
      uniformOut
        (requiredNetForOut amountOut priceNum priceDen)
        priceNum
        priceDen := by
  have hMul :
      amountOut * priceDen <=
        priceNum * requiredNetForOut amountOut priceNum priceDen := by
    simpa [requiredNetForOut] using
      (le_smul_ceilDiv
        (a := priceNum)
        (b := amountOut * priceDen)
        hPriceNum)
  have hMul' :
      amountOut * priceDen <=
        requiredNetForOut amountOut priceNum priceDen * priceNum := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hMul
  exact
    (Nat.le_div_iff_mul_le hPriceDen).2
      (by simpa [uniformOut] using hMul')

theorem requiredNetForOut_minimal
    {amountOut priceNum priceDen netIn : Nat}
    (hPriceNum : 0 < priceNum)
    (hPriceDen : 0 < priceDen)
    (hOut : amountOut <= uniformOut netIn priceNum priceDen) :
    requiredNetForOut amountOut priceNum priceDen <= netIn := by
  have hMul :
      amountOut * priceDen <= netIn * priceNum := by
    exact
      (Nat.le_div_iff_mul_le hPriceDen).1
        (by simpa [uniformOut] using hOut)
  have hMul' :
      amountOut * priceDen <= priceNum * netIn := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hMul
  simpa [requiredNetForOut] using
    (ceilDiv_le_iff_le_mul hPriceNum).2 hMul'

theorem requiredNetForOut_iff
    {amountOut priceNum priceDen netIn : Nat}
    (hPriceNum : 0 < priceNum)
    (hPriceDen : 0 < priceDen) :
    amountOut <= uniformOut netIn priceNum priceDen <->
      requiredNetForOut amountOut priceNum priceDen <= netIn := by
  constructor
  · exact requiredNetForOut_minimal hPriceNum hPriceDen
  · intro hNet
    have hSatisfies :=
      requiredNetForOut_satisfies
        (amountOut := amountOut)
        (priceNum := priceNum)
        (priceDen := priceDen)
        hPriceNum
        hPriceDen
    have hMono :
        uniformOut
            (requiredNetForOut amountOut priceNum priceDen)
            priceNum
            priceDen <=
          uniformOut netIn priceNum priceDen := by
      unfold uniformOut
      exact Nat.div_le_div_right (Nat.mul_le_mul_right priceNum hNet)
    exact le_trans hSatisfies hMono

theorem minimalGrossForNet_satisfies
    {requiredNet feeBps : Nat}
    (hFee : feeBps < BPS_DENOM) :
    requiredNet <=
      netAfterFee (minimalGrossForNet requiredNet feeBps) feeBps := by
  have hBPS : 0 < BPS_DENOM := by decide
  have hFeeDen : 0 < feeDen feeBps := feeDen_pos hFee
  have hGrossMul :
      requiredNet * BPS_DENOM <=
        feeDen feeBps * minimalGrossForNet requiredNet feeBps := by
    simpa [minimalGrossForNet] using
      (le_smul_ceilDiv
        (a := feeDen feeBps)
        (b := requiredNet * BPS_DENOM)
        hFeeDen)
  have hGrossMul' :
      requiredNet * BPS_DENOM <=
        minimalGrossForNet requiredNet feeBps * feeDen feeBps := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hGrossMul
  have hFloor :
      requiredNet <=
        (minimalGrossForNet requiredNet feeBps * feeDen feeBps) / BPS_DENOM := by
    exact (Nat.le_div_iff_mul_le hBPS).2 hGrossMul'
  simpa [netAfterFee_eq_floor_discount] using hFloor

theorem minimalGrossForNet_minimal
    {requiredNet feeBps gross : Nat}
    (hFee : feeBps < BPS_DENOM)
    (hNet : requiredNet <= netAfterFee gross feeBps) :
    minimalGrossForNet requiredNet feeBps <= gross := by
  have hBPS : 0 < BPS_DENOM := by decide
  have hFeeDen : 0 < feeDen feeBps := feeDen_pos hFee
  have hFloor :
      requiredNet <= (gross * feeDen feeBps) / BPS_DENOM := by
    simpa [netAfterFee_eq_floor_discount] using hNet
  have hMul :
      requiredNet * BPS_DENOM <= gross * feeDen feeBps := by
    exact (Nat.le_div_iff_mul_le hBPS).1 hFloor
  have hMul' :
      requiredNet * BPS_DENOM <= feeDen feeBps * gross := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hMul
  simpa [minimalGrossForNet] using
    (ceilDiv_le_iff_le_mul hFeeDen).2 hMul'

theorem minimalGrossForNet_iff
    {requiredNet feeBps gross : Nat}
    (hFee : feeBps < BPS_DENOM) :
    minimalGrossForNet requiredNet feeBps <= gross <->
      requiredNet <= netAfterFee gross feeBps := by
  constructor
  · intro hGross
    have hSatisfies :=
      minimalGrossForNet_satisfies
        (requiredNet := requiredNet)
        (feeBps := feeBps)
        hFee
    have hFeeMono : feeDen feeBps <= feeDen feeBps := le_rfl
    have hNetMono :
        netAfterFee (minimalGrossForNet requiredNet feeBps) feeBps <=
          netAfterFee gross feeBps := by
      rw [netAfterFee_eq_floor_discount, netAfterFee_eq_floor_discount]
      exact Nat.div_le_div_right (Nat.mul_le_mul_right (feeDen feeBps) hGross)
    exact le_trans hSatisfies hNetMono
  · exact minimalGrossForNet_minimal hFee

theorem minimalGrossForOut_satisfies
    {amountOut priceNum priceDen feeBps : Nat}
    (hPriceNum : 0 < priceNum)
    (hPriceDen : 0 < priceDen)
    (hFee : feeBps < BPS_DENOM) :
    amountOut <=
      uniformOut
        (netAfterFee
          (minimalGrossForOut amountOut priceNum priceDen feeBps)
          feeBps)
        priceNum
        priceDen := by
  have hRequiredSatisfies :=
    requiredNetForOut_satisfies
      (amountOut := amountOut)
      (priceNum := priceNum)
      (priceDen := priceDen)
      hPriceNum
      hPriceDen
  have hNet :
      requiredNetForOut amountOut priceNum priceDen <=
        netAfterFee
          (minimalGrossForOut amountOut priceNum priceDen feeBps)
          feeBps := by
    simpa [minimalGrossForOut] using
      minimalGrossForNet_satisfies
        (requiredNet := requiredNetForOut amountOut priceNum priceDen)
        (feeBps := feeBps)
        hFee
  have hMono :
      uniformOut
          (requiredNetForOut amountOut priceNum priceDen)
          priceNum
          priceDen <=
        uniformOut
          (netAfterFee
            (minimalGrossForOut amountOut priceNum priceDen feeBps)
            feeBps)
          priceNum
          priceDen := by
    unfold uniformOut
    exact Nat.div_le_div_right (Nat.mul_le_mul_right priceNum hNet)
  exact le_trans hRequiredSatisfies hMono

theorem minimalGrossForOut_minimal
    {amountOut priceNum priceDen feeBps gross : Nat}
    (hPriceNum : 0 < priceNum)
    (hPriceDen : 0 < priceDen)
    (hFee : feeBps < BPS_DENOM)
    (hOut :
      amountOut <=
        uniformOut (netAfterFee gross feeBps) priceNum priceDen) :
    minimalGrossForOut amountOut priceNum priceDen feeBps <= gross := by
  have hRequiredNet :
      requiredNetForOut amountOut priceNum priceDen <= netAfterFee gross feeBps :=
    requiredNetForOut_minimal hPriceNum hPriceDen hOut
  simpa [minimalGrossForOut] using
    minimalGrossForNet_minimal
      (requiredNet := requiredNetForOut amountOut priceNum priceDen)
      (feeBps := feeBps)
      (gross := gross)
      hFee
      hRequiredNet

theorem minimalGrossForOut_iff
    {amountOut priceNum priceDen feeBps gross : Nat}
    (hPriceNum : 0 < priceNum)
    (hPriceDen : 0 < priceDen)
    (hFee : feeBps < BPS_DENOM) :
    minimalGrossForOut amountOut priceNum priceDen feeBps <= gross <->
      amountOut <=
        uniformOut (netAfterFee gross feeBps) priceNum priceDen := by
  constructor
  · intro hGross
    have hRequiredNet :
        requiredNetForOut amountOut priceNum priceDen <=
          netAfterFee gross feeBps := by
      have hGrossNet :=
        (minimalGrossForNet_iff
          (requiredNet := requiredNetForOut amountOut priceNum priceDen)
          (feeBps := feeBps)
          (gross := gross)
          hFee).1
      exact hGrossNet (by simpa [minimalGrossForOut] using hGross)
    exact
      (requiredNetForOut_iff
        (amountOut := amountOut)
        (priceNum := priceNum)
        (priceDen := priceDen)
        (netIn := netAfterFee gross feeBps)
        hPriceNum
        hPriceDen).2 hRequiredNet
  · exact minimalGrossForOut_minimal hPriceNum hPriceDen hFee

theorem minimalGrossForOut_satisfies_and_minimal
    {amountOut priceNum priceDen feeBps : Nat}
    (hPriceNum : 0 < priceNum)
    (hPriceDen : 0 < priceDen)
    (hFee : feeBps < BPS_DENOM) :
    let gross := minimalGrossForOut amountOut priceNum priceDen feeBps
    amountOut <= uniformOut (netAfterFee gross feeBps) priceNum priceDen ∧
      ∀ candidateGross,
        amountOut <=
            uniformOut
              (netAfterFee candidateGross feeBps)
              priceNum
              priceDen ->
          gross <= candidateGross := by
  intro gross
  constructor
  · simpa [gross] using
      minimalGrossForOut_satisfies
        (amountOut := amountOut)
        (priceNum := priceNum)
        (priceDen := priceDen)
        (feeBps := feeBps)
        hPriceNum
        hPriceDen
        hFee
  · intro candidateGross hCandidate
    simpa [gross] using
      minimalGrossForOut_minimal
        (amountOut := amountOut)
        (priceNum := priceNum)
        (priceDen := priceDen)
        (feeBps := feeBps)
        (gross := candidateGross)
        hPriceNum
        hPriceDen
        hFee
        hCandidate

end UniformBatchExactOutMinimality
