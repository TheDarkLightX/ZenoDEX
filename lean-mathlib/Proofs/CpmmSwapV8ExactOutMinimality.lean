import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Basic

/-!
CPMM v8 exact-out minimality (Mathlib-backed).

We certify the core property of the Python kernel `src/kernels/python/cpmm_swap_v8.py`:

Given reserves `(rin, rout)`, desired output `aout < rout`, and fee in bps `fee_bps < 10000`,
the kernel computes:

  net_req    = ceil(rin * aout / (rout - aout))
  gross      = ceil(net_req * 10000 / (10000 - fee_bps))
  fee_total  = ceil(gross * fee_bps / 10000)
  net_actual = gross - fee_total
  out_quote  = floor(rout * net_actual / (rin + net_actual))

and checks `out_quote >= aout`.

This file proves:
- **Sufficiency**: the computed `gross` always satisfies `out_quote >= aout`.
- **Minimality**: any strictly smaller `g < gross` yields `out_quote(g) < aout`.

The proof is integer-only and relies on Mathlib’s `⌈/⌉` (ceilDiv) and `Nat.div` (floor div).
-/

namespace TauSwap
namespace CPMM
namespace V8

-- Helper: strictness property of `ceilDiv`.
lemma mul_lt_of_lt_ceilDiv {b a m : Nat} (ha : 0 < a) (hm : m < b ⌈/⌉ a) : a * m < b := by
  have hnot : ¬ b ≤ a * m := by
    intro hle
    have : b ⌈/⌉ a ≤ m := (ceilDiv_le_iff_le_mul ha).2 hle
    exact (not_le_of_gt hm) this
  exact lt_of_not_ge hnot

-- Fee rounding identity used by the kernel:
-- `gross - ceil(gross*fee/BPS) = floor(gross*(BPS-fee)/BPS)`.
lemma net_actual_eq_floor_mul (gross fee BPS : Nat) (hBPS : 0 < BPS) :
    gross - ((gross * fee) ⌈/⌉ BPS) = (gross * (BPS - fee)) / BPS := by
  set fee_total : Nat := (gross * fee) ⌈/⌉ BPS
  set net : Nat := gross - fee_total
  have hceil_lo : gross * fee ≤ BPS * fee_total := by
    simpa [fee_total] using (le_smul_ceilDiv (a := BPS) (b := gross * fee) hBPS)
  have hceil_hi : BPS * fee_total ≤ gross * fee + (BPS - 1) := by
    have : BPS * ((gross * fee + BPS - 1) / BPS) ≤ gross * fee + BPS - 1 := by
      exact Nat.mul_div_le (gross * fee + BPS - 1) BPS
    have h1 : gross * fee + BPS - 1 = gross * fee + (BPS - 1) := by
      have hle : 1 ≤ BPS := Nat.succ_le_iff.2 hBPS
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.add_sub_assoc hle (gross * fee))
    simpa [fee_total, Nat.ceilDiv_eq_add_pred_div, h1] using this
  have hnet_le : net ≤ (gross * (BPS - fee)) / BPS := by
    have : net * BPS ≤ gross * (BPS - fee) := by
      have hceil_lo' : gross * fee ≤ fee_total * BPS := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hceil_lo
      calc
        net * BPS = (gross - fee_total) * BPS := by simp [net]
        _ = gross * BPS - fee_total * BPS := by simp [Nat.sub_mul]
        _ ≤ gross * BPS - gross * fee := by
          exact Nat.sub_le_sub_left hceil_lo' (gross * BPS)
        _ = gross * (BPS - fee) := by simp [Nat.mul_sub]
    exact (Nat.le_div_iff_mul_le hBPS).2 this
  have hdiv_le : (gross * (BPS - fee)) / BPS ≤ net := by
    have : gross * (BPS - fee) ≤ BPS * net + (BPS - 1) := by
      have hsub : gross * BPS - (gross * fee + (BPS - 1)) ≤ gross * BPS - (BPS * fee_total) := by
        exact Nat.sub_le_sub_left hceil_hi (gross * BPS)
      have hsub' : gross * BPS - gross * fee - (BPS - 1) ≤ gross * BPS - BPS * fee_total := by
        simpa [Nat.sub_add_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsub
      have hsub'' : gross * BPS - gross * fee ≤ (gross * BPS - BPS * fee_total) + (BPS - 1) := by
        exact (Nat.sub_le_iff_le_add).1 hsub'
      simpa [net, Nat.mul_sub, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc] using hsub''
    exact (Nat.div_le_iff_le_mul_add_pred hBPS).2 this
  have : net = (gross * (BPS - fee)) / BPS := by
    exact le_antisymm hnet_le hdiv_le
  simpa [net, fee_total] using this

-- Exact-out condition equivalence:
-- `aout ≤ floor(rout*net/(rin+net))` iff `rin*aout ≤ (rout-aout)*net`.
lemma out_ge_iff {rin rout aout net : Nat} (hrin : 0 < rin) (haout : aout < rout) :
    aout ≤ (rout * net) / (rin + net) ↔ rin * aout ≤ (rout - aout) * net := by
  have hden : 0 < rin + net := Nat.add_pos_left hrin net
  constructor
  · intro h
    have hmul : aout * (rin + net) ≤ rout * net := (Nat.le_div_iff_mul_le hden).1 h
    have hmul' : aout * rin + aout * net ≤ rout * net := by
      simpa [Nat.mul_add] using hmul
    have hsub : aout * rin ≤ rout * net - aout * net := Nat.le_sub_of_add_le hmul'
    have hsub2 : rin * aout ≤ rout * net - aout * net := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsub
    have hrhs : rout * net - aout * net = (rout - aout) * net := by
      simp [Nat.sub_mul]
    simpa [hrhs] using hsub2
  · intro h
    have hrhs : (rout - aout) * net = rout * net - aout * net := by
      simp [Nat.sub_mul]
    have h' : rin * aout ≤ rout * net - aout * net := by
      simpa [hrhs] using h
    have h'' : aout * rin ≤ rout * net - aout * net := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h'
    have hmul' : aout * rin + aout * net ≤ rout * net :=
      Nat.add_le_of_le_sub (Nat.mul_le_mul_right net (Nat.le_of_lt haout)) h''
    have hmul : aout * (rin + net) ≤ rout * net := by
      simpa [Nat.mul_add] using hmul'
    exact (Nat.le_div_iff_mul_le hden).2 hmul

/-- Main theorem: CPMM v8 exact-out computes a sufficient and minimal gross input. -/
theorem swap_exact_out_sufficient_and_minimal
    {rin rout aout fee_bps : Nat}
    (hrin : 0 < rin)
    (haout : aout < rout)
    (hfee : fee_bps < 10000) :
    let BPS : Nat := 10000
    let fee_den : Nat := BPS - fee_bps
    let net_req : Nat := (rin * aout) ⌈/⌉ (rout - aout)
    let gross : Nat := (net_req * BPS) ⌈/⌉ fee_den
    let net_actual : Nat := gross - ((gross * fee_bps) ⌈/⌉ BPS)
    let out_quote : Nat := (rout * net_actual) / (rin + net_actual)
    (aout ≤ out_quote) ∧
      (∀ g : Nat,
        g < gross →
          let na : Nat := g - ((g * fee_bps) ⌈/⌉ BPS)
          (rout * na) / (rin + na) < aout) := by
  intro BPS fee_den net_req gross net_actual out_quote
  have hBPS : 0 < BPS := by
    decide
  have hfee_den : 0 < fee_den := by
    have : fee_bps < BPS := by
      simpa [BPS] using hfee
    exact Nat.sub_pos_of_lt this
  have hden_out : 0 < rout - aout := Nat.sub_pos_of_lt haout

  have hnet_actual : net_actual = (gross * fee_den) / BPS := by
    have : gross - ((gross * fee_bps) ⌈/⌉ BPS) = (gross * (BPS - fee_bps)) / BPS :=
      net_actual_eq_floor_mul gross fee_bps BPS hBPS
    simpa [net_actual, fee_den] using this

  have hnet_req_mul : rin * aout ≤ (rout - aout) * net_req := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (le_smul_ceilDiv (a := rout - aout) (b := rin * aout) hden_out)

  have hgross_mul : net_req * BPS ≤ fee_den * gross := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (le_smul_ceilDiv (a := fee_den) (b := net_req * BPS) hfee_den)

  have hnet_req_le_net_actual : net_req ≤ net_actual := by
    have : net_req ≤ (gross * fee_den) / BPS := by
      have : net_req * BPS ≤ gross * fee_den := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hgross_mul
      exact (Nat.le_div_iff_mul_le hBPS).2 this
    simpa [hnet_actual] using this

  have hsuf_mul : rin * aout ≤ (rout - aout) * net_actual := by
    have hmono : (rout - aout) * net_req ≤ (rout - aout) * net_actual :=
      Nat.mul_le_mul_left (rout - aout) hnet_req_le_net_actual
    exact le_trans hnet_req_mul hmono

  have hsuf : aout ≤ out_quote := by
    have : aout ≤ (rout * net_actual) / (rin + net_actual) :=
      (out_ge_iff (rin := rin) (rout := rout) (aout := aout) (net := net_actual) hrin haout).2 hsuf_mul
    simpa [out_quote] using this

  have hmin :
      ∀ g : Nat,
        g < gross →
          let na : Nat := g - ((g * fee_bps) ⌈/⌉ BPS)
          (rout * na) / (rin + na) < aout := by
    intro g hg
    intro na
    have hna : na = (g * fee_den) / BPS := by
      have : g - ((g * fee_bps) ⌈/⌉ BPS) = (g * (BPS - fee_bps)) / BPS :=
        net_actual_eq_floor_mul g fee_bps BPS hBPS
      simpa [na, fee_den] using this

    have hna_lt : na < net_req := by
      have hmul_lt : fee_den * g < net_req * BPS := by
        have : fee_den * g < net_req * BPS :=
          mul_lt_of_lt_ceilDiv (b := net_req * BPS) (a := fee_den) (m := g) hfee_den (by
            simpa [gross] using hg)
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      have : (g * fee_den) / BPS < net_req := by
        have : g * fee_den < net_req * BPS := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul_lt
        exact (Nat.div_lt_iff_lt_mul hBPS).2 this
      simpa [hna] using this

    have hfail_mul : ¬ rin * aout ≤ (rout - aout) * na := by
      intro hmul
      have hle : net_req ≤ na := by
        have : (rin * aout) ⌈/⌉ (rout - aout) ≤ na :=
          (ceilDiv_le_iff_le_mul hden_out).2 (by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul)
        simpa [net_req] using this
      exact (not_le_of_gt hna_lt) hle

    have hnot_ge : ¬ aout ≤ (rout * na) / (rin + na) := by
      have : aout ≤ (rout * na) / (rin + na) ↔ rin * aout ≤ (rout - aout) * na :=
        out_ge_iff (rin := rin) (rout := rout) (aout := aout) (net := na) hrin haout
      exact (mt this.1) hfail_mul

    exact lt_of_not_ge hnot_ge

  exact ⟨hsuf, hmin⟩

end V8
end CPMM
end TauSwap

