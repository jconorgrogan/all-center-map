import PrincipalZetaHuxley1972CorrectedTerminalSource
import APRegularNearAppendixBAdapter

/-!
# The corrected Huxley zero-free branch from the primitive high gap

The full Appendix-B corollary was previously passed twice to the live
endpoint: once to terminate the regular-near mesh and once to supply the
conductor-one Huxley alternative.  The latter is already a consequence of
the former.  High ordinates use `PrimitiveRegularHighGap`; the fixed
`|gamma| < 3` range uses the certified compact principal gap.
-/

namespace MAPPrincipalZetaHuxley1972ZeroFreeFromHighGap

open Filter Set DirichletZeros
open MAPAPRegularNearAppendixBAdapter
open MAPAPPrimitiveRegularLowGap
open MAPPrincipalZetaHuxley1972CorrectedTerminalSource

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

theorem correctedEquation610ZeroFree_of_primitiveRegularHighGap
    (hHighGap : PrimitiveRegularHighGap) :
    Huxley1972CorrectedEquation610ZeroFree := by
  obtain ⟨cHigh, hcHigh, hHighEventually⟩ :=
    hHighGap 1 (by norm_num)
  obtain ⟨cLow, hcLow, hLow⟩ :=
    exists_primitive_principal_regular_low_gap
  let c : ℝ := min cHigh cLow
  have hc : 0 < c := lt_min hcHigh hcLow
  have hLowDecay := eventually_weakGap_le_constant cLow c hcLow hc
  have hTrade := eventually_correctedThreshold_lt_weakVKScale hc
  have hLog : ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
    have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
    rw [Real.le_log_iff_exp_le hTpos]
    exact hT
  obtain ⟨Thigh, hHigh⟩ := Filter.eventually_atTop.1 hHighEventually
  obtain ⟨Tlow, hLowDecay'⟩ := Filter.eventually_atTop.1 hLowDecay
  obtain ⟨Ttrade, hTrade'⟩ := Filter.eventually_atTop.1 hTrade
  obtain ⟨Tlog, hLog'⟩ := Filter.eventually_atTop.1 hLog
  let T₀ : ℝ := max (Real.exp (Real.exp 1))
    (max Thigh (max Tlow (max Ttrade Tlog)))
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T sigma hT hsigmaLow _hsigmaHigh hthreshold
  have hinner : max Thigh (max Tlow (max Ttrade Tlog)) ≤ T :=
    (le_max_right (Real.exp (Real.exp 1)) _).trans hT
  have hThigh : Thigh ≤ T := (le_max_left _ _).trans hinner
  have hrest : max Tlow (max Ttrade Tlog) ≤ T :=
    (le_max_right Thigh _).trans hinner
  have hTlow : Tlow ≤ T := (le_max_left _ _).trans hrest
  have hrest' : max Ttrade Tlog ≤ T := (le_max_right Tlow _).trans hrest
  have hTtrade : Ttrade ≤ T := (le_max_left _ _).trans hrest'
  have hTlog : Tlog ≤ T := (le_max_right _ _).trans hrest'
  have hHighT := hHigh T hThigh
  have hLowT := hLowDecay' T hTlow
  have hTradeT := hTrade' T hTtrade
  have hLogT := hLog' T hTlog
  have hTlarge : Real.exp (Real.exp 1) ≤ T :=
    (le_max_left (Real.exp (Real.exp 1)) _).trans hT
  have hTpos : 0 < T := (Real.exp_pos (Real.exp 1)).trans_le hTlarge
  have hpow0 : 0 ≤ Real.rpow (Real.log T) (-(3 / 4 : ℝ)) :=
    Real.rpow_nonneg (Real.log_nonneg (by
      exact (Real.one_le_exp (Real.exp_pos 1).le).trans hTlarge)) _
  have hprim : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
    show (1 : DirichletCharacter ℂ 1).conductor = 1
    rw [DirichletCharacter.conductor_one]
  have hqcap : ((1 : ℕ) : ℝ) ≤ Real.rpow (Real.log T) 1 := by
    simpa using hLogT
  rw [Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  obtain ⟨rho, hrho⟩ := hnonempty
  have hfull : rho ∈ zeroSupport chiOne 0 T :=
    MAPMellinDetectorLeaf.zeroSupport_mono chiOne (by linarith) le_rfl hrho
  have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
    chiOne sigma T hrho
  rw [zeroRectangle, Complex.mem_reProdIm] at hrect
  have hre : sigma ≤ rho.re := hrect.1.1
  have hbeta : 4 / 5 < rho.re := by linarith
  have himT : |rho.im| ≤ T := abs_le.mpr hrect.2
  have hweak : c * Real.rpow (Real.log T) (-(3 / 4 : ℝ)) ≤
      1 - rho.re := by
    by_cases him : |rho.im| < 3
    · have hgap := hLow 1 chiOne hprim rfl T rho hfull hbeta him
      exact hLowT.trans hgap
    · have hgap := hHighT 1 chiOne hprim hqcap T rho hfull hbeta
          (le_of_not_gt him) himT
      have hcoef : c ≤ cHigh := min_le_left _ _
      exact (mul_le_mul_of_nonneg_right hcoef hpow0).trans hgap
  linarith

end
end MAPPrincipalZetaHuxley1972ZeroFreeFromHighGap

#print axioms MAPPrincipalZetaHuxley1972ZeroFreeFromHighGap.correctedEquation610ZeroFree_of_primitiveRegularHighGap
