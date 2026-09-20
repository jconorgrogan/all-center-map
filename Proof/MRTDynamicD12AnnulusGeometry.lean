import MRTProposition61HighAnnulusPreservationV3
import MRTDynamicD12MomentSource
import MRTProposition61TypeIIEndpointWidthV3

/-! First serialized annulus weld for the d1/d2 carrier.  The component is
kept in its original signed location; the enlarged interval is
`[a-P-U,b+P+U]`, not a centered replacement. -/
namespace MRTDynamicD12AnnulusGeometry

open Filter
open MAPMRTCorollary53Source MAPDynamicHBSourceV3
open MRTProposition61HighAnnulusPreservationV3
open MRTProposition61TypeIIEndpointWidthV3
open MRTDynamicD12MomentSource
open MRTLemma215HBExpansion

noncomputable section

set_option maxHeartbeats 1000000

def d12FreePerronHeight (lambda X : ℝ) : ℝ :=
  lambda * Real.rpow X (23 / 24)

def d12MomentHeight (lambda X Q : ℝ) : ℝ :=
  2 * lambda * X * Real.sqrt Q

def d12InnerRadius (lambda X Q : ℝ) : ℝ :=
  lambda * X / (2 * Real.sqrt Q)

theorem d12FreePerronHeight_eq_sigma (lambda X : ℝ) :
    d12FreePerronHeight lambda X =
      lambda * Real.rpow X (1 - (1 / 24 : ℝ)) := by
  unfold d12FreePerronHeight
  congr 1
  ring

theorem outerLower_eq_two_rho_of_eta
    {X beta Q : ℝ} (hQ : 0 < Q) :
    outerLower X beta (1 / Real.sqrt Q) =
      2 * d12InnerRadius |beta| X Q := by
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  unfold outerLower d12InnerRadius
  field_simp

theorem outerUpper_eq_T_half_of_eta
    {X beta Q : ℝ} (hQ : 0 < Q) :
    outerUpper X beta (1 / Real.sqrt Q) =
      d12MomentHeight |beta| X Q / 2 := by
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  unfold outerUpper d12MomentHeight
  field_simp

theorem eventually_freePerron_add_width_le_innerRadius (B : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (lambda reserve : ℝ),
      0 ≤ lambda → reserve ≤ 1 / 1200 →
      d12FreePerronHeight lambda X +
          lambda * ((1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve)) ≤
        d12InnerRadius lambda X ((Real.log X) ^ B) := by
  filter_upwards [eventually_freeTruncation_add_width_le_half_innerRadius
    B (1 / 24) (by norm_num) (by norm_num)] with X hX
  intro lambda reserve hlambda hr
  simpa [d12FreePerronHeight, d12InnerRadius,
    show (23 / 24 : ℝ) = 1 - (1 / 24 : ℝ) by ring] using
    hX lambda reserve hlambda hr

theorem enlarged_component_mem_rho_band
    {X beta eta P U T rho : ℝ}
    (hX : 0 ≤ X) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hP : 0 ≤ P) (hU : 0 ≤ U) (hT : 0 ≤ T)
    (hPU : P + U ≤ rho)
    (hLower : outerLower X beta eta = 2 * rho)
    (hUpper : outerUpper X beta eta = T / 2)
    (component : OuterComponent) {t : ℝ}
    (ht : t ∈ Set.Icc
      ((componentEndpoints X beta eta component).1 - (P + U))
      ((componentEndpoints X beta eta component).2 + (P + U))) :
    rho ≤ |t| ∧ |t| ≤ T := by
  have houter0 : 0 ≤ outerLower X beta eta := by
    unfold outerLower
    positivity
  have hrho : 0 ≤ rho := by linarith
  have hlo : rho ≤ outerLower X beta eta - (P + U) := by linarith
  have hcmp : outerLower X beta eta ≤ outerUpper X beta eta := by
    unfold outerLower outerUpper
    have hetaSq : eta ^ 2 ≤ 1 := by nlinarith
    apply (le_div_iff₀ heta).2
    nlinarith [mul_nonneg (abs_nonneg beta) hX]
  have hhi : outerUpper X beta eta + (P + U) ≤ T := by
    have : rho ≤ outerUpper X beta eta := by linarith
    linarith
  cases component with
  | positive =>
      simp only [componentEndpoints, Set.mem_Icc] at ht
      have ht0 : rho ≤ t := hlo.trans (by linarith)
      have ht1 : t ≤ T := (by linarith :
        t ≤ outerUpper X beta eta + (P + U)).trans hhi
      have habs : |t| = t := abs_of_nonneg (hrho.trans ht0)
      exact ⟨by simpa [habs] using ht0, by simpa [habs] using ht1⟩
  | negative =>
      simp only [componentEndpoints, Set.mem_Icc] at ht
      have hneg : t ≤ -rho := by linarith
      have hpos : |t| = -t := abs_of_nonpos
        (hneg.trans (neg_nonpos.2 hrho))
      constructor
      · have : rho ≤ -t := by linarith
        simpa [hpos] using this
      · have : -t ≤ outerUpper X beta eta + (P + U) := by linarith
        have : -t ≤ T := this.trans hhi
        simpa [hpos] using this

theorem enlarged_length_succ_le_Tmoment
    {X beta eta P U T rho : ℝ}
    (hX : 0 ≤ X) (heta : 0 < eta) (hPU : P + U ≤ rho)
    (hLower : outerLower X beta eta = 2 * rho)
    (hUpper : outerUpper X beta eta = T / 2)
    (hOuter : 1 ≤ outerUpper X beta eta)
    (component : OuterComponent) :
    ((componentEndpoints X beta eta component).2 + (P + U)) -
        ((componentEndpoints X beta eta component).1 - (P + U)) + 1 ≤ T := by
  have hwidth := componentEndpoints_sub_eq_outerUpper_sub_outerLower
    X beta eta component
  have hrewrite :
      ((componentEndpoints X beta eta component).2 + (P + U)) -
          ((componentEndpoints X beta eta component).1 - (P + U)) + 1 =
        (componentEndpoints X beta eta component).2 -
          (componentEndpoints X beta eta component).1 + 2 * (P + U) + 1 := by
    ring
  rw [hrewrite, hwidth]
  have : outerUpper X beta eta - outerLower X beta eta +
      2 * (P + U) + 1 ≤
      outerUpper X beta eta - outerLower X beta eta + 2 * rho + 1 := by
    gcongr
  have hsimp : outerUpper X beta eta - outerLower X beta eta +
      2 * rho + 1 = outerUpper X beta eta + 1 := by linarith
  have hT : T = 2 * outerUpper X beta eta := by linarith
  have : outerUpper X beta eta + 1 ≤ T := by
    rw [hT]
    linarith
  linarith

theorem hbFactorCutoff_le_eightX {X : ℝ} (hX : 0 ≤ X) :
    (hbFactorCutoff X : ℝ) ≤ 8 * X := by
  unfold hbFactorCutoff
  exact (Nat.floor_le (by positivity : 0 ≤ 2 * X)).trans (by linarith)

theorem hbFactorCutoff_ge_two {X : ℝ} (hX : 1 ≤ X) :
    2 ≤ hbFactorCutoff X := by
  unfold hbFactorCutoff
  exact Nat.le_floor (by linarith : (2 : ℝ) ≤ 2 * X)

theorem dynamicD12MomentRange_eightX
    {X T : ℝ} {q B : ℕ}
    (hX : 1 ≤ X) (hT : 2 ≤ T) (hq : 1 ≤ q)
    (hB : (B : ℝ) ≤ Real.log (Real.log (8 * X)))
    (hqlog : (q : ℝ) ≤ (Real.log (8 * X)) ^ B)
    (hqT : (q : ℝ) ≤ T) (hT8 : 2 * T ≤ 8 * X) :
    DynamicD12MomentRange (8 * X) T (B : ℝ) q (hbFactorCutoff X) := by
  refine ⟨?_, hT, hq, hbFactorCutoff_ge_two hX,
    Nat.cast_nonneg _, hB, ?_, hqT,
    hbFactorCutoff_le_eightX (by linarith), hT8⟩
  · nlinarith
  · simpa [Real.rpow_natCast] using hqlog

end
end MRTDynamicD12AnnulusGeometry
