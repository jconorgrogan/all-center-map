import MRTMediumEq79ParallelCore
import MRTEquation81AveragingBilinear

/-!
# MRT (79)--(81): exact moving-window normalization

This module identifies the `ENNReal` moving average used by the certified
equation-(81) Schur argument with the literal real interval integral in
`proposition51I`.  No enlargement of the radius `|β|H` is made.
-/

namespace MAPMRTMediumEq79Parallel

open MeasureTheory Set
open MAPMRTCorollary53Source
open MAPFarAnnulusSourceToModel
open MAPMRTProposition51Source MAPMRTEquation81Averaging
open MAPMRTEquation81AveragingBilinear

noncomputable section

/-- Nonnegative version of the source Dirichlet-polynomial amplitude. -/
def criticalNormWeight (N : ℕ) (f : ℕ → ℂ) (t : ℝ) : ENNReal :=
  ENNReal.ofReal ‖finiteCriticalPolynomial N f t‖

theorem measurable_criticalNormWeight (N : ℕ) (f : ℕ → ℂ) :
    Measurable (criticalNormWeight N f) :=
  (continuous_norm_finiteCriticalPolynomial N f).measurable.ennreal_ofReal

/-- The equation-(81) radius is exactly the manuscript radius `|β|H`. -/
theorem equation81Average_criticalNormWeight_eq_untwistedWindow
    {N : ℕ} {X H beta x : ℝ} {f : ℕ → ℂ}
    (hH : 0 ≤ H) :
    equation81Average (|beta| * H) (criticalNormWeight N f) x =
      ENNReal.ofReal
        (∫ t in (x - |beta| * H)..(x + |beta| * H),
          ‖finiteCriticalPolynomial N f t‖) := by
  have hR : 0 ≤ |beta| * H := mul_nonneg (abs_nonneg _) hH
  let a : ℝ := x - |beta| * H
  let b : ℝ := x + |beta| * H
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hc : Continuous (fun t : ℝ ↦ ‖finiteCriticalPolynomial N f t‖) :=
    continuous_norm_finiteCriticalPolynomial N f
  have hint : IntegrableOn
      (fun t : ℝ ↦ ‖finiteCriticalPolynomial N f t‖) (Icc a b) :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  rw [equation81Average_eq_symmetricMovingIntegral]
  unfold symmetricMovingIntegral criticalNormWeight
  change (∫⁻ t in Icc a b,
      ENNReal.ofReal ‖finiteCriticalPolynomial N f t‖) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun t ↦ norm_nonneg _)]
  congr 1
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

/-- The exact `ENNReal` counterpart of the source's `proposition51I`. -/
def proposition51ILintegral
    (N : ℕ) (X H : ℝ) (f : ℕ → ℂ) (beta eta : ℝ) : ENNReal :=
  ∑ component : OuterComponent,
    let endpoints := componentEndpoints X beta eta component
    ∫⁻ t in Icc endpoints.1 endpoints.2,
      (equation81Average (|beta| * H) (criticalNormWeight N f) t) ^ 2

/-- Each real component integral in `proposition51I` is nonnegative. -/
theorem untwistedComponentIntegral_nonneg
    {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 ≤ X) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (component : OuterComponent) :
    0 ≤ untwistedComponentIntegral X H f beta eta component := by
  unfold untwistedComponentIntegral
  apply intervalIntegral.integral_nonneg
    (componentEndpoints_mono hX heta hetaOne component)
  intro t ht
  positivity

/-- Exact weld from the Schur-side moving-window mass to the published
`proposition51I`.  The finite polynomial cutoff is the source cutoff
`N=⌊2X⌋₊`; no change in the outer components or inner radius occurs. -/
theorem proposition51ILintegral_eq_ofReal_proposition51I
    {X H beta eta : ℝ} {f : ℕ → ℂ}
    (hX : 0 ≤ X) (hH : 0 ≤ H)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) :
    proposition51ILintegral ⌊2 * X⌋₊ X H f beta eta =
      ENNReal.ofReal (proposition51I X H f beta eta) := by
  unfold proposition51ILintegral proposition51I
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro component hcomponent
    let endpoints := componentEndpoints X beta eta component
    let a := endpoints.1
    let b := endpoints.2
    have hab : a ≤ b := by
      exact componentEndpoints_mono hX heta hetaOne component
    have havg : Continuous (fun t : ℝ ↦
        ∫ u in (t - |beta| * H)..(t + |beta| * H),
          ‖finiteCriticalPolynomial ⌊2 * X⌋₊ f u‖) :=
      continuous_movingWindowIntegral
        (continuous_norm_finiteCriticalPolynomial ⌊2 * X⌋₊ f)
        (|beta| * H)
    have hint : IntegrableOn (fun t : ℝ ↦
        (∫ u in (t - |beta| * H)..(t + |beta| * H),
          ‖finiteCriticalPolynomial ⌊2 * X⌋₊ f u‖) ^ 2) (Icc a b) :=
      havg.pow 2 |>.continuousOn.integrableOn_compact isCompact_Icc
    dsimp only
    rw [show componentEndpoints X beta eta component = endpoints by rfl]
    change (∫⁻ t in Icc a b,
        (equation81Average (|beta| * H)
          (criticalNormWeight ⌊2 * X⌋₊ f) t) ^ 2) = _
    simp_rw [equation81Average_criticalNormWeight_eq_untwistedWindow
      (N := ⌊2 * X⌋₊) (X := X) (f := f) hH]
    have hpows : (fun t : ℝ ↦
        (ENNReal.ofReal
          (∫ u in (t - |beta| * H)..(t + |beta| * H),
            ‖finiteCriticalPolynomial ⌊2 * X⌋₊ f u‖)) ^ 2) =
        (fun t : ℝ ↦ ENNReal.ofReal
          ((∫ u in (t - |beta| * H)..(t + |beta| * H),
            ‖finiteCriticalPolynomial ⌊2 * X⌋₊ f u‖) ^ 2)) := by
      funext t
      symm
      apply ENNReal.ofReal_pow
      apply intervalIntegral.integral_nonneg
      · have hR : 0 ≤ |beta| * H := mul_nonneg (abs_nonneg _) hH
        linarith
      · intro u hu
        exact norm_nonneg _
    rw [hpows]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)]
    congr 1
    dsimp [untwistedComponentIntegral, untwistedWindow, endpoints, a, b]
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  · intro component hcomponent
    exact untwistedComponentIntegral_nonneg hX heta hetaOne component

end
end MAPMRTMediumEq79Parallel

#print axioms MAPMRTMediumEq79Parallel.equation81Average_criticalNormWeight_eq_untwistedWindow
#print axioms MAPMRTMediumEq79Parallel.proposition51ILintegral_eq_ofReal_proposition51I
