import JutilaDualTailPSeries
import GammaCompactStripSharp

/-!
# Literal pointwise reduction of Jutila's `I₂` error

On the shifted line `w=-h/2+iv`, this combines the certified Gamma decay,
two-scale quotient bound, and the full real-power dual-series tail.  The
functional-equation multiplier is deliberately left in its exact norm.  Thus
the theorem exposes, without a renamed `I₂` premise, the sole remaining
archimedean estimate needed for the numerical error bound on p. 58.
-/

namespace JutilaDualTailIntegrandBound

open Complex Real
open JutilaDualTailContour JutilaDualTailPSeries
open JutilaTwoScaleHorizontalDecay
open JutilaTwoScaleSmoothing JutilaCriticalPartialTruncation
open MAPGammaCompactStripSharp

noncomputable section

def dualTailShiftedPoint (s : ℂ) (h v : ℝ) : ℂ :=
  s + ((-(h / 2) : ℝ) : ℂ) + v * I

/-- Exact pointwise reduction on Jutila's new `I₂` line.  Every factor other
than the deep-left functional-equation multiplier has its explicit source
majorant. -/
theorem norm_dualTailIntegrand_shifted_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (s : ℂ) {N h : ℝ} (hN : 0 < N) (hh : 3 ≤ h)
    (hsigma0 : 0 ≤ s.re) (hsigma1 : s.re ≤ 1)
    {M : ℕ} (hM : 1 ≤ M) {v : ℝ} (hv : 1 ≤ |v|) :
    ‖dualTailIntegrand chi s N h M
        (((-(h / 2) : ℝ) : ℂ) + v * I)‖ ≤
      (12 * (1 + |v| / h) *
          Real.exp (-(Real.pi / 2) * (|v| / h))) *
        twoScaleCpowEndpointBound N (-(h / 2)) (-(h / 2)) *
        ‖reflectedDualMultiplier chi (dualTailShiftedPoint s h v)‖ *
        ((M : ℝ) ^ (s.re - h / 2 - 1) +
          (M : ℝ) ^ (s.re - h / 2) / (h / 2 - s.re)) := by
  have hh0 : 0 < h := lt_of_lt_of_le (by norm_num) hh
  let w : ℂ := (((-(h / 2) : ℝ) : ℂ) + v * I)
  let z : ℂ := s + w
  have hzre : z.re = s.re - h / 2 := by
    simp [z, w]
    ring
  have hzneg : z.re < 0 := by rw [hzre]; nlinarith
  have hGammaPoint :
      1 + w / (h : ℂ) =
        GammaCompactStripScratch.stripPoint (1 / 2) (v / h) := by
    apply Complex.ext
    · simp [w, GammaCompactStripScratch.stripPoint]
      field_simp [hh0.ne']
      ring
    · simp [w, GammaCompactStripScratch.stripPoint]
  have hGamma := norm_Gamma_positive_strip_le_exp_pi_half
    (a := (1 / 2 : ℝ)) (t := v / h) (by norm_num) (by norm_num)
  rw [← hGammaPoint] at hGamma
  have habs : |v / h| = |v| / h := by rw [abs_div, abs_of_pos hh0]
  rw [habs] at hGamma
  have hQ := norm_twoScaleRemovableQuotient_horizontal_le
    hN (a := -(h / 2)) (b := -(h / 2))
      (x := -(h / 2)) le_rfl le_rfl hv
  have htail := norm_dualTail_le chi hzneg hM
  rw [hzre] at htail
  have hzname : z = dualTailShiftedPoint s h v := by
    simp [z, w, dualTailShiftedPoint]
    ring
  have htailNamed :
      ‖dualTail chi (dualTailShiftedPoint s h v) M‖ ≤
        (M : ℝ) ^ (s.re - h / 2 - 1) +
          (M : ℝ) ^ (s.re - h / 2) / (h / 2 - s.re) := by
    simpa [z, hzname, dualTailShiftedPoint] using htail
  have hGammaR0 : 0 ≤
      12 * (1 + |v| / h) *
        Real.exp (-(Real.pi / 2) * (|v| / h)) := by positivity
  have hQ0 : 0 ≤ twoScaleCpowEndpointBound N (-(h / 2)) (-(h / 2)) :=
    twoScaleCpowEndpointBound_nonneg hN _ _
  have hGQ :
      ‖Complex.Gamma (1 + w / (h : ℂ))‖ *
          ‖twoScaleRemovableQuotient N w‖ ≤
        (12 * (1 + |v| / h) *
          Real.exp (-(Real.pi / 2) * (|v| / h))) *
            twoScaleCpowEndpointBound N (-(h / 2)) (-(h / 2)) :=
    mul_le_mul hGamma hQ (norm_nonneg _) hGammaR0
  have hGQF :
      ‖Complex.Gamma (1 + w / (h : ℂ))‖ *
          ‖twoScaleRemovableQuotient N w‖ *
          ‖reflectedDualMultiplier chi (dualTailShiftedPoint s h v)‖ ≤
        (12 * (1 + |v| / h) *
          Real.exp (-(Real.pi / 2) * (|v| / h))) *
            twoScaleCpowEndpointBound N (-(h / 2)) (-(h / 2)) *
          ‖reflectedDualMultiplier chi (dualTailShiftedPoint s h v)‖ :=
    mul_le_mul_of_nonneg_right hGQ (norm_nonneg _)
  have hpref0 : 0 ≤
      (12 * (1 + |v| / h) *
        Real.exp (-(Real.pi / 2) * (|v| / h))) *
          twoScaleCpowEndpointBound N (-(h / 2)) (-(h / 2)) *
        ‖reflectedDualMultiplier chi (dualTailShiftedPoint s h v)‖ :=
    mul_nonneg (mul_nonneg hGammaR0 hQ0) (norm_nonneg _)
  unfold dualTailIntegrand
  change ‖Complex.Gamma (1 + w / (h : ℂ)) *
      twoScaleRemovableQuotient N w * reflectedDualMultiplier chi z *
        dualTail chi z M‖ ≤ _
  repeat' rw [norm_mul]
  rw [hzname]
  calc
    ‖Complex.Gamma (1 + w / (h : ℂ))‖ *
          ‖twoScaleRemovableQuotient N w‖ *
          ‖reflectedDualMultiplier chi (dualTailShiftedPoint s h v)‖ *
          ‖dualTail chi (dualTailShiftedPoint s h v) M‖ ≤
      (12 * (1 + |v| / h) *
          Real.exp (-(Real.pi / 2) * (|v| / h))) *
        twoScaleCpowEndpointBound N (-(h / 2)) (-(h / 2)) *
        ‖reflectedDualMultiplier chi (dualTailShiftedPoint s h v)‖ *
        ((M : ℝ) ^ (s.re - h / 2 - 1) +
          (M : ℝ) ^ (s.re - h / 2) / (h / 2 - s.re)) := by
      exact mul_le_mul hGQF htailNamed (norm_nonneg _) hpref0
    _ = _ := rfl

end

end JutilaDualTailIntegrandBound

#print axioms JutilaDualTailIntegrandBound.norm_dualTailIntegrand_shifted_le
