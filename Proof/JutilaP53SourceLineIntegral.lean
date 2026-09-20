import JutilaP53SourceLineEstimate
import JutilaP53AmbientSourceConvexity

/-! # Actual integrability and uniform norm bound on Jutila's source line -/
namespace MAPJutilaP53SourceLineIntegral
open Complex Real MeasureTheory
open MAPJutilaP53TwoScaleContour MAPJutilaP53SourceLineEstimate
open MAPJutilaP53AmbientSourceConvexity
open RamachandraShiftedGammaPoleContour
noncomputable section

/-- An actual ambient nonprincipal source-line integral theorem: neither
integrability nor a pointwise L-bound is assumed. -/
theorem exists_sourceLine_integrable_and_norm_integral_le
    {epsilon : ℝ} (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      ∀ (s : ℂ) (U V : ℝ), 0 < U → 0 < V →
      0 ≤ s.re → s.re ≤ 2 * epsilon →
      Integrable (fun t : ℝ => p53TwoScaleContourIntegrand chi s U V
        (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)) ∧
      ‖∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) *
          (Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon)) := by
  obtain ⟨C, hC, hL⟩ := exists_ambient_source_convexity heps (by linarith)
  let f : ℝ → ℝ := fun t => (1 + |t|)^6 * Real.exp (-|t|)
  let J : ℝ := ∫ t : ℝ, f t
  have hf : Integrable f := integrable_one_add_abs_pow_six_mul_exp_neg_abs
  have hJ : 0 ≤ J := integral_nonneg fun t => by dsimp [f]; positivity
  let A : ℝ := (24 / epsilon) * C
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A * (1 + J), mul_pos hA (by linarith), ?_⟩
  intro q _inst chi hchi s U V hU hV hsLo hsHi
  let B : ℝ := Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2)
  let D : ℝ := Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon)
  let F : ℝ → ℂ := fun t => p53TwoScaleContourIntegrand chi s U V
    (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)
  have hB : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  have hD : 0 ≤ D := add_nonneg (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg hV.le _)
  have hbound (t : ℝ) : ‖F t‖ ≤ (A * B * D) * f t := by
    have hraw := norm_integrand_sourceLine_le_of_pointwiseL chi hC.le hU hV
      heps hepsHi hsLo hsHi
      (hL q chi hchi (epsilon + s.re) (s.im + t) (by linarith) (by linarith))
    have hpow : (1 + |t|)^2 ≤ (1 + |t|)^6 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by norm_num)
    have hexp : Real.exp (-(Real.pi / 2) * |t|) ≤ Real.exp (-|t|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three, abs_nonneg t]
    calc
      ‖F t‖ ≤ A * B * (1 + |t|)^2 * Real.exp (-(Real.pi / 2) * |t|) * D := hraw
      _ ≤ A * B * (1 + |t|)^6 * Real.exp (-|t|) * D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hpow (mul_nonneg hA.le hB)) hexp
            (Real.exp_pos _).le (by positivity)) hD
      _ = (A * B * D) * f t := by dsimp [f]; ring
  have hcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro t
    have hinner : ContinuousAt (fun u : ℝ =>
        (((-1 + epsilon : ℝ) : ℂ) + (u : ℂ) * I)) t := by fun_prop
    have houter :=
      (differentiableAt_p53TwoScaleContourIntegrand_nonprincipal hchi s hU hV
        (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)
        (by simp; linarith)).continuousAt
    exact ContinuousAt.comp
      (f := fun u : ℝ => (((-1 + epsilon : ℝ) : ℂ) + (u : ℂ) * I))
      (g := p53TwoScaleContourIntegrand chi s U V) (x := t) houter hinner
  have hmajor : Integrable (fun t : ℝ => (A * B * D) * f t) := hf.const_mul _
  have hInt : Integrable F := hmajor.mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  refine ⟨hInt, ?_⟩
  calc
    ‖∫ t : ℝ, F t‖ ≤ ∫ t : ℝ, (A * B * D) * f t :=
      MeasureTheory.norm_integral_le_of_norm_le hmajor (Filter.Eventually.of_forall hbound)
    _ = (A * B * D) * J := by rw [integral_const_mul]
    _ ≤ (A * B * D) * (1 + J) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg hA.le hB) hD)
    _ = _ := by dsimp [B, D]; ring
end
end MAPJutilaP53SourceLineIntegral
#print axioms MAPJutilaP53SourceLineIntegral.exists_sourceLine_integrable_and_norm_integral_le
