import FordScaledLRemainder
import FordFinitePoleReal
import FordScaledLZeroReal
import FordScaledDiskEvaluation

open scoped BigOperators
noncomputable section
namespace FordScaledLLogDerivativeUpper

open Complex Set Metric FordScaledDiskGrowth

/-- A common thin-disk logarithmic-derivative upper bound, including the
selected-pole refinement for every actual zero at the evaluation ordinate. -/
theorem exists_uniform_actual_negLogDeriv_upper :
    ∃ D : ℝ, 0 < D ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ),
        3 ≤ t → ∀ δ : ℝ, 0 < δ → δ ≤ diskScale t →
        (-logDeriv (DirichletCharacter.LFunction χ)
            (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))).re ≤
          (20 + 1 / (2 * Real.log 2)) *
            (1 + D + 3 * Real.log (N : ℝ) +
              2 * Real.log (Real.log (t + 3))) / diskScale t ∧
        ∀ ρ : ℂ,
          DirichletCharacter.LFunction χ ρ = 0 →
          ρ.im = t →
          1 - ρ.re ≤ diskScale t →
          (-logDeriv (DirichletCharacter.LFunction χ)
              (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))).re ≤
            (20 + 1 / (2 * Real.log 2)) *
              (1 + D + 3 * Real.log (N : ℝ) +
                2 * Real.log (Real.log (t + 3))) / diskScale t -
              1 / (δ + (1 - ρ.re)) := by
  obtain ⟨D, hD, hmain⟩ :=
    FordScaledLRemainder.exists_finite_L_zero_set_remainder
  refine ⟨D, hD, ?_⟩
  intro N hN χ t ht δ hδ hδa
  obtain ⟨S, hSexact, hSprops, hrem⟩ := hmain N χ t ht
  have ha : 0 < diskScale t := (disk_geometry ht).2.1
  have hs :
      (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) ∈
        Metric.ball (diskCenter t) (diskScale t) :=
    FordScaledDiskEvaluation.evaluation_mem_ball ht hδ hδa
  have hsre : 1 <
      ((((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) : ℂ).re := by
    simp
    linarith
  have hfs : DirichletCharacter.LFunction χ
      (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
    FordScaledLZeroReal.LFunction_ne_zero_of_one_lt_re χ hsre
  have hrem' := hrem
    (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) hs hfs
  have hzeroRe : ∀ ρ : ℂ,
      DirichletCharacter.LFunction χ ρ = 0 → ρ.re ≤ 1 := by
    intro ρ hzero
    exact FordScaledLZeroReal.LFunction_eq_zero_re_le_one χ hzero
  have hSright : ∀ z ∈ S,
      z.re ≤ (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)).re := by
    intro z hz
    have hzzero := ((hSexact z).mp hz).2
    exact (hzeroRe z hzzero).trans hsre.le
  have hid :
      logDeriv (DirichletCharacter.LFunction χ)
          (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) =
        (logDeriv (DirichletCharacter.LFunction χ)
            (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) -
          ∑ ρ ∈ S,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) /
              ((((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) - ρ)) +
        ∑ ρ ∈ S,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) /
            ((((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) - ρ) := by
    ring
  have hupper := FordFinitePoleReal.neg_re_le S
    (fun z => analyticOrderNatAt (DirichletCharacter.LFunction χ) z)
    hSright hid hrem'
  refine ⟨hupper, ?_⟩
  intro ρ hρzero him hgap
  have hρball := FordScaledDiskEvaluation.zero_mem_inner_ball ht him
    (hzeroRe ρ hρzero) hgap
  have hρS : ρ ∈ S := (hSexact ρ).mpr ⟨hρball, hρzero⟩
  have hmult := (hSprops ρ hρS).2
  have hρlt : ρ.re <
      (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)).re :=
    (hzeroRe ρ hρzero).trans_lt hsre
  have him' :
      (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)).im = ρ.im := by
    simp [him]
  have hselected := FordFinitePoleReal.neg_re_le_sub_selected S
    (fun z => analyticOrderNatAt (DirichletCharacter.LFunction χ) z)
    hSright hρS hmult him' hρlt hid hrem'
  convert hselected using 1 <;> simp <;> ring

end FordScaledLLogDerivativeUpper

#print axioms FordScaledLLogDerivativeUpper.exists_uniform_actual_negLogDeriv_upper
