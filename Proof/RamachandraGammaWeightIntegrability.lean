import RamachandraWeightedCauchy
import RamachandraShiftedHeadContourTails

/-!
# Full-line Gamma weight for shifted Mellin Cauchy
-/

namespace RamachandraGammaWeightIntegrability

open Complex MeasureTheory Set
open RamachandraShiftedHeadContourTails
open RamachandraShiftedGammaPoleContour

noncomputable section

def gammaPolynomialWeight (c : ℝ) (v : ℝ) : ℝ :=
  ‖Complex.Gamma ((c : ℂ) + (v : ℂ) * I)‖ * (1 + |v|) ^ 6

theorem continuous_gammaPolynomialWeight {c : ℝ}
    (hcLo : -1 < c) (hcHi : c < 0) :
    Continuous (gammaPolynomialWeight c) := by
  apply Continuous.mul
  · apply Continuous.norm
    rw [continuous_iff_continuousAt]
    intro v
    have harg : DifferentiableAt ℂ Complex.Gamma ((c : ℂ) + (v : ℂ) * I) := by
      apply Complex.differentiableAt_Gamma
      intro n hn
      have hre := congrArg Complex.re hn
      simp at hre
      by_cases hn0 : n = 0
      · subst n
        norm_num at hre
        linarith
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
        linarith
    have hinner : ContinuousAt (fun x : ℝ => (c : ℂ) + (x : ℂ) * I) v := by
      fun_prop
    exact harg.continuousAt.comp_of_eq hinner rfl
  · fun_prop

/-- The degree-six weight is ample for both sharp contour factors and has
finite mass on the entire Mellin line. -/
theorem integrable_gammaPolynomialWeight {c : ℝ}
    (hcLo : -1 < c) (hcHi : c < 0) :
    Integrable (gammaPolynomialWeight c) := by
  let S : Set ℝ := {v | 1 ≤ |v|}
  let E : ℝ → ℝ := fun v =>
    12 * ((1 + |v|) ^ 8 * Real.exp (-|v|))
  have hcont := continuous_gammaPolynomialWeight hcLo hcHi
  have hE : Integrable E :=
    integrable_one_add_abs_pow_eight_mul_exp_neg_abs.const_mul 12
  have htail : IntegrableOn (gammaPolynomialWeight c) S := by
    apply hE.integrableOn.mono'
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (by
          dsimp [S]
          exact measurableSet_le measurable_const measurable_abs)] with v hv
      have hgamma := norm_Gamma_ramachandraHorizontalStrip_le_exp
        (a := c) (t := v) (by linarith) (by linarith) hv
      rw [Real.norm_of_nonneg (by
        unfold gammaPolynomialWeight
        positivity : 0 ≤ gammaPolynomialWeight c v)]
      dsimp [gammaPolynomialWeight, E]
      calc
        ‖Complex.Gamma ((c : ℂ) + (v : ℂ) * I)‖ * (1 + |v|) ^ 6 ≤
            (12 * (1 + |v|) ^ 2 * Real.exp (-|v|)) *
              (1 + |v|) ^ 6 :=
          mul_le_mul_of_nonneg_right hgamma (by positivity)
        _ = 12 * ((1 + |v|) ^ 8 * Real.exp (-|v|)) := by ring
  have hcompact : IntegrableOn (gammaPolynomialWeight c) (Sᶜ) := by
    have hIcc : IntegrableOn (gammaPolynomialWeight c) (Set.Icc (-1 : ℝ) 1) :=
      hcont.integrableOn_Icc
    apply hIcc.mono_set
    intro v hv
    have hv' : ¬ 1 ≤ |v| := by simpa [S] using hv
    have habs : |v| < 1 := lt_of_not_ge hv'
    exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
  have hall := htail.union hcompact
  rw [Set.union_compl_self] at hall
  exact integrableOn_univ.mp hall

theorem gammaPolynomialWeight_nonneg (c v : ℝ) :
    0 ≤ gammaPolynomialWeight c v := by
  unfold gammaPolynomialWeight
  positivity

end
end RamachandraGammaWeightIntegrability

#print axioms RamachandraGammaWeightIntegrability.integrable_gammaPolynomialWeight
