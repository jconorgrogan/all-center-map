import GuthMaynardLemma44TraceOne

/-!
# Exact cancellation of the Section 4 Poisson main terms

The zero Fourier coefficient of the literal cutoff is real.  Consequently
the cubic Poisson main term cancels the cube of the trace-one main term with
the exact `|W|^2` normalization used in Proposition 4.6.
-/

namespace GuthMaynardProposition46MainCancellation

open MeasureTheory
open GuthMaynardS1Source GuthMaynardSectionThreeCutoff

noncomputable section

theorem sourceHhat_zero_zero_eq_ofReal_integral :
    sourceHhat 0 0 =
      ((∫ x in Set.Ioi (0 : ℝ), sectionThreeCutoffReal x ^ 2 : ℝ) : ℂ) := by
  rw [sourceHhat_zero_eq_mellin]
  unfold mellin sectionThreeCutoff
  have he : ((1 : ℂ) + (0 : ℝ) * Complex.I) - 1 = 0 := by norm_num
  rw [he]
  simp only [Complex.cpow_zero, one_smul]
  calc
    (∫ x in Set.Ioi (0 : ℝ), (sectionThreeCutoffReal x : ℂ) ^ 2) =
        ∫ x in Set.Ioi (0 : ℝ), ((sectionThreeCutoffReal x ^ 2 : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with x
          exact (Complex.ofReal_pow _ _).symm
    _ = ((∫ x in Set.Ioi (0 : ℝ), sectionThreeCutoffReal x ^ 2 : ℝ) : ℂ) :=
      integral_ofReal

theorem sourceHhat_zero_zero_im : (sourceHhat 0 0).im = 0 := by
  rw [sourceHhat_zero_zero_eq_ofReal_integral]
  simp

theorem source_poisson_main_cancellation
    {N : ℕ} {W : Finset ℝ} (hW : W.Nonempty) :
    (((N : ℂ) ^ 3 * (W.card : ℂ) * sourceHhat 0 0 ^ 3).re) =
      (((N : ℂ) * (W.card : ℂ) * sourceHhat 0 0).re) ^ 3 /
        (W.card : ℝ) ^ 2 := by
  have hw0 : (W.card : ℝ) ≠ 0 := by
    exact_mod_cast hW.card_ne_zero
  rw [sourceHhat_zero_zero_eq_ofReal_integral]
  let a : ℝ := ∫ x in Set.Ioi (0 : ℝ), sectionThreeCutoffReal x ^ 2
  have hM3 : (N : ℂ) ^ 3 * (W.card : ℂ) * (a : ℂ) ^ 3 =
      (((N : ℝ) ^ 3 * (W.card : ℝ) * a ^ 3 : ℝ) : ℂ) := by
    push_cast
    ring
  have hM1 : (N : ℂ) * (W.card : ℂ) * (a : ℂ) =
      (((N : ℝ) * (W.card : ℝ) * a : ℝ) : ℂ) := by
    push_cast
    ring
  change ((N : ℂ) ^ 3 * (W.card : ℂ) * (a : ℂ) ^ 3).re =
    ((N : ℂ) * (W.card : ℂ) * (a : ℂ)).re ^ 3 / (W.card : ℝ) ^ 2
  rw [hM3, hM1]
  simp only [Complex.ofReal_re]
  field_simp [hw0]

end
end GuthMaynardProposition46MainCancellation

#print axioms GuthMaynardProposition46MainCancellation.sourceHhat_zero_zero_eq_ofReal_integral
#print axioms GuthMaynardProposition46MainCancellation.source_poisson_main_cancellation
