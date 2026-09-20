import GuthMaynardLemma295ThetaAnalytic
import GuthMaynardLemma295DualTail

/-!
# Compact low-ordinate theta control on the deep-left line

The recurrence bound handles `|t-g| >= 2`.  The complementary bounded
ordinate interval is compact and pole-free because the deep-left real part is
strictly below one.  This module supplies the finite constant needed for that
piece of the vertical-tail integral.
-/

namespace GuthMaynardLemma295ThetaDeepCompact

open Complex Set
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295ThetaAnalytic
open GuthMaynardLemma295DualTail

noncomputable section

theorem continuous_deepLeftThetaNorm (n : ℕ) :
    Continuous (fun u : ℝ =>
      ‖sourceZetaTheta ((deepLeftSigma n : ℂ) + u * I)‖) := by
  apply Continuous.norm
  apply continuous_iff_continuousAt.2
  intro u
  have hsre : (((deepLeftSigma n : ℂ) + u * I)).re < 1 := by
    simp [deepLeftSigma]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact (differentiableAt_sourceZetaTheta_of_re_lt_one hsre).continuousAt.comp_of_eq
    (by fun_prop) rfl

/-- An explicit existential constant, depending only on the fixed contour
depth, controls the exceptional compact ordinate range. -/
theorem exists_deepLeftTheta_compact_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Set.Icc (-2 : ℝ) 2,
      ‖sourceZetaTheta ((deepLeftSigma n : ℂ) + u * I)‖ ≤ C := by
  let f : ℝ → ℝ := fun u =>
    ‖sourceZetaTheta ((deepLeftSigma n : ℂ) + u * I)‖
  have hf : Continuous f := continuous_deepLeftThetaNorm n
  obtain ⟨u₀, hu₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (by exact ⟨0, by norm_num⟩ : (Set.Icc (-2 : ℝ) 2).Nonempty)
    hf.continuousOn
  let C : ℝ := max 1 (f u₀)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu
  exact (hmax hu).trans (le_max_right _ _)

end

end GuthMaynardLemma295ThetaDeepCompact

#print axioms GuthMaynardLemma295ThetaDeepCompact.exists_deepLeftTheta_compact_bound
