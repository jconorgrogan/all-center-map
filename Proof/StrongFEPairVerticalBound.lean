import DirichletLQuantitativeFoundation
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

open Complex Filter Topology Asymptotics Real Set MeasureTheory

namespace PLInteriorGrowth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Mellin transform is bounded by the scalar Mellin integral obtained after
discarding its vertical phase. -/
lemma norm_mellin_le_real_mellin_norm
    (f : ℝ → E) (s : ℂ) (hs : MellinConvergent f s) :
    ‖mellin f s‖ ≤ ∫ t : ℝ in Ioi 0, t ^ (s.re - 1) * ‖f t‖ := by
  rw [mellin]
  calc
    ‖∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • f t‖ ≤
        ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) • f t‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ in Ioi 0, t ^ (s.re - 1) * ‖f t‖ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change ‖(t : ℂ) ^ (s - 1) • f t‖ = t ^ (s.re - 1) * ‖f t‖
      rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]

private lemma rpow_middle_le_endpoint_sum {a b σ t : ℝ}
    (ht : 0 < t) (ha : a ≤ σ) (hb : σ ≤ b) :
    t ^ (σ - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
  rcases le_total t 1 with ht1 | ht1
  · have hpow : t ^ (σ - 1) ≤ t ^ (a - 1) := by
      exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
    exact hpow.trans (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
  · have hpow : t ^ (σ - 1) ≤ t ^ (b - 1) := by
      exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    exact hpow.trans (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))

/-- A strong functional-equation pair is uniformly bounded on every closed
vertical strip.  The proof is the literal Mellin integral estimate; no
Phragmen--Lindelof or number-theoretic growth input is used. -/
theorem StrongFEPair.exists_norm_Λ_le_on_re_Icc
    (P : StrongFEPair E) (a b : ℝ) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖P.Λ s‖ ≤ C := by
  let ga : ℝ → ℝ := fun t => t ^ (a - 1) * ‖P.f t‖
  let gb : ℝ → ℝ := fun t => t ^ (b - 1) * ‖P.f t‖
  have hma := (P.hasMellin (a : ℂ)).1
  have hmb := (P.hasMellin (b : ℂ)).1
  have hmeas : AEStronglyMeasurable P.f (volume.restrict (Ioi 0)) :=
    P.hf_int.aestronglyMeasurable
  have hga : IntegrableOn ga (Ioi 0) := by
    rw [show ga = fun t : ℝ => t ^ (((a : ℂ).re) - 1) * ‖P.f t‖ by
      funext t; simp [ga]]
    exact (mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hmeas).mp hma
  have hgb : IntegrableOn gb (Ioi 0) := by
    rw [show gb = fun t : ℝ => t ^ (((b : ℂ).re) - 1) * ‖P.f t‖ by
      funext t; simp [gb]]
    exact (mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hmeas).mp hmb
  let C : ℝ := ∫ t : ℝ in Ioi 0, ga t + gb t
  refine ⟨C, ?_, ?_⟩
  · apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact add_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _))
      (mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _))
  · intro s hsa hsb
    have hms := (P.hasMellin s).1
    refine (norm_mellin_le_real_mellin_norm P.f s hms).trans ?_
    change (∫ t : ℝ in Ioi 0, t ^ (s.re - 1) * ‖P.f t‖) ≤ C
    apply integral_mono_ae
    · exact (mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hmeas).mp hms
    · simpa only [Pi.add_apply] using hga.add hgb
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp [ga, gb]
      simpa [add_mul] using mul_le_mul_of_nonneg_right
        (rpow_middle_le_endpoint_sum (a := a) (b := b) (σ := s.re) ht hsa hsb)
        (norm_nonneg (P.f t))

end

end PLInteriorGrowth

#print axioms PLInteriorGrowth.StrongFEPair.exists_norm_Λ_le_on_re_Icc
