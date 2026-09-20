import GuthMaynardLemma295ThetaDeepCompact
import GuthMaynardLemma295DeepLeftTailPolynomial
import GuthMaynardLemma295FiniteContour

/-!
# The compact part of the deep-left vertical tail

This closes the exceptional range `|t-g| <= 2`, where the recurrence estimate
for the theta multiplier is not used.
-/

namespace GuthMaynardLemma295DeepLeftCompactIntegral

open Complex Set MeasureTheory
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295ThetaAnalytic
open GuthMaynardLemma295ThetaDeepCompact
open GuthMaynardLemma295DualTail
open GuthMaynardLemma295MellinPolynomialDecay

noncomputable section

theorem continuous_lemma295DeepLeftTailIntegrand
    {N : ℝ} (hN : 0 < N) (g : ℝ) (K n : ℕ) :
    Continuous (lemma295DeepLeftTailIntegrand N g K n) := by
  apply continuous_iff_continuousAt.2
  intro t
  let s : ℂ := (deepLeftSigma n : ℝ) + t * I
  let z : ℂ := s - g * I
  have hzre : z.re = deepLeftSigma n := by simp [z, s]
  have hz0 : z ≠ 0 := by
    apply ne_zero_of_re_ne_zero
    rw [hzre]
    unfold deepLeftSigma
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hzlt : z.re < 1 := by
    rw [hzre]
    unfold deepLeftSigma
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hline : ContinuousAt (fun r : ℝ =>
      ((deepLeftSigma n : ℝ) : ℂ) + r * I - g * I) t := by fun_prop
  have htheta : ContinuousAt (fun r : ℝ =>
      sourceZetaTheta (((deepLeftSigma n : ℝ) : ℂ) + r * I - g * I)) t :=
    (differentiableAt_sourceZetaTheta_of_re_lt_one hzlt).continuousAt.comp_of_eq
      hline rfl
  have hdualZ : DifferentiableAt ℂ (sourceDualTailNat K) z := by
    unfold sourceDualTailNat sourceDualPartialNat
    apply DifferentiableAt.sub
    · exact (differentiableAt_riemannZeta (by
        intro h
        apply hz0
        linear_combination -h)).comp z (by fun_prop)
    · have hs : ∀ m ∈ Finset.range K,
          DifferentiableAt ℂ
            (fun w : ℂ => 1 / ((m + 1 : ℕ) : ℂ) ^ (1 - w)) z := by
        intro m hm
        apply DifferentiableAt.div (by fun_prop)
        · exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z).const_cpow
            (.inl (Nat.cast_ne_zero.mpr (by omega)))
        · rw [Complex.cpow_ne_zero_iff]
          exact Or.inl (Nat.cast_ne_zero.mpr (by omega))
      have hsum := DifferentiableAt.sum (u := Finset.range K) hs
      convert hsum using 1 <;> ext w <;> simp
  have hdual : ContinuousAt (fun r : ℝ =>
      sourceDualTailNat K
        (((deepLeftSigma n : ℝ) : ℂ) + r * I - g * I)) t :=
    hdualZ.continuousAt.comp_of_eq hline rfl
  have hscale : ContinuousAt (fun r : ℝ =>
      (N : ℂ) ^ ((((deepLeftSigma n : ℝ) : ℂ) + r * I) - g * I)) t := by
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ w) z :=
      differentiableAt_id.const_cpow (.inl (ofReal_ne_zero.mpr hN.ne'))
    exact hpow.continuousAt.comp_of_eq hline rfl
  have hmellin : ContinuousAt (fun r : ℝ =>
      mellin sourceHZero (((deepLeftSigma n : ℝ) : ℂ) + r * I)) t :=
    (GuthMaynardLemma295FiniteContour.differentiableAt_mellin_sourceHZero s).continuousAt.comp_of_eq
      (by fun_prop) rfl
  unfold lemma295DeepLeftTailIntegrand
  dsimp only
  exact ((htheta.mul hdual).mul hscale).mul hmellin

/-- The compact exceptional range has length four and is controlled by a
constant depending only on the fixed contour depth. -/
theorem exists_norm_integral_deepLeft_compact_le
    (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℝ} (hN : 0 < N) (g : ℝ) (K : ℕ),
      ‖∫ t : ℝ in Set.Icc (g - 2) (g + 2),
          lemma295DeepLeftTailIntegrand N g K n t‖ ≤
        4 * C *
          ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
            (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
          (Real.rpow N (deepLeftSigma n) *
            sourceMellinDecayConstantAt (deepLeftSigma n) 0) := by
  obtain ⟨C, hC, htheta⟩ := exists_deepLeftTheta_compact_bound n
  refine ⟨C, hC, ?_⟩
  intro N hN g K
  let B : ℝ := C *
    ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
      (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
    (Real.rpow N (deepLeftSigma n) *
      sourceMellinDecayConstantAt (deepLeftSigma n) 0)
  have hBint : Integrable (fun _t : ℝ => B)
      (volume.restrict (Set.Icc (g - 2) (g + 2))) :=
    continuous_const.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint : ∀ t ∈ Set.Icc (g - 2) (g + 2),
      ‖lemma295DeepLeftTailIntegrand N g K n t‖ ≤ B := by
    intro t ht
    let s : ℂ := (deepLeftSigma n : ℝ) + t * I
    let z : ℂ := s - g * I
    have hzform : z = (deepLeftSigma n : ℂ) + (t - g) * I := by
      dsimp [z, s]
      ring
    have hzre : z.re = deepLeftSigma n := by simp [z, s]
    have hzneg : z.re < 0 := by
      rw [hzre]
      unfold deepLeftSigma
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hu : t - g ∈ Set.Icc (-2 : ℝ) 2 := by
      constructor <;> linarith [ht.1, ht.2]
    have hth : ‖sourceZetaTheta z‖ ≤ C := by
      rw [hzform]
      simpa [sub_mul] using htheta (t - g) hu
    have htail := norm_sourceDualTailNat_le hzneg K
    rw [hzre] at htail
    have hscale : ‖(N : ℂ) ^ (s - g * I)‖ =
        Real.rpow N (deepLeftSigma n) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
      simp [s]
    have hmellin :=
      norm_mellin_sourceHZero_vertical_le_inv_one_add_abs_pow
        (deepLeftSigma n) 0 t
    simp only [pow_zero, add_comm, one_add_one_eq_two] at hmellin
    have hmellin' : ‖mellin sourceHZero s‖ ≤
        sourceMellinDecayConstantAt (deepLeftSigma n) 0 := by
      dsimp [s]
      exact hmellin.trans (by
        have hc := sourceMellinDecayConstantAt_nonneg (deepLeftSigma n) 0
        linarith)
    have hident : ‖lemma295DeepLeftTailIntegrand N g K n t‖ =
        ‖sourceZetaTheta z‖ * ‖sourceDualTailNat K z‖ *
          Real.rpow N (deepLeftSigma n) * ‖mellin sourceHZero s‖ := by
      unfold lemma295DeepLeftTailIntegrand
      dsimp only
      repeat' rw [norm_mul]
      rw [hscale]
    have htail0 : 0 ≤
        (K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
          (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n) :=
      (norm_nonneg _).trans htail
    have hscale0 : 0 ≤ Real.rpow N (deepLeftSigma n) :=
      Real.rpow_nonneg hN.le _
    rw [hident]
    dsimp [B]
    calc
      ‖sourceZetaTheta z‖ * ‖sourceDualTailNat K z‖ *
          Real.rpow N (deepLeftSigma n) * ‖mellin sourceHZero s‖ ≤
        C * ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
          (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
          Real.rpow N (deepLeftSigma n) * ‖mellin sourceHZero s‖ := by
            gcongr
      _ ≤ C * ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
          (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
          Real.rpow N (deepLeftSigma n) *
          sourceMellinDecayConstantAt (deepLeftSigma n) 0 := by
            gcongr
      _ = C * ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
          (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
          (Real.rpow N (deepLeftSigma n) *
          sourceMellinDecayConstantAt (deepLeftSigma n) 0) := by ring
  calc
    ‖∫ t : ℝ in Set.Icc (g - 2) (g + 2),
        lemma295DeepLeftTailIntegrand N g K n t‖ ≤
      ∫ _t : ℝ in Set.Icc (g - 2) (g + 2), B :=
        norm_integral_le_of_norm_le hBint (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact hpoint t ht)
    _ = 4 * C *
          ((K + 1 : ℝ) ^ (deepLeftSigma n - 1) +
            (K + 1 : ℝ) ^ deepLeftSigma n / (-deepLeftSigma n)) *
          (Real.rpow N (deepLeftSigma n) *
            sourceMellinDecayConstantAt (deepLeftSigma n) 0) := by
      simp [B]
      ring

end
end GuthMaynardLemma295DeepLeftCompactIntegral

#print axioms GuthMaynardLemma295DeepLeftCompactIntegral.exists_norm_integral_deepLeft_compact_le
#print axioms GuthMaynardLemma295DeepLeftCompactIntegral.continuous_lemma295DeepLeftTailIntegrand
