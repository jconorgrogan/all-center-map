import RamachandraShiftedRightLineIdentity

/-!
# Generic premise-free Gamma right-line identity

The Ramachandra development already certifies every analytic ingredient of
the starting-line Mellin inversion.  This file packages the same argument for
an arbitrary coefficient sequence whose L-series is absolutely convergent on
the shifted positive line.
-/

namespace MAPJutilaGenericGammaRightLine

open Complex MeasureTheory
open RamachandraShiftedRightLineIdentity

noncomputable section

def genericRightLineTerm (f : ℕ → ℂ) (X : ℝ) (s : ℂ)
    (c v : ℝ) (n : ℕ) : ℂ :=
  Complex.Gamma ((c : ℂ) + v * I) *
    LSeries.term f (s + ((c : ℂ) + v * I)) n *
    (X : ℂ) ^ ((c : ℂ) + v * I)

theorem integrable_genericRightLineTerm
    (f : ℕ → ℂ) {c X : ℝ} (hc : 0 < c) (hX : 0 < X)
    (s : ℂ) (n : ℕ) :
    Integrable (fun v : ℝ => genericRightLineTerm f X s c v n) := by
  by_cases hn0 : n = 0
  · subst n
    simp [genericRightLineTerm, LSeries.term_zero]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let r : ℝ := X / n
  have hr : 0 < r := div_pos hX (by exact_mod_cast hn)
  let a : ℂ := LSeries.term f s n
  let phase : ℝ → ℂ := fun v => a * (r : ℂ) ^ ((c : ℂ) + v * I)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  letI : NeZero (r : ℂ) := ⟨hrC⟩
  have hphase : Continuous phase := by
    dsimp [phase]
    exact continuous_const.mul
      (continuous_const_cpow (r : ℂ) |>.comp (by fun_prop))
  have hphaseBound : ∀ v : ℝ, ‖phase v‖ ≤ ‖a‖ * Real.rpow r c := by
    intro v
    rw [show ‖phase v‖ = ‖a‖ *
        ‖(r : ℂ) ^ ((c : ℂ) + v * I)‖ by simp [phase]]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    simp
  have hGamma := MAPGammaMellinInversion.verticalIntegrable_Gamma hc
  have hprod : Integrable (fun v : ℝ =>
      phase v * Complex.Gamma ((c : ℂ) + v * I)) :=
    hGamma.bdd_mul hphase.aestronglyMeasurable
      (Filter.Eventually.of_forall hphaseBound)
  apply hprod.congr
  filter_upwards [] with v
  unfold genericRightLineTerm
  have hterm := term_mul_ratio_cpow_eq_shiftedTerm_mul_scale
    f s ((c : ℂ) + v * I) hX hn
  dsimp [phase, r, a]
  rw [hterm]
  ring

theorem integral_norm_genericRightLineTerm
    (f : ℕ → ℂ) {c X : ℝ} (hX : 0 < X) (s : ℂ) (n : ℕ) :
    (∫ v : ℝ, ‖genericRightLineTerm f X s c v n‖) =
      (‖LSeries.term f s n‖ * Real.rpow (X / n) c) *
        ∫ v : ℝ, ‖Complex.Gamma ((c : ℂ) + v * I)‖ := by
  by_cases hn0 : n = 0
  · subst n
    simp [genericRightLineTerm, LSeries.term_zero]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  let r : ℝ := X / n
  have hr : 0 < r := div_pos hX (by exact_mod_cast hn)
  let a : ℂ := LSeries.term f s n
  have hpoint (v : ℝ) :
      ‖genericRightLineTerm f X s c v n‖ =
        (‖a‖ * Real.rpow r c) *
          ‖Complex.Gamma ((c : ℂ) + v * I)‖ := by
    unfold genericRightLineTerm
    have hterm := term_mul_ratio_cpow_eq_shiftedTerm_mul_scale
      f s ((c : ℂ) + v * I) hX hn
    have heq : Complex.Gamma ((c : ℂ) + v * I) *
          LSeries.term f (s + ((c : ℂ) + v * I)) n *
          (X : ℂ) ^ ((c : ℂ) + v * I) =
        Complex.Gamma ((c : ℂ) + v * I) *
          (LSeries.term f s n *
            ((X / n : ℝ) : ℂ) ^ ((c : ℂ) + v * I)) := by
      rw [hterm]
      ring
    rw [heq, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hr]
    simp [a, r]
    ring
  calc
    (∫ v : ℝ, ‖genericRightLineTerm f X s c v n‖) =
        ∫ v : ℝ, (‖a‖ * Real.rpow r c) *
          ‖Complex.Gamma ((c : ℂ) + v * I)‖ := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact hpoint v
    _ = (‖a‖ * Real.rpow r c) *
        ∫ v : ℝ, ‖Complex.Gamma ((c : ℂ) + v * I)‖ := by
      rw [MeasureTheory.integral_const_mul]
    _ = _ := by rfl

theorem summable_integral_norm_genericRightLineTerm
    (f : ℕ → ℂ) {c X : ℝ} (hX : 0 < X) (s : ℂ)
    (hLS : LSeriesSummable f (s + (c : ℂ))) :
    Summable (fun n : ℕ =>
      ∫ v : ℝ, ‖genericRightLineTerm f X s c v n‖) := by
  let G : ℝ := ∫ v : ℝ,
    ‖Complex.Gamma ((c : ℂ) + v * I)‖
  have hnorm : Summable (fun n =>
      ‖LSeries.term f (s + (c : ℂ)) n‖) := summable_norm_iff.mpr hLS
  have hscaled : Summable (fun n =>
      Real.rpow X c * ‖LSeries.term f (s + (c : ℂ)) n‖) :=
    hnorm.mul_left (Real.rpow X c)
  have hscaled' : Summable (fun n =>
      ‖LSeries.term f s n‖ * Real.rpow (X / n) c) := by
    apply hscaled.congr
    intro n
    exact (norm_term_mul_ratio_rpow f s hX n).symm
  have hfinal := hscaled'.mul_left G
  apply hfinal.congr
  intro n
  rw [integral_norm_genericRightLineTerm f hX s n]
  dsimp [G]
  ring

theorem smoothed_genericTerm_eq_gamma_right_line
    (f : ℕ → ℂ) {c X : ℝ} (hc : 0 < c) (hX : 0 < X)
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    LSeries.term f s n *
        (Real.exp (-((n : ℝ) / X)) : ℂ) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          LSeries.term f s n *
            (Complex.Gamma ((c : ℂ) + v * I) *
              ((X / n : ℝ) : ℂ) ^ ((c : ℂ) + v * I))) := by
  rw [MAPGammaMellinInversion.exp_neg_nat_div_eq_detector_right_line
    hc hX hn]
  rw [MeasureTheory.integral_const_mul]
  ring

theorem smoothed_genericTerm_eq_shifted_gamma_right_line
    (f : ℕ → ℂ) {c X : ℝ} (hc : 0 < c) (hX : 0 < X)
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    LSeries.term f s n *
        (Real.exp (-((n : ℝ) / X)) : ℂ) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          Complex.Gamma ((c : ℂ) + v * I) *
            LSeries.term f (s + ((c : ℂ) + v * I)) n *
            (X : ℂ) ^ ((c : ℂ) + v * I)) := by
  rw [smoothed_genericTerm_eq_gamma_right_line f hc hX hn s]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  have hterm := term_mul_ratio_cpow_eq_shiftedTerm_mul_scale
    f s ((c : ℂ) + v * I) hX hn
  calc
    LSeries.term f s n *
        (Complex.Gamma ((c : ℂ) + v * I) *
          ((X / n : ℝ) : ℂ) ^ ((c : ℂ) + v * I)) =
      Complex.Gamma ((c : ℂ) + v * I) *
        (LSeries.term f s n *
          ((X / n : ℝ) : ℂ) ^ ((c : ℂ) + v * I)) := by ring
    _ = Complex.Gamma ((c : ℂ) + v * I) *
        (LSeries.term f (s + ((c : ℂ) + v * I)) n *
          (X : ℂ) ^ ((c : ℂ) + v * I)) := by rw [hterm]
    _ = _ := by ring

/-- Full right-line inverse Mellin identity for an arbitrary absolutely
convergent coefficient series. -/
theorem smoothedSeries_eq_LSeries_gamma_rightLine
    (f : ℕ → ℂ) {c X : ℝ} (hc : 0 < c) (hX : 0 < X)
    (s : ℂ) (hLS : LSeriesSummable f (s + (c : ℂ))) :
    (∑' n : ℕ,
      LSeries.term f s n *
        (Real.exp (-((n : ℝ) / X)) : ℂ)) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          LSeries f (s + ((c : ℂ) + v * I)) *
            Complex.Gamma ((c : ℂ) + v * I) *
            (X : ℂ) ^ ((c : ℂ) + v * I)) := by
  let A : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hcoeff (n : ℕ) :
      LSeries.term f s n * (Real.exp (-((n : ℝ) / X)) : ℂ) =
        A * ∫ v : ℝ, genericRightLineTerm f X s c v n := by
    by_cases hn : n = 0
    · subst n
      simp [genericRightLineTerm, A, LSeries.term_zero]
    · simpa [genericRightLineTerm, A] using
        (smoothed_genericTerm_eq_shifted_gamma_right_line
          f hc hX (Nat.pos_of_ne_zero hn) s)
  calc
    (∑' n : ℕ,
        LSeries.term f s n *
          (Real.exp (-((n : ℝ) / X)) : ℂ)) =
        ∑' n : ℕ, A *
          ∫ v : ℝ, genericRightLineTerm f X s c v n := by
      apply tsum_congr
      exact hcoeff
    _ = A * ∑' n : ℕ,
          ∫ v : ℝ, genericRightLineTerm f X s c v n := tsum_mul_left
    _ = A * ∫ v : ℝ,
          ∑' n : ℕ, genericRightLineTerm f X s c v n := by
      rw [MeasureTheory.integral_tsum_of_summable_integral_norm
        (integrable_genericRightLineTerm f hc hX s)
        (summable_integral_norm_genericRightLineTerm f hX s hLS)]
    _ = A * ∫ v : ℝ,
          LSeries f (s + ((c : ℂ) + v * I)) *
            Complex.Gamma ((c : ℂ) + v * I) *
            (X : ℂ) ^ ((c : ℂ) + v * I) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      unfold genericRightLineTerm LSeries
      calc
        (∑' n : ℕ,
            Complex.Gamma ((c : ℂ) + v * I) *
              LSeries.term f (s + ((c : ℂ) + v * I)) n *
              (X : ℂ) ^ ((c : ℂ) + v * I)) =
            ∑' n : ℕ,
              Complex.Gamma ((c : ℂ) + v * I) *
                (LSeries.term f (s + ((c : ℂ) + v * I)) n *
                  (X : ℂ) ^ ((c : ℂ) + v * I)) := by
          apply tsum_congr
          intro n
          ring
        _ =
            Complex.Gamma ((c : ℂ) + v * I) *
              ∑' n : ℕ,
                LSeries.term f (s + ((c : ℂ) + v * I)) n *
                  (X : ℂ) ^ ((c : ℂ) + v * I) := by
          exact tsum_mul_left
        _ = Complex.Gamma ((c : ℂ) + v * I) *
            ((∑' n : ℕ,
                LSeries.term f (s + ((c : ℂ) + v * I)) n) *
              (X : ℂ) ^ ((c : ℂ) + v * I)) := by
          rw [tsum_mul_right]
        _ = (∑' n : ℕ,
              LSeries.term f (s + ((c : ℂ) + v * I)) n) *
            Complex.Gamma ((c : ℂ) + v * I) *
              (X : ℂ) ^ ((c : ℂ) + v * I) := by ring
    _ = _ := by rfl

end

end MAPJutilaGenericGammaRightLine

#print axioms MAPJutilaGenericGammaRightLine.smoothedSeries_eq_LSeries_gamma_rightLine
