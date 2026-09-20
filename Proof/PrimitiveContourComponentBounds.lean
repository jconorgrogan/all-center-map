import PaperEdgePrimitiveComponents

/-!
# Deterministic bounds for the primitive contour components

These lemmas turn a pointwise bound for the literal logarithmic derivative
into bounds for the left and horizontal sides of the primitive Perron
rectangle.  The analytic logarithmic-derivative estimate remains an explicit
hypothesis, so the same bounds can feed both the pointwise and AP-family
explicit-formula consumers.
-/

namespace PrimitiveContourComponentBounds

open Set
open scoped Interval
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

theorem norm_perronContourIntegrand_vertical_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma u M : ℝ} (hx : 0 < x) (hsigma : 0 < sigma)
    (hlog : ‖logDeriv (DirichletCharacter.LFunction chi)
        ((sigma : ℂ) + Complex.I * u)‖ ≤ M) :
    ‖perronContourIntegrand chi x
        ((sigma : ℂ) + Complex.I * u)‖ ≤
      M * x ^ sigma / sigma := by
  have hden : sigma ≤ ‖(sigma : ℂ) + Complex.I * u‖ := by
    calc
      sigma = |(((sigma : ℂ) + Complex.I * u).re)| := by
        simp [abs_of_pos hsigma]
      _ ≤ ‖(sigma : ℂ) + Complex.I * u‖ := Complex.abs_re_le_norm _
  rw [perronContourIntegrand, norm_div, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
    sub_zero, add_zero]
  calc
    ‖logDeriv (DirichletCharacter.LFunction chi)
          ((sigma : ℂ) + Complex.I * u)‖ * x ^ sigma /
          ‖(sigma : ℂ) + Complex.I * u‖
        ≤ (M * x ^ sigma) / ‖(sigma : ℂ) + Complex.I * u‖ := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hx.le _))
            (norm_nonneg _)
    _ ≤ M * x ^ sigma / sigma := by
      have hM : 0 ≤ M := le_trans (norm_nonneg _) hlog
      exact div_le_div_of_nonneg_left
        (mul_nonneg hM (Real.rpow_nonneg hx.le _)) hsigma hden

theorem norm_leftLineIntegral_le_of_logDeriv
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma T M : ℝ} (hx : 0 < x) (hsigma : 0 < sigma)
    (hT : 0 ≤ T)
    (hlog : ∀ u ∈ Set.Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((sigma : ℂ) + Complex.I * u)‖ ≤ M) :
    ‖leftLineIntegral chi x sigma T‖ ≤
      T / Real.pi * (M * x ^ sigma / sigma) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [leftLineIntegral, norm_mul]
  have hconst : norm ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hpi)]
  rw [hconst]
  have hint :
      ‖∫ u in (-T)..T,
          perronContourIntegrand chi x ((sigma : ℂ) + Complex.I * u)‖ ≤
        (M * x ^ sigma / sigma) * |T - (-T)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => by
      apply norm_perronContourIntegrand_vertical_le chi hx hsigma
      apply hlog u
      have hu' : u ∈ Set.uIcc (-T) T := Set.uIoc_subset_uIcc hu
      simpa [Set.uIcc_of_le (neg_le_self hT)] using hu')
  calc
    (2 * Real.pi)⁻¹ *
        ‖∫ u in (-T)..T,
          perronContourIntegrand chi x ((sigma : ℂ) + Complex.I * u)‖
        ≤ (2 * Real.pi)⁻¹ *
            ((M * x ^ sigma / sigma) * |T - (-T)|) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
    _ = T / Real.pi * (M * x ^ sigma / sigma) := by
      have habs : |T - (-T)| = 2 * T := by
        rw [sub_neg_eq_add, ← two_mul,
          abs_of_nonneg (mul_nonneg (by norm_num) hT)]
      rw [habs]
      field_simp [ne_of_gt hpi]

theorem norm_perronContourIntegrand_horizontal_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x r c tau M : ℝ} (hx : 1 ≤ x) (hrc : r ≤ c)
    (htau : 0 < |tau|)
    (hlog : ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * tau)‖ ≤ M) :
    ‖perronContourIntegrand chi x
        ((r : ℂ) + Complex.I * tau)‖ ≤
      M * x ^ c / |tau| := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hden : |tau| ≤ ‖(r : ℂ) + Complex.I * tau‖ := by
    calc
      |tau| = |(((r : ℂ) + Complex.I * tau).im)| := by simp
      _ ≤ ‖(r : ℂ) + Complex.I * tau‖ := Complex.abs_im_le_norm _
  rw [perronContourIntegrand, norm_div, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
    sub_zero, add_zero]
  have hrpow : x ^ r ≤ x ^ c :=
    Real.rpow_le_rpow_of_exponent_le hx hrc
  calc
    ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + Complex.I * tau)‖ * x ^ r /
          ‖(r : ℂ) + Complex.I * tau‖
        ≤ (M * x ^ c) / ‖(r : ℂ) + Complex.I * tau‖ := by
          apply div_le_div_of_nonneg_right _ (norm_nonneg _)
          calc
            ‖logDeriv (DirichletCharacter.LFunction chi)
                  ((r : ℂ) + Complex.I * tau)‖ * x ^ r
                ≤ M * x ^ r :=
                  mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hx0.le _)
            _ ≤ M * x ^ c := by
              have hM : 0 ≤ M := le_trans (norm_nonneg _) hlog
              exact mul_le_mul_of_nonneg_left hrpow hM
    _ ≤ M * x ^ c / |tau| := by
      have hM : 0 ≤ M := le_trans (norm_nonneg _) hlog
      exact div_le_div_of_nonneg_left
        (mul_nonneg hM (Real.rpow_nonneg hx0.le _)) htau hden

theorem norm_horizontalBoundaryIntegral_le_of_logDeriv
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x sigma c T M : ℝ} (hx : 1 ≤ x) (hsigma : sigma ≤ c)
    (hT : 0 < T)
    (htop : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * T)‖ ≤ M)
    (hbottom : ∀ r ∈ Set.Icc sigma c,
      ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) - Complex.I * T)‖ ≤ M) :
    ‖horizontalBoundaryIntegral chi x sigma c T‖ ≤
      (c - sigma) / Real.pi * (M * x ^ c / T) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hTnonneg : 0 ≤ T := hT.le
  have habsT : |T| = T := abs_of_pos hT
  have habsNegT : |-T| = T := by simp [abs_of_pos hT]
  have htopint :
      ‖∫ r in sigma..c,
          perronContourIntegrand chi x ((r : ℂ) + Complex.I * T)‖ ≤
        (M * x ^ c / T) * |c - sigma| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      have hr' : r ∈ Set.Icc sigma c := by
        have hru : r ∈ Set.uIcc sigma c := Set.uIoc_subset_uIcc hr
        simpa [Set.uIcc_of_le hsigma] using hru
      simpa [habsT] using
        (norm_perronContourIntegrand_horizontal_le chi hx hr'.2
          (by simpa [habsT] using hT) (htop r hr')))
  have hbottomint :
      ‖∫ r in sigma..c,
          perronContourIntegrand chi x ((r : ℂ) - Complex.I * T)‖ ≤
        (M * x ^ c / T) * |c - sigma| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => by
      have hr' : r ∈ Set.Icc sigma c := by
        have hru : r ∈ Set.uIcc sigma c := Set.uIoc_subset_uIcc hr
        simpa [Set.uIcc_of_le hsigma] using hru
      have hpoint := norm_perronContourIntegrand_horizontal_le chi hx hr'.2
        (tau := -T) (M := M) (by simpa [habsNegT] using hT)
        (by simpa [sub_eq_add_neg] using hbottom r hr')
      simpa [sub_eq_add_neg, habsNegT] using hpoint)
  let A : ℂ := ((2 * Real.pi : ℝ) : ℂ)⁻¹ * Complex.I
  let Itop : ℂ := ∫ r in sigma..c,
    perronContourIntegrand chi x ((r : ℂ) + Complex.I * T)
  let Ibottom : ℂ := ∫ r in sigma..c,
    perronContourIntegrand chi x ((r : ℂ) - Complex.I * T)
  have hA : ‖A‖ =
        (2 * Real.pi)⁻¹ := by
    dsimp [A]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hpi), Complex.norm_I, mul_one]
  change ‖A * Itop - A * Ibottom‖ ≤
    (c - sigma) / Real.pi * (M * x ^ c / T)
  calc
    ‖A * Itop - A * Ibottom‖ ≤ ‖A * Itop‖ + ‖A * Ibottom‖ :=
      norm_sub_le _ _
    _ = (2 * Real.pi)⁻¹ * ‖Itop‖ +
        (2 * Real.pi)⁻¹ * ‖Ibottom‖ := by
          rw [norm_mul A Itop, norm_mul A Ibottom, hA]
    _ ≤ (2 * Real.pi)⁻¹ *
          ((M * x ^ c / T) * |c - sigma|) +
        (2 * Real.pi)⁻¹ *
          ((M * x ^ c / T) * |c - sigma|) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (by simpa [Itop] using htopint)
              (by positivity))
            (mul_le_mul_of_nonneg_left (by simpa [Ibottom] using hbottomint)
              (by positivity))
    _ = (c - sigma) / Real.pi * (M * x ^ c / T) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hsigma)]
      field_simp [ne_of_gt hpi]
      ring

end

end PrimitiveContourComponentBounds
