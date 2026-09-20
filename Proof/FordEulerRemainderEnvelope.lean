import FordEulerCellSeriesBound

noncomputable section
namespace FordEulerRemainderEnvelope

open FordEulerCellAnalytic FordEulerCellSeriesBound

private lemma norm_s_le_two_im {s : ℂ} (hsre_lo : (1 / 2 : ℝ) ≤ s.re)
    (hsre_hi : s.re ≤ 2) (ht : 2 ≤ s.im) :
    ‖s‖ ≤ 2 * s.im := by
  have him : 0 ≤ s.im := by linarith
  have hre : 0 ≤ s.re := by linarith
  have hdecomp : s = (s.re : ℂ) + (s.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  calc
    ‖s‖ = ‖(s.re : ℂ) + (s.im : ℂ) * Complex.I‖ := congrArg norm hdecomp
    _ ≤
        ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = s.re + s.im := by
      simp [abs_of_nonneg hre, abs_of_nonneg him]
    _ ≤ 2 * s.im := by linarith

private lemma rpow_neg_half_le {a t : ℝ} (ha : 0 < a) (ht : 2 ≤ t)
    (hat : t ^ 2 / 4 ≤ a) :
    a ^ (-(1 / 2 : ℝ)) ≤ 2 / t := by
  have ht0 : 0 < t := by linarith
  have htsq : (t / 2) ^ 2 ≤ a := by nlinarith
  have hsqrt : t / 2 ≤ a ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by positivity) (by positivity)).2 htsq
  rw [Real.rpow_neg (le_of_lt ha)]
  rw [show 2 / t = (t / 2)⁻¹ by field_simp]
  exact (inv_le_inv₀ (by positivity) (by positivity)).2 hsqrt

theorem remainder_envelope {s : ℂ} {a : ℝ}
    (hsre_lo : (1 / 2 : ℝ) ≤ s.re) (hsre_hi : s.re ≤ 2)
    (ht : 2 ≤ s.im)
    (ha_lo : s.im ^ 2 / 2 ≤ a)
    (ha_hi : a ≤ s.im ^ 2 + 1) :
    ‖∑' n : ℕ, cell (a + n) s‖ ≤ 12 ∧
      ‖(a : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 2 := by
  have him : 0 < s.im := by linarith
  have hsre_pos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have ha_pos : 0 < a := by
    have : 0 < s.im ^ 2 / 2 := by positivity
    linarith
  have ha_one : 1 ≤ a := by
    have hsq : 4 ≤ s.im ^ 2 := by nlinarith
    nlinarith [ha_lo]
  have ha_quarter : s.im ^ 2 / 4 ≤ a := by
    have hsquare : 0 ≤ s.im ^ 2 := sq_nonneg s.im
    linarith
  have hnorms := norm_s_le_two_im hsre_lo hsre_hi ht
  have hpowhalf := rpow_neg_half_le ha_pos ht ha_quarter
  have hpow_sigma : a ^ (-s.re) ≤ a ^ (-(1 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le ha_one
    linarith
  have hpow_sigma1 : a ^ (-s.re - 1) ≤ a ^ (-s.re) := by
    apply Real.rpow_le_rpow_of_exponent_le ha_one
    linarith
  have hsig_inv : 1 / s.re ≤ 2 := by
    apply (div_le_iff₀ hsre_pos).2
    linarith
  have hseries := norm_tsum_cell_le ha_pos hsre_pos hs1
  have hsum_bound : a ^ (-s.re - 1) + a ^ (-s.re) / s.re ≤ 3 * (2 / s.im) := by
    have hterm : a ^ (-s.re) / s.re ≤ 2 * a ^ (-s.re) := by
      have hm : a ^ (-s.re) * (1 / s.re) ≤ a ^ (-s.re) * 2 :=
        mul_le_mul_of_nonneg_left hsig_inv
          (Real.rpow_nonneg (le_of_lt ha_pos) _)
      calc
        a ^ (-s.re) / s.re = a ^ (-s.re) * (1 / s.re) := by ring
        _ ≤ a ^ (-s.re) * 2 := hm
        _ = 2 * a ^ (-s.re) := by ring
    calc
      a ^ (-s.re - 1) + a ^ (-s.re) / s.re ≤
          a ^ (-s.re) + 2 * a ^ (-s.re) := by
            gcongr
      _ = 3 * a ^ (-s.re) := by ring
      _ ≤ 3 * (2 / s.im) := by
        gcongr
        exact hpow_sigma.trans hpowhalf
  constructor
  · calc
      ‖∑' n : ℕ, cell (a + n) s‖ ≤
          ‖s‖ * (a ^ (-s.re - 1) + a ^ (-s.re) / s.re) := hseries
      _ ≤ (2 * s.im) * (3 * (2 / s.im)) := by
        gcongr
      _ = 12 := by
        field_simp [ne_of_gt him]
        norm_num
  · have hnum : ‖(a : ℂ) ^ (1 - s)‖ = a ^ (1 - s.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ha_pos]
      congr 1
    have hexp_le : 1 - s.re ≤ (1 / 2 : ℝ) := by linarith
    have hnum_le : a ^ (1 - s.re) ≤ a ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le ha_one
      exact hexp_le
    have hsqrt : a ^ (1 / 2 : ℝ) ≤ 2 * s.im := by
      rw [← Real.sqrt_eq_rpow]
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith [ha_hi]
    have hden : s.im ≤ ‖s - 1‖ := by
      have hi := Complex.abs_im_le_norm (s - 1)
      simpa [abs_of_pos him] using hi
    rw [norm_div, hnum]
    have hdenpos : 0 < ‖s - 1‖ := lt_of_lt_of_le him hden
    apply (div_le_iff₀ hdenpos).2
    calc
      a ^ (1 - s.re) ≤ a ^ (1 / 2 : ℝ) := hnum_le
      _ ≤ 2 * s.im := hsqrt
      _ ≤ 2 * ‖s - 1‖ := by nlinarith [hden]

end FordEulerRemainderEnvelope

#print axioms FordEulerRemainderEnvelope.remainder_envelope
