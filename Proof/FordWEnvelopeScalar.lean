import Mathlib

noncomputable section
namespace FordWEnvelopeScalar

abbrev mu1 : ℝ := 1905 / 10000
abbrev mu2 : ℝ := 1603 / 10000
abbrev b : ℝ := 1623 / 2500
abbrev eps : ℝ := 1 / 1000

abbrev envelopeIntegral : ℝ := 529631531821 / 3978922975983

/-- The exact rational constant used by the scalar margin contract. -/
theorem envelopeConstant_value :
    envelopeIntegral = (529631531821 : ℝ) / 3978922975983 := by
  norm_num [envelopeIntegral]

/-- Literal page-42 W-envelope, before any finite summation. -/
def envelope (z : ℝ) : ℝ :=
  min (mu2 * z) (max 0 (max (1 - (1 - mu2) * z) ((1 - mu1) * z - 1)))

/-- First affine branch of the literal envelope. -/
theorem envelope_first_branch {z : ℝ} (hz1 : z ≤ 1) :
    envelope z = mu2 * z := by
  unfold envelope
  apply min_eq_left
  have hsecond : mu2 * z ≤ 1 - (1 - mu2) * z := by
    norm_num [mu2]
    linarith
  exact hsecond.trans ((le_max_left _ _).trans (le_max_right _ _))

/-- Second affine branch of the literal envelope. -/
theorem envelope_second_branch {z : ℝ}
    (hz1 : 1 ≤ z) (hza : z ≤ 10000 / 8397) :
    envelope z = 1 - (1 - mu2) * z := by
  unfold envelope
  have hmax : max 0 (max (1 - (1 - mu2) * z) ((1 - mu1) * z - 1)) =
      1 - (1 - mu2) * z := by
    apply le_antisymm
    · apply max_le
      · norm_num [mu2]
        linarith
      · apply max_le
        · norm_num [mu2]
        · norm_num [mu1, mu2]
          linarith
    · exact (le_max_left _ _).trans (le_max_right _ _)
  rw [hmax]
  apply min_eq_right
  norm_num [mu2]
  linarith


/-- Zero branch of the literal envelope. -/
theorem envelope_zero_branch {z : ℝ}
    (hza : 10000 / 8397 ≤ z) (hzw : z ≤ 2000 / 1619) :
    envelope z = 0 := by
  unfold envelope
  have hqr : max (1 - (1 - mu2) * z) ((1 - mu1) * z - 1) ≤ 0 := by
    apply max_le
    · norm_num [mu2]
      linarith
    · norm_num [mu1]
      linarith
  rw [max_eq_left hqr]
  apply min_eq_right
  norm_num [mu2]
  linarith

/-- Final affine branch up to the support endpoint. -/
theorem envelope_final_branch {z : ℝ}
    (hzw : 2000 / 1619 ≤ z) (hzb : z ≤ 2500 / 1623) :
    envelope z = (1 - mu1) * z - 1 := by
  unfold envelope
  have hmax : max 0 (max (1 - (1 - mu2) * z) ((1 - mu1) * z - 1)) =
      (1 - mu1) * z - 1 := by
    apply le_antisymm
    · apply max_le
      · norm_num [mu1]
        linarith
      · apply max_le
        · norm_num [mu2]
          linarith
        · exact le_rfl
    · exact (le_max_right _ _).trans (le_max_right _ _)
  rw [hmax]
  apply min_eq_right
  norm_num [mu1, mu2]
  linarith



lemma affine_lipschitz_one {c d : ℝ} (hc : |c| ≤ 1) :
    LipschitzWith 1 (fun x : ℝ => c * x + d) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  have habs : |c * (x - y)| ≤ |x - y| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hc
  simpa [mul_sub] using habs


theorem envelope_lipschitz_one :
    LipschitzWith 1 envelope := by
  have hmu : LipschitzWith 1 (fun z : ℝ => mu2 * z) := by
    simpa using (affine_lipschitz_one (c := mu2) (d := 0) (by norm_num [mu2]))
  have hq : LipschitzWith 1 (fun z : ℝ => 1 - (1 - mu2) * z) := by
    convert (affine_lipschitz_one (c := -(1 - mu2)) (d := 1) (by norm_num [mu2])) using 1 <;> ring
  have hr : LipschitzWith 1 (fun z : ℝ => (1 - mu1) * z - 1) := by
    simpa using (affine_lipschitz_one (c := 1 - mu1) (d := -1) (by norm_num [mu1]))
  have hzero : LipschitzWith 0 (fun _ : ℝ => (0 : ℝ)) := LipschitzWith.const 0
  have hg : LipschitzWith 1 (fun z : ℝ => max 0 (max (1 - (1 - mu2) * z) ((1 - mu1) * z - 1))) := by
    simpa using hzero.max (hq.max hr)
  simpa [envelope] using hmu.min hg

abbrev quadA : ℝ := 17460190897 / 4720396875000
abbrev quadD : ℝ := -4964602839001 / 9806341284000
abbrev quadE : ℝ := -529631531821 / 15915691903932

/-- The rational margin polynomial is positive for every real k ≥ 2000. -/
theorem quadratic_margin_pos {k : ℝ} (hk : 2000 ≤ k) :
    0 < quadA * k ^ 2 + quadD * k + quadE := by
  have hA : 0 < quadA := by norm_num [quadA]
  have h2000 : 0 < quadA * (2000 : ℝ) ^ 2 + quadD * 2000 + quadE := by
    norm_num [quadA, quadD, quadE]
  have hderiv : 0 < 2 * quadA * 2000 + quadD := by
    norm_num [quadA, quadD]
  nlinarith [sq_nonneg (k - 2000)]

/-- The exact scalar conclusion once the finite Riemann envelope bound is supplied. -/
theorem saving_ge_target_of_riemann
    {K S : ℝ}
    (hK : 2000 ≤ K)
    (hS : S ≥ mu2 * K * (K + 1) / 2 -
      (b * K + 1 / 2) ^ 2 * envelopeIntegral - K / 2 -
      eps * (mu1 + mu2) * K ^ 2) :
    K ^ 2 / 50 ≤ S := by
  have hq := quadratic_margin_pos hK
  norm_num [mu1, mu2, b, eps, envelopeIntegral, quadA, quadD, quadE] at hq ⊢
  nlinarith

end FordWEnvelopeScalar
#print axioms FordWEnvelopeScalar.quadratic_margin_pos
#print axioms FordWEnvelopeScalar.saving_ge_target_of_riemann
