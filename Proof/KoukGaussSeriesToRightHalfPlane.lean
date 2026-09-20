import KoukDigammaAwayFromPoles

/-!
# Gauss digamma series to the right-half-plane logarithmic bound

This module separates the classical analytic identity from its elementary
quantitative consequence.  No growth estimate is assumed here: the sole input
is Gauss' convergent series for the digamma function on `Re z > 0`.
-/

namespace KoukGaussSeriesToRightHalfPlane

open Complex
open scoped BigOperators

noncomputable section

/-- Gauss' classical series identity on its natural half-plane. -/
abbrev GaussDigammaSeries : Prop :=
  ∀ z : ℂ, 0 < z.re →
    HasSum (fun n : ℕ =>
      ((n + 1 : ℕ) : ℂ)⁻¹ - (z + (n : ℂ))⁻¹)
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ))

private def gaussTerm (z : ℂ) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ)⁻¹ - (z + (n : ℂ))⁻¹

private theorem norm_z_add_nat_ge
    (z : ℂ) (hz : 1 ≤ z.re) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ≤ ‖z + (n : ℂ)‖ := by
  calc
    ((n + 1 : ℕ) : ℝ) ≤ (z + (n : ℂ)).re := by
      push_cast
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    _ ≤ ‖z + (n : ℂ)‖ := Complex.re_le_norm _

private theorem norm_gaussTerm_le_two_div
    (z : ℂ) (hz : 1 ≤ z.re) (n : ℕ) :
    ‖gaussTerm z n‖ ≤ 2 / ((n + 1 : ℕ) : ℝ) := by
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hzpos : 0 < ‖z + (n : ℂ)‖ :=
    lt_of_lt_of_le hnpos (norm_z_add_nat_ge z hz n)
  have hinv : ‖(z + (n : ℂ))⁻¹‖ ≤
      1 / ((n + 1 : ℕ) : ℝ) := by
    rw [norm_inv]
    simpa [one_div] using
      (one_div_le_one_div_of_le hnpos (norm_z_add_nat_ge z hz n))
  calc
    ‖gaussTerm z n‖ ≤ ‖(((n + 1 : ℕ) : ℂ))⁻¹‖ +
        ‖(z + (n : ℂ))⁻¹‖ := norm_sub_le _ _
    _ ≤ 1 / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := by
      apply add_le_add
      · rw [norm_inv, Complex.norm_natCast]
        simp [one_div]
      · exact hinv
    _ = 2 / ((n + 1 : ℕ) : ℝ) := by ring

private theorem gaussTerm_eq_mul_inv
    (z : ℂ) (hz : 1 ≤ z.re) (n : ℕ) :
    gaussTerm z n =
      (z - 1) * ((((n + 1 : ℕ) : ℂ) * (z + (n : ℂ)))⁻¹) := by
  have hnne : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hzne : z + (n : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  dsimp [gaussTerm]
  field_simp
  push_cast
  ring

private theorem norm_gaussTerm_le_tail
    (z : ℂ) (hz : 1 ≤ z.re) (n : ℕ) :
    ‖gaussTerm z n‖ ≤
      ‖z - 1‖ / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  rw [gaussTerm_eq_mul_inv z hz n, norm_mul, norm_inv, norm_mul,
    Complex.norm_natCast]
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hden := norm_z_add_nat_ge z hz n
  rw [div_eq_mul_inv]
  gcongr
  rw [pow_two]
  exact (mul_le_mul_of_nonneg_left hden hnpos.le)

private theorem norm_sum_range_gaussTerm_le
    (z : ℂ) (hz : 1 ≤ z.re) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, gaussTerm z n‖ ≤
      2 * (harmonic N : ℝ) := by
  refine (norm_sum_le_of_le (Finset.range N)
    (f := gaussTerm z)
    (n := fun n => 2 / ((n + 1 : ℕ) : ℝ)) ?_).trans ?_
  · intro n hn
    exact norm_gaussTerm_le_two_div z hz n
  · unfold harmonic
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [div_eq_mul_inv]

/-- The quadratic comparison tail, written with the exact index translation
used by the Gauss series. -/
private theorem sum_Ico_inv_succ_sq_le (N M : ℕ) :
    ∑ n ∈ Finset.Ico N M,
        (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
      2 / ((N : ℝ) + 1) := by
  have heq :
      (∑ n ∈ Finset.Ico N M,
          (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) =
        ∑ j ∈ Finset.Ioo N (M + 1), ((j : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_bij (fun n _ => n + 1)
    · intro n hn
      simp only [Finset.mem_Ioo, Finset.mem_Ico] at hn ⊢
      omega
    · intro a ha b hb hab
      omega
    · intro j hj
      simp only [Finset.mem_Ioo] at hj
      refine ⟨j - 1, ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        omega
      · omega
    · intro n hn
      norm_num
  rw [heq]
  exact sum_Ioo_inv_sq_le N (M + 1)

private theorem norm_sum_Ico_gaussTerm_le_two
    (z : ℂ) (hz : 1 ≤ z.re) {N M : ℕ}
    (hscale : ‖z - 1‖ ≤ (N : ℝ) + 1) :
    ‖∑ n ∈ Finset.Ico N M, gaussTerm z n‖ ≤ 2 := by
  calc
    ‖∑ n ∈ Finset.Ico N M, gaussTerm z n‖ ≤
        ∑ n ∈ Finset.Ico N M, ‖gaussTerm z n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico N M,
        ‖z - 1‖ / (((n + 1 : ℕ) : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_gaussTerm_le_tail z hz n
    _ = ‖z - 1‖ *
        (∑ n ∈ Finset.Ico N M,
          (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
    _ ≤ ((N : ℝ) + 1) * (2 / ((N : ℝ) + 1)) := by
      exact mul_le_mul hscale (sum_Ico_inv_succ_sq_le N M)
        (Finset.sum_nonneg (fun n hn => inv_nonneg.mpr (sq_nonneg _)))
        (by positivity)
    _ = 2 := by
      have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      field_simp

private theorem norm_z_sub_one_le_ceil_add_one (z : ℂ) :
    ‖z - 1‖ ≤ (⌈‖z‖⌉₊ : ℝ) + 1 := by
  have hceil : ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
  exact (norm_sub_le z 1).trans (by
    rw [norm_one]
    linarith)

private theorem ceil_norm_le_scale (z : ℂ) :
    (⌈‖z‖⌉₊ : ℝ) ≤ ‖z‖ + 1 := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ ‖z‖ by positivity)
  exact h.le

private theorem partial_gauss_sum_uniform_bound
    (z : ℂ) (hz : 1 ≤ z.re) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, gaussTerm z n‖ ≤
      2 * (1 + Real.log (‖z‖ + 2)) + 2 := by
  let N : ℕ := ⌈‖z‖⌉₊
  have hscale : ‖z - 1‖ ≤ (N : ℝ) + 1 := by
    simpa [N] using norm_z_sub_one_le_ceil_add_one z
  have hNscale : (N : ℝ) ≤ ‖z‖ + 1 := by
    simpa [N] using ceil_norm_le_scale z
  have hlogScale : ∀ {k : ℕ}, 0 < k → k ≤ N →
      Real.log (k : ℝ) ≤ Real.log (‖z‖ + 2) := by
    intro k hk hkN
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hkScale : (k : ℝ) ≤ ‖z‖ + 2 := by
      have : (k : ℝ) ≤ N := by exact_mod_cast hkN
      linarith
    exact Real.strictMonoOn_log.monotoneOn hkpos
      (show (0 : ℝ) < ‖z‖ + 2 by positivity) hkScale
  by_cases hMN : M ≤ N
  · by_cases hM0 : M = 0
    · subst M
      simp
      have : 0 ≤ Real.log (‖z‖ + 2) :=
        Real.log_nonneg (by linarith [norm_nonneg z])
      linarith
    · have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
      have hhead := norm_sum_range_gaussTerm_le z hz M
      have hh := harmonic_le_one_add_log M
      calc
        ‖∑ n ∈ Finset.range M, gaussTerm z n‖ ≤
            2 * (harmonic M : ℝ) := hhead
        _ ≤ 2 * (1 + Real.log (M : ℝ)) := by nlinarith
        _ ≤ 2 * (1 + Real.log (‖z‖ + 2)) := by
          nlinarith [hlogScale hMpos hMN]
        _ ≤ 2 * (1 + Real.log (‖z‖ + 2)) + 2 := by norm_num
  · have hNM : N ≤ M := Nat.le_of_not_ge hMN
    have hsplit := Finset.sum_range_add_sum_Ico (gaussTerm z) hNM
    have hnormSplit :
        ‖∑ n ∈ Finset.range M, gaussTerm z n‖ ≤
          ‖∑ n ∈ Finset.range N, gaussTerm z n‖ +
            ‖∑ n ∈ Finset.Ico N M, gaussTerm z n‖ := by
      rw [← hsplit]
      exact norm_add_le _ _
    have hhead := norm_sum_range_gaussTerm_le z hz N
    have htail := norm_sum_Ico_gaussTerm_le_two z hz
      (N := N) (M := M) hscale
    by_cases hN0 : N = 0
    · have hlognonneg : 0 ≤ Real.log (‖z‖ + 2) :=
        Real.log_nonneg (by linarith [norm_nonneg z])
      calc
        ‖∑ n ∈ Finset.range M, gaussTerm z n‖ ≤
            ‖∑ n ∈ Finset.range N, gaussTerm z n‖ +
              ‖∑ n ∈ Finset.Ico N M, gaussTerm z n‖ := hnormSplit
        _ = ‖∑ n ∈ Finset.Ico N M, gaussTerm z n‖ := by simp [hN0]
        _ ≤ 2 := htail
        _ ≤ 2 * (1 + Real.log (‖z‖ + 2)) + 2 := by linarith
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
      have hh := harmonic_le_one_add_log N
      calc
        ‖∑ n ∈ Finset.range M, gaussTerm z n‖ ≤
            ‖∑ n ∈ Finset.range N, gaussTerm z n‖ +
              ‖∑ n ∈ Finset.Ico N M, gaussTerm z n‖ := hnormSplit
        _ ≤ 2 * (harmonic N : ℝ) + 2 := add_le_add hhead htail
        _ ≤ 2 * (1 + Real.log (N : ℝ)) + 2 := by nlinarith
        _ ≤ 2 * (1 + Real.log (‖z‖ + 2)) + 2 := by
          nlinarith [hlogScale hNpos (le_refl N)]

/-- Gauss' series implies the pole-free right-half-plane estimate by an
explicit head/tail split.  Thus the classical series identity, rather than a
growth estimate in disguise, is the only analytic input to this theorem. -/
theorem rightHalfPlaneDigammaLogBound_of_gaussSeries
    (hGauss : GaussDigammaSeries) :
    KoukDigammaAwayFromPoles.RightHalfPlaneDigammaLogBound := by
  let ell2 : ℝ := Real.log 2
  have hell2pos : 0 < ell2 := Real.log_pos (by norm_num)
  let C : ℝ := 2 + 5 / ell2
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro z hz
  have hzpos : 0 < z.re := lt_of_lt_of_le (by norm_num) hz
  have hsum : HasSum (gaussTerm z)
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ)) := by
    convert hGauss z hzpos using 1 <;>
      simp [gaussTerm, Nat.cast_add, Nat.cast_one]
  have hlimit :
      ‖Complex.digamma z + (Real.eulerMascheroniConstant : ℂ)‖ ≤
        2 * (1 + Real.log (‖z‖ + 2)) + 2 := by
    exact le_of_tendsto'
      (hsum.tendsto_sum_nat.norm)
      (partial_gauss_sum_uniform_bound z hz)
  have hgammaPos : 0 < Real.eulerMascheroniConstant :=
    (by linarith [Real.one_half_lt_eulerMascheroniConstant])
  have hgamma : ‖(Real.eulerMascheroniConstant : ℂ)‖ ≤ 2 / 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hgammaPos]
    exact Real.eulerMascheroniConstant_lt_two_thirds.le
  have hraw : ‖Complex.digamma z‖ ≤
      2 * (1 + Real.log (‖z‖ + 2)) + 2 + 2 / 3 := by
    calc
      ‖Complex.digamma z‖ =
          ‖(Complex.digamma z + (Real.eulerMascheroniConstant : ℂ)) -
            (Real.eulerMascheroniConstant : ℂ)‖ := by ring_nf
      _ ≤ ‖Complex.digamma z + (Real.eulerMascheroniConstant : ℂ)‖ +
          ‖(Real.eulerMascheroniConstant : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 * (1 + Real.log (‖z‖ + 2)) + 2 + 2 / 3 :=
        add_le_add hlimit hgamma
  let L : ℝ := Real.log (‖z‖ + 2)
  have hL2 : ell2 ≤ L := by
    dsimp [ell2, L]
    exact Real.strictMonoOn_log.monotoneOn (by norm_num)
      (show (0 : ℝ) < ‖z‖ + 2 by positivity)
      (by linarith [norm_nonneg z])
  have hOne : (1 : ℝ) ≤ L / ell2 :=
    (le_div_iff₀ hell2pos).2 (by simpa using hL2)
  have hconst : (14 / 3 : ℝ) ≤ (5 / ell2) * L := by
    have : (5 : ℝ) ≤ (5 / ell2) * L := by
      calc
        (5 : ℝ) ≤ 5 * (L / ell2) := by nlinarith
        _ = (5 / ell2) * L := by ring
    linarith
  calc
    ‖Complex.digamma z‖ ≤ 2 * (1 + L) + 2 + 2 / 3 := by simpa [L] using hraw
    _ ≤ 2 * L + (5 / ell2) * L := by nlinarith
    _ = C * L := by
      dsimp [C]
      ring

/-- Full fixed-clearance digamma growth from Gauss' series. -/
theorem awayFromPolesDigammaLogBound_of_gaussSeries
    (hGauss : GaussDigammaSeries) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) :=
  KoukDigammaAwayFromPoles.awayFromPolesDigammaLogBound_of_rightHalfPlane
    (rightHalfPlaneDigammaLogBound_of_gaussSeries hGauss)

end
end KoukGaussSeriesToRightHalfPlane

#print axioms KoukGaussSeriesToRightHalfPlane.rightHalfPlaneDigammaLogBound_of_gaussSeries
#print axioms KoukGaussSeriesToRightHalfPlane.awayFromPolesDigammaLogBound_of_gaussSeries
