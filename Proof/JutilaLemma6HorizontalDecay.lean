import JutilaLemma6FiniteContour
import AppendixA4GammaTails
import JutilaMNonnegativeHalfPlaneBound

namespace MAPJutilaLemma6HorizontalDecay
open Complex Real MeasureTheory Set Filter Topology
open MAPJutilaLemma6FiniteContour MAPJutilaMEntire
open MAPAppendixA4GammaTails
noncomputable section

/-- At height at least one, two recurrences cover the entire detector strip;
no inverse distance from the real Gamma poles is lost. -/
theorem norm_Gamma_detectorStrip_le {x t : ℝ}
    (hxlo : -1 ≤ x) (hxhi : x ≤ 1) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((x : ℂ) + t * I)‖ ≤
      12 * (1 + |t|) * Real.exp (-|t|) := by
  by_cases hlo : -(1 / 2 : ℝ) ≤ x
  · by_cases hhi : x ≤ 1 / 2
    · simpa [GammaCompactStripScratch.stripPoint] using
        GammaCompactStripScratch.norm_Gamma_compactStrip_le_exp hlo hhi ht
    · exact GammaCompactStripScratch.norm_Gamma_positive_strip_le_exp
        (by linarith) (by linarith)
  · let z : ℂ := (x : ℂ) + t * I
    have hn : 1 ≤ ‖z‖ := ht.trans (by simpa [z] using Complex.abs_im_le_norm z)
    have hz : z ≠ 0 := by intro hz; norm_num [hz] at hn
    have hrec := congrArg norm (Complex.Gamma_add_one z hz)
    rw [norm_mul] at hrec
    have hshift : ‖Complex.Gamma (z + 1)‖ ≤
        12 * (1 + |t|) * Real.exp (-|t|) := by
      have hh := GammaCompactStripScratch.norm_Gamma_compactStrip_le_exp
        (a := x + 1) (t := t) (by linarith) (by linarith) ht
      have hp : GammaCompactStripScratch.stripPoint (x + 1) t = z + 1 := by
        simp [z, GammaCompactStripScratch.stripPoint]
        ring
      simpa only [hp, pow_one, neg_one_mul] using hh
    change ‖Complex.Gamma z‖ ≤ _
    exact (le_mul_of_one_le_left (norm_nonneg _) hn).trans (hrec ▸ hshift)

/-- Pointwise horizontal bound, with an explicit bound for the finite entire
factor supplied separately. The polynomial growth here is only fixed-strip
L-growth, so it is adequate for taking the contour limit. -/
theorem norm_detector_horizontal_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (xi : ℕ → ℂ) (D S : Finset ℕ)
    {X C x t : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hM : ∀ s : ℂ, 0 ≤ s.re → ‖jutilaMWeightedSumComplex chi xi D S s‖ ≤ C)
    (hrlo : 0 ≤ rho.re) (hrhi : rho.re ≤ 1)
    (hxlo : -rho.re ≤ x) (hxhi : x ≤ 1) (ht : 1 ≤ |t|) :
    ‖jutilaDetectorExtension chi rho xi D S X ((x : ℂ) + t * I)‖ ≤
      horizontalEnvelope q 0 rho 1 |t| * X * C := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hz : (x : ℂ) + t * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    norm_num [him] at ht
  rw [jutilaDetectorExtension_eq_raw chi xi D S X hrho hz]
  have hg := norm_Gamma_detectorStrip_le (by linarith) hxhi ht
  have hxp : ‖(X : ℂ) ^ ((x : ℂ) + t * I)‖ ≤ X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    simpa using Real.rpow_le_rpow_of_exponent_le hX hxhi
  have hslo : 0 ≤ (rho + ((x : ℂ) + t * I)).re := by simp; linarith
  have hshi : (rho + ((x : ℂ) + t * I)).re ≤ 2 := by simp; linarith
  have hLraw := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi
    (by linarith : -1 ≤ (rho + ((x : ℂ) + t * I)).re) hshi
  have hznorm : ‖rho + ((x : ℂ) + t * I) + 3‖ ≤ 5 + |rho.im| + |t| := by
    calc
      _ ≤ |(rho + ((x : ℂ) + t * I) + 3).re| +
          |(rho + ((x : ℂ) + t * I) + 3).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |rho.re + x + 3| + |rho.im + t| := by simp
      _ ≤ 5 + |rho.im| + |t| := by
        rw [abs_of_nonneg (by linarith : 0 ≤ rho.re + x + 3)]
        linarith [abs_add_le rho.im t]
  have hL := hLraw.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hznorm 2) (by positivity))
  have hm := hM _ hslo
  simp only [norm_mul]
  calc
    _ ≤ (12 * (1 + |t|) * Real.exp (-|t|)) *
        (200 * (q : ℝ) ^ 2 * (5 + |rho.im| + |t|) ^ 2) * X * C := by
      gcongr
    _ = _ := by simp [horizontalEnvelope]

/-- Both horizontal edge integrals vanish, using one common fixed finite
bound for the entire arithmetic factor. -/
theorem tendsto_detector_horizontal_zero_of_bound
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (xi : ℕ → ℂ) (D S : Finset ℕ)
    {X C ε : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hM : ∀ s : ℂ, 0 ≤ s.re → ‖jutilaMWeightedSumComplex chi xi D S s‖ ≤ C)
    (hrlo : 0 ≤ rho.re) (hrhi : rho.re ≤ 1) (hε : |ε| = 1) :
    Tendsto (fun B : ℝ => ∫ x : ℝ in (-rho.re)..1,
      jutilaDetectorExtension chi rho xi D S X ((x : ℂ) + (ε * B) * I))
      atTop (𝓝 0) := by
  have henv := tendsto_horizontalEnvelope_zero q 0 rho (Y := 1) (by norm_num)
  have hlim : Tendsto (fun B : ℝ =>
      horizontalEnvelope q 0 rho 1 B * X * C * |1 - (-rho.re)|)
      atTop (𝓝 0) := by
    simpa using ((henv.mul_const X).mul_const C).mul_const |1 - (-rho.re)|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun B : ℝ =>
    horizontalEnvelope q 0 rho 1 B * X * C * |1 - (-rho.re)|)
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (-rho.re) 1 := by
      have hh := Set.uIoc_subset_uIcc hx
      simpa [Set.uIcc_of_le (show -rho.re ≤ 1 by linarith)] using hh
    have habs : |ε * B| = B := by rw [abs_mul, hε, one_mul, abs_of_nonneg (by linarith)]
    have hh := norm_detector_horizontal_le chi hchi hrho xi D S hX hC hM
      hrlo hrhi hx'.1 hx'.2 (t := ε * B) (by rw [habs]; exact hB)
    simpa only [habs, Complex.ofReal_mul] using hh
  · exact hlim

/-- Unconditional horizontal decay for the actual finite detector. No
horizontal decay estimate or arithmetic-factor bound is assumed. -/
theorem tendsto_detector_horizontal_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (xi : ℕ → ℂ) {D : Finset ℕ} (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ)
    {X ε : ℝ} (hX : 1 ≤ X)
    (hrlo : 0 ≤ rho.re) (hrhi : rho.re ≤ 1) (hε : |ε| = 1) :
    Tendsto (fun B : ℝ => ∫ x : ℝ in (-rho.re)..1,
      jutilaDetectorExtension chi rho xi D S X ((x : ℂ) + (ε * B) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hM⟩ :=
    MAPJutilaMNonnegativeHalfPlaneBound.exists_jutilaMWeightedSumComplex_bound
      chi xi hDpos S
  exact tendsto_detector_horizontal_zero_of_bound chi hchi hrho xi D S
    hX hC hM hrlo hrhi hε

end
end MAPJutilaLemma6HorizontalDecay

#print axioms MAPJutilaLemma6HorizontalDecay.tendsto_detector_horizontal_zero
