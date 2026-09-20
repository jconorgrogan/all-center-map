import FiniteZeroAvoidingRectangle
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Quantitative finite-divisor aperture selection

This strengthens the qualitative finite-coordinate avoidance used by the
Perron rectangle.  A point is selected in a real interval with a literal
inverse-cardinality distance from every member of a finite forbidden set.
-/

namespace QuantitativeFiniteAperture

open Set Metric MeasureTheory DirichletZeros

noncomputable section

/-- A finite set cannot cover an interval by balls whose total diameter is
strictly smaller than the interval length.  The explicit denominator `4`
leaves enough slack to avoid endpoint and `card = 0` case distinctions. -/
theorem exists_mem_Ioo_with_finset_clearance
    (F : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Set.Ioo a b,
      ∀ y ∈ F,
        (b - a) / (4 * (F.card + 1)) ≤ |x - y| := by
  let r : ℝ := (b - a) / (4 * (F.card + 1))
  let U : Set ℝ := ⋃ y ∈ F, Metric.ball y r
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hUmeasure : volume U < volume (Set.Ioo a b) := by
    calc
      volume U ≤ ∑ y ∈ F, volume (Metric.ball y r) :=
        measure_biUnion_finset_le F (fun y => Metric.ball y r)
      _ = ENNReal.ofReal (2 * r) * F.card := by
        simp_rw [Real.volume_ball]
        rw [Finset.sum_const]
        simp [nsmul_eq_mul, mul_comm]
      _ < ENNReal.ofReal (b - a) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        rw [ENNReal.ofReal_lt_ofReal_iff (sub_pos.mpr hab)]
        dsimp [r]
        have hcard : (0 : ℝ) ≤ F.card := by positivity
        have hden : (0 : ℝ) < 4 * (F.card + 1) := by positivity
        rw [show 2 * ((b - a) / (4 * (F.card + 1))) * F.card =
            (2 * (b - a) * F.card) / (4 * (F.card + 1)) by ring]
        apply (div_lt_iff₀ hden).2
        nlinarith [sub_pos.mpr hab]
      _ = volume (Set.Ioo a b) := by rw [Real.volume_Ioo]
  have hnonempty : (Set.Ioo a b \ U).Nonempty := by
    by_contra h
    have hsub : Set.Ioo a b ⊆ U := by
      intro x hx
      by_contra hxU
      exact h ⟨x, hx, hxU⟩
    exact (not_lt_of_ge (measure_mono hsub)) hUmeasure
  obtain ⟨x, hxIoo, hxU⟩ := hnonempty
  refine ⟨x, hxIoo, ?_⟩
  intro y hy
  have hnotball : x ∉ Metric.ball y r := by
    intro hxball
    apply hxU
    simp only [U, Set.mem_iUnion]
    exact ⟨y, ⟨hy, hxball⟩⟩
  rw [Metric.mem_ball, Real.dist_eq] at hnotball
  exact (not_lt.mp hnotball)

/-- Real coordinates of the compact divisor used by the rectangle. -/
def zeroRealCoordinates
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (H : ℝ) : Finset ℝ :=
  (zeroSupport χ 0 (H + 1)).image Complex.re

/-- Both signs of the imaginary coordinates of the compact divisor.  Avoiding
this set by a positive height `T` gives the same clearance on the top and
bottom sides. -/
def signedZeroImagCoordinates
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (H : ℝ) : Finset ℝ :=
  ((zeroSupport χ 0 (H + 1)).image Complex.im) ∪
    ((zeroSupport χ 0 (H + 1)).image fun ρ => -ρ.im)

/-- The literal inverse-cardinality clearance delivered by the two one
dimensional aperture selections. -/
def zeroRectangleClearance
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (H : ℝ) : ℝ :=
  min
    ((1 / 2 : ℝ) /
      (4 * ((zeroRealCoordinates χ H).card + 1)))
    (1 /
      (4 * ((signedZeroImagCoordinates χ H).card + 1)))

theorem zeroRectangleClearance_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (H : ℝ) :
    0 < zeroRectangleClearance χ H := by
  unfold zeroRectangleClearance
  apply lt_min
  · positivity
  · positivity

/-- Quantitative version of the common zero-avoiding rectangle.  The selected
left edge and height have an explicit inverse-cardinality distance from every
point of the compact divisor on all three moved sides. -/
theorem exists_quantitativeZeroAvoidingRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {H c : ℝ} (hH : 0 < H) :
    ∃ σ ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ T ∈ Set.Ioo H (H + 1),
        (∀ u ∈ Set.Icc (-T) T,
          regularizedLFunction χ
            ((σ : ℂ) + (u : ℂ) * Complex.I) ≠ 0) ∧
        (∀ r ∈ Set.Icc σ c,
          regularizedLFunction χ
            ((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0) ∧
        (∀ r ∈ Set.Icc σ c,
          regularizedLFunction χ
            ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) ∧
        (∀ u ∈ Set.Icc (-T) T,
          ∀ ρ ∈ zeroSupport χ 0 (H + 1),
            zeroRectangleClearance χ H ≤
              ‖((σ : ℂ) + (u : ℂ) * Complex.I) - ρ‖) ∧
        (∀ r ∈ Set.Icc σ c,
          ∀ ρ ∈ zeroSupport χ 0 (H + 1),
            zeroRectangleClearance χ H ≤
              ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - ρ‖) ∧
        (∀ r ∈ Set.Icc σ c,
          ∀ ρ ∈ zeroSupport χ 0 (H + 1),
            zeroRectangleClearance χ H ≤
              ‖((r : ℂ) + (T : ℂ) * Complex.I) - ρ‖) := by
  let S := zeroSupport χ 0 (H + 1)
  let R := zeroRealCoordinates χ H
  let A := signedZeroImagCoordinates χ H
  obtain ⟨σ, hσIoo, hσclear⟩ :=
    exists_mem_Ioo_with_finset_clearance R (a := 0) (b := 1 / 2) (by norm_num)
  obtain ⟨T, hTIoo, hTclear⟩ :=
    exists_mem_Ioo_with_finset_clearance A (a := H) (b := H + 1) (by linarith)
  have hdpos : 0 < zeroRectangleClearance χ H :=
    zeroRectangleClearance_pos χ H
  have hdistLeft : ∀ u ∈ Set.Icc (-T) T,
      ∀ ρ ∈ S, zeroRectangleClearance χ H ≤
        ‖((σ : ℂ) + (u : ℂ) * Complex.I) - ρ‖ := by
    intro u hu ρ hρ
    have hρR : ρ.re ∈ R := by
      apply Finset.mem_image.mpr
      exact ⟨ρ, hρ, rfl⟩
    have hcoord := hσclear ρ.re hρR
    dsimp [R] at hcoord
    norm_num at hcoord
    have hdcoord : zeroRectangleClearance χ H ≤ |σ - ρ.re| := by
      exact (min_le_left _ _).trans hcoord
    exact hdcoord.trans (by
      simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero] using
          Complex.abs_re_le_norm
            (((σ : ℂ) + (u : ℂ) * Complex.I) - ρ))
  have hdistBottom : ∀ r ∈ Set.Icc σ c,
      ∀ ρ ∈ S, zeroRectangleClearance χ H ≤
        ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - ρ‖ := by
    intro r hr ρ hρ
    have hρA : -ρ.im ∈ A := by
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨ρ, hρ, rfl⟩
    have hcoord := hTclear (-ρ.im) hρA
    have hcoord' :
        1 / (4 * ((signedZeroImagCoordinates χ H).card + 1)) ≤
          |T - (-ρ.im)| := by
      simpa [A] using hcoord
    have hdcoord : zeroRectangleClearance χ H ≤ |T - (-ρ.im)| := by
      exact (min_le_right _ _).trans hcoord'
    calc
      zeroRectangleClearance χ H ≤ |T - (-ρ.im)| := hdcoord
      _ = |(-T) - ρ.im| := by rw [show (-T) - ρ.im = -(T - (-ρ.im)) by ring, abs_neg]
      _ ≤ ‖((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - ρ‖ := by
        simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, zero_mul, add_zero, zero_add] using
            Complex.abs_im_le_norm
              (((r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) - ρ)
  have hdistTop : ∀ r ∈ Set.Icc σ c,
      ∀ ρ ∈ S, zeroRectangleClearance χ H ≤
        ‖((r : ℂ) + (T : ℂ) * Complex.I) - ρ‖ := by
    intro r hr ρ hρ
    have hρA : ρ.im ∈ A := by
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨ρ, hρ, rfl⟩
    have hcoord := hTclear ρ.im hρA
    have hcoord' :
        1 / (4 * ((signedZeroImagCoordinates χ H).card + 1)) ≤
          |T - ρ.im| := by
      simpa [A] using hcoord
    have hdcoord : zeroRectangleClearance χ H ≤ |T - ρ.im| := by
      exact (min_le_right _ _).trans hcoord'
    exact hdcoord.trans (by
      simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
        mul_one, zero_mul, add_zero, zero_add] using
          Complex.abs_im_le_norm
            (((r : ℂ) + (T : ℂ) * Complex.I) - ρ))
  refine ⟨σ, hσIoo, T, hTIoo, ?_, ?_, ?_, hdistLeft, hdistBottom, hdistTop⟩
  · intro u hu hzero
    let z : ℂ := (σ : ℂ) + (u : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 1) := by
      constructor
      · constructor
        · simpa [z] using hσIoo.1.le
        · have : σ ≤ 1 := by linarith [hσIoo.2]
          simpa [z] using this
      · constructor
        · have : -(H + 1) ≤ u := by linarith [hu.1, hTIoo.2]
          simpa [z] using this
        · have : u ≤ H + 1 := by linarith [hu.2, hTIoo.2]
          simpa [z] using this
    have hzS : z ∈ S :=
      (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        χ 0 (H + 1) hzrect).2 hzero
    have hdz := hdistLeft u hu z hzS
    have : ‖z - z‖ = 0 := by simp
    rw [this] at hdz
    exact (not_lt_of_ge hdz) hdpos
  · intro r hr hzero
    by_cases hrone : 1 ≤ r
    · exact (MAPMellinDetectorLeaf.regularizedLFunction_ne_zero_of_one_le_re
        χ (by simpa using hrone)) hzero
    · let z : ℂ := (r : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
      have hzrect : z ∈ zeroRectangle 0 (H + 1) := by
        constructor
        · constructor
          · have : 0 ≤ r := hσIoo.1.le.trans hr.1
            simpa [z] using this
          · have : r ≤ 1 := (not_le.mp hrone).le
            simpa [z] using this
        · constructor
          · have : -(H + 1) ≤ -T := by linarith [hTIoo.2]
            simpa [z] using this
          · have : -T ≤ H + 1 := by linarith [hH, hTIoo.1]
            simpa [z] using this
      have hzS : z ∈ S :=
        (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
          χ 0 (H + 1) hzrect).2 hzero
      have hdz := hdistBottom r hr z hzS
      have : ‖z - z‖ = 0 := by simp
      rw [this] at hdz
      exact (not_lt_of_ge hdz) hdpos
  · intro r hr hzero
    by_cases hrone : 1 ≤ r
    · exact (MAPMellinDetectorLeaf.regularizedLFunction_ne_zero_of_one_le_re
        χ (by simpa using hrone)) hzero
    · let z : ℂ := (r : ℂ) + (T : ℂ) * Complex.I
      have hzrect : z ∈ zeroRectangle 0 (H + 1) := by
        constructor
        · constructor
          · have : 0 ≤ r := hσIoo.1.le.trans hr.1
            simpa [z] using this
          · have : r ≤ 1 := (not_le.mp hrone).le
            simpa [z] using this
        · constructor
          · have : -(H + 1) ≤ T := by linarith [hH, hTIoo.1]
            simpa [z] using this
          · have : T ≤ H + 1 := hTIoo.2.le
            simpa [z] using this
      have hzS : z ∈ S :=
        (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
          χ 0 (H + 1) hzrect).2 hzero
      have hdz := hdistTop r hr z hzS
      have : ‖z - z‖ = 0 := by simp
      rw [this] at hdz
      exact (not_lt_of_ge hdz) hdpos

end

end QuantitativeFiniteAperture
