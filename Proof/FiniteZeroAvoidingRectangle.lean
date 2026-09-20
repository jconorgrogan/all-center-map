import APZeroDensityCertificate
import MellinDetectorLeaf
import Mathlib.Order.Interval.Set.Infinite

/-!
# Finite-divisor aperture selection

The compact divisor makes the elementary contour-aperture step completely
deterministic: inside any nonempty real intervals one can choose a left edge
and a height avoiding the finitely many zero coordinates.  This supplies the
same legal rectangle to pointwise Perron and AP family-square arguments.
-/

namespace FiniteZeroAvoidingRectangle

open Set DirichletZeros

noncomputable section

/-- A zero-avoiding rectangle with left edge in `(0, 1/2)` and height in
`(H, H+1)`.  The right edge may be any `c > 1`. -/
theorem exists_zeroAvoidingRectangle
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
            ((r : ℂ) + (T : ℂ) * Complex.I) ≠ 0) := by
  let S := zeroSupport χ 0 (H + 1)
  let R : Finset ℝ := S.image Complex.re
  let A : Finset ℝ := S.image (fun ρ => |ρ.im|)
  have hσinf : (Set.Ioo (0 : ℝ) (1 / 2)).Infinite :=
    Set.Ioo_infinite (by norm_num)
  obtain ⟨σ, hσIoo, hσR⟩ :=
    (hσinf.diff R.finite_toSet).nonempty
  have hTinf : (Set.Ioo H (H + 1)).Infinite :=
    Set.Ioo_infinite (by linarith)
  obtain ⟨T, hTIoo, hTA⟩ :=
    (hTinf.diff A.finite_toSet).nonempty
  refine ⟨σ, hσIoo, T, hTIoo, ?_, ?_, ?_⟩
  · intro u hu hzero
    let z : ℂ := (σ : ℂ) + (u : ℂ) * Complex.I
    have hzrect : z ∈ zeroRectangle 0 (H + 1) := by
      constructor
      · constructor
        · simpa only [z, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
            Complex.ofReal_im, zero_mul, sub_zero, add_zero] using hσIoo.1.le
        · have hσone : σ ≤ 1 := by linarith [hσIoo.2]
          simpa only [z, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
            Complex.ofReal_im, zero_mul, sub_zero, add_zero] using hσone
      · constructor
        · have hTlt : T < H + 1 := hTIoo.2
          have : -(H + 1) ≤ u := by linarith [hu.1]
          simpa [z] using this
        · have hTlt : T < H + 1 := hTIoo.2
          have : u ≤ H + 1 := by linarith [hu.2]
          simpa [z] using this
    have hzS : z ∈ S := by
      exact (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
        χ 0 (H + 1) hzrect).2 hzero
    apply hσR
    change σ ∈ R
    apply Finset.mem_image.mpr
    refine ⟨z, hzS, ?_⟩
    simp [z]
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
          · have hTlt : T < H + 1 := hTIoo.2
            have : -(H + 1) ≤ -T := by linarith
            simpa [z] using this
          · have hTpos : 0 < T := hH.trans hTIoo.1
            have : -T ≤ H + 1 := by linarith
            simpa [z] using this
      have hzS : z ∈ S :=
        (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
          χ 0 (H + 1) hzrect).2 hzero
      apply hTA
      change T ∈ A
      apply Finset.mem_image.mpr
      refine ⟨z, hzS, ?_⟩
      have hTpos : 0 < T := hH.trans hTIoo.1
      simp [z, abs_of_pos hTpos]
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
          · have hTpos : 0 < T := hH.trans hTIoo.1
            have : -(H + 1) ≤ T := by linarith
            simpa [z] using this
          · have : T ≤ H + 1 := hTIoo.2.le
            simpa [z] using this
      have hzS : z ∈ S :=
        (MAPAPZeroDensityCert.mem_zeroSupport_iff_eq_zero
          χ 0 (H + 1) hzrect).2 hzero
      apply hTA
      change T ∈ A
      apply Finset.mem_image.mpr
      refine ⟨z, hzS, ?_⟩
      have hTpos : 0 < T := hH.trans hTIoo.1
      simp [z, abs_of_pos hTpos]

end

end FiniteZeroAvoidingRectangle
