import RamachandraTheorem6SourceProofChain
import BHPAllCharacterDyadicBudget

/-!
# Primitive shifted Ramachandra reduction to literal dyadic mean squares

This is the continuous analogue of the mean-value step used in Ramachandra's
Lemmas 4--6.  It is premise-free: primitive characters are masked inside the
complete character family, after which character orthogonality and the finite
logarithmic Hilbert inequality give the exact cost of every literal dyadic
block.  No fourth-moment estimate is assumed.

The remaining input is now only the source-specific contour/Cauchy statement
that majorizes `|L(s,chi)|^4` by these blocks and its elementary coefficient
energy calculation.
-/

namespace RamachandraPrimitiveShiftedFiniteReduction

open scoped BigOperators
open Complex MeasureTheory
open RamachandraTheorem6ShiftedStripSource
open RamachandraTheorem6SourceProofChain
open BHPAllCharacterDyadicBudget

noncomputable section

/-- The primitive mask used to embed the starred source sum in the complete
character family required by orthogonality. -/
def primitiveMaskedShiftedFourth {d : ℕ} [NeZero d]
    (sigma : ℝ) (chi : DirichletCharacter ℂ d) (t : ℝ) : ℝ := by
  classical
  exact if chi.IsPrimitive then shiftedStripLFourth chi sigma t else 0

theorem continuous_shiftedStripLFourth
    {d : ℕ} [NeZero d] (chi : DirichletCharacter ℂ d)
    {sigma : ℝ} (hsigma : sigma ≠ 1) :
    Continuous (shiftedStripLFourth chi sigma) := by
  unfold shiftedStripLFourth
  apply Continuous.pow
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  have harg : ((sigma : ℂ) + t * Complex.I) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact hsigma hre
  have houter := (DirichletCharacter.differentiableAt_LFunction chi _
    (.inl harg)).continuousAt
  have hinner : ContinuousAt (fun u : ℝ =>
      ((sigma : ℂ) + u * Complex.I)) t := by fun_prop
  exact ContinuousAt.comp_of_eq houter hinner rfl

/-- Every point in Ramachandra's stated strip stays away from the principal
pole at `sigma = 1`. -/
theorem sigma_ne_one_of_ramachandraStrip
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    sigma ≠ 1 := by
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hTpos : 0 < T := by linarith
  have hprodTwo : (2 : ℝ) ≤ (q : ℝ) * T := by
    nlinarith [mul_le_mul hqone hT (by norm_num : (0 : ℝ) ≤ 3) hqpos.le]
  have hprodPos : 0 < (q : ℝ) * T := mul_pos hqpos hTpos
  have hlogTwoLe : Real.log 2 ≤ Real.log ((q : ℝ) * T) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hprodPos hprodTwo
  have hlogPos : 0 < Real.log ((q : ℝ) * T) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hlogTwoLe
  have hwindow : (100 * Real.log ((q : ℝ) * T))⁻¹ < (1 / 2 : ℝ) := by
    rw [inv_lt_iff_one_lt_mul₀ (mul_pos (by norm_num) hlogPos)]
    nlinarith [Real.log_two_gt_d9]
  intro hsigma
  subst sigma
  have habs : |(1 : ℝ) - (1 / 2 : ℝ)| = (1 / 2 : ℝ) := by norm_num
  rw [habs] at hstrip
  exact (not_le_of_gt hwindow) hstrip

theorem continuous_primitiveMaskedShiftedFourth
    {d : ℕ} [NeZero d] (chi : DirichletCharacter ℂ d)
    {sigma : ℝ} (hsigma : sigma ≠ 1) :
    Continuous (primitiveMaskedShiftedFourth sigma chi) := by
  classical
  by_cases hp : chi.IsPrimitive
  · change Continuous (fun t =>
      if chi.IsPrimitive then shiftedStripLFourth chi sigma t else 0)
    simp only [hp, if_pos]
    exact continuous_shiftedStripLFourth chi hsigma
  · change Continuous (fun t =>
      if chi.IsPrimitive then shiftedStripLFourth chi sigma t else 0)
    simp only [hp, if_false]
    exact continuous_const

/-- The source's primitive-family integral is exactly the integral of the
primitive mask over the complete character family. -/
theorem primitiveFamilyShiftedFourthIntegral_eq_masked
    (d : ℕ) [NeZero d] (U sigma : ℝ) :
    primitiveFamilyShiftedFourthIntegral d U sigma =
      ∑ chi : DirichletCharacter ℂ d,
        ∫ t in (-U)..U, primitiveMaskedShiftedFourth sigma chi t := by
  classical
  unfold primitiveFamilyShiftedFourthIntegral primitiveMaskedShiftedFourth
  apply Finset.sum_congr rfl
  intro chi hchi
  by_cases hp : chi.IsPrimitive <;> simp [hp]

/-- Exact primitive-family continuous mean-square reduction for a finite
family of literal Ramachandra blocks.  The coefficient arrays are independent
of `chi`, which is the decisive source structure.

This theorem proves the full orthogonality/Hilbert step.  Its pointwise premise
is strictly below a fourth-moment estimate: it is the explicit AFE/Cauchy
majorant produced by Lemmas 3--6. -/
theorem primitiveFamilyShiftedFourthIntegral_le_dyadicCost
    {J d : ℕ} [NeZero d]
    {U sigma A : ℝ}
    (dual : Fin J → Bool) (N : Fin J → ℕ)
    (b : Fin J → ℕ → ℂ)
    (hU : 0 ≤ U) (hA : 0 ≤ A) (hsigma : sigma ≠ 1)
    (hN : ∀ j, 1 ≤ N j)
    (hmajor : ∀ (chi : DirichletCharacter ℂ d), chi.IsPrimitive →
      ∀ t, |t| ≤ U →
        shiftedStripLFourth chi sigma t ≤
          A * ramachandraDyadicFamily dual N b chi t) :
    primitiveFamilyShiftedFourthIntegral d U sigma ≤
      A * ramachandraDyadicFamilyCost d U N b := by
  classical
  let F : DirichletCharacter ℂ d → ℝ → ℝ :=
    fun chi => primitiveMaskedShiftedFourth sigma chi
  have hF : ∀ chi, Continuous (F chi) := by
    intro chi
    exact continuous_primitiveMaskedShiftedFourth chi hsigma
  have hmajorMasked : ∀ chi t, |t| ≤ U →
      F chi t ≤ A * ramachandraDyadicFamily dual N b chi t := by
    intro chi t ht
    by_cases hp : chi.IsPrimitive
    · simpa [F, primitiveMaskedShiftedFourth, hp] using hmajor chi hp t ht
    · have hright : 0 ≤ A * ramachandraDyadicFamily dual N b chi t := by
        unfold ramachandraDyadicFamily
        positivity
      simpa [F, primitiveMaskedShiftedFourth, hp] using hright
  rw [primitiveFamilyShiftedFourthIntegral_eq_masked]
  exact allCharacter_integral_le_ramachandraDyadicFamilyCost
    hU hA dual N b F hF hN hmajorMasked

end
end RamachandraPrimitiveShiftedFiniteReduction

#print axioms RamachandraPrimitiveShiftedFiniteReduction.continuous_shiftedStripLFourth
#print axioms RamachandraPrimitiveShiftedFiniteReduction.primitiveFamilyShiftedFourthIntegral_eq_masked
#print axioms RamachandraPrimitiveShiftedFiniteReduction.primitiveFamilyShiftedFourthIntegral_le_dyadicCost
