import RamachandraShiftedDirectShellAbsorption
import RamachandraEulerExpEnvelope

/-!
# Primitive shifted fourth moment after closing the direct-series leaf

The literal `S` estimate is now theorem, so the source construction need only
supply the contour identity and the long, short, and exact-remainder budgets.
This file performs that final deterministic weld into
`RamachandraPrimitiveShiftedFourthK2`.
-/

namespace RamachandraPrimitiveShiftedSClosed

open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedDirectShellAbsorption
open RamachandraTheorem6SourceProofChain
open RamachandraTheorem6ShiftedStripSource

noncomputable section

/-- The three obligations still outside the now-certified direct-series
estimate.  The remainder is dependently tied to the supplied exact identity. -/
structure PrimitiveShiftedNonDirectBudgets
    (d : ℕ) [NeZero d] (T sigma C : ℝ)
    (identity : PrimitiveShiftedContourIdentityData d T sigma) where
  long : primitiveFamilyLongContourSecondMoment d T sigma ≤
    C * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200
  short : primitiveFamilyShortContourSecondMoment d T sigma ≤
    C * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200
  remainder_budget :
    primitiveFamilyRemainderSecondMoment d T identity.remainder ≤
      C * ((d : ℝ) * T) * Real.log ((d : ℝ) * T) ^ 200

private theorem sourceDelta_nonneg
    (q : ℕ) [NeZero q] {T : ℝ} (hT : 3 ≤ T) :
    0 ≤ (100 * Real.log ((q : ℝ) * T))⁻¹ := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hprod : 1 < (q : ℝ) * T := by nlinarith
  exact inv_nonneg.mpr
    (mul_nonneg (by norm_num) (Real.log_nonneg hprod.le))

private theorem sigma_nonneg_of_sourceStrip
    (q : ℕ) [NeZero q] {T sigma : ℝ} (hT : 3 ≤ T)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    0 ≤ sigma := by
  let R : ℝ := (q : ℝ) * T
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hR : 3 ≤ R := by dsimp [R]; nlinarith
  have hlog : 1 < Real.log R :=
    RamachandraShiftedDirectParameters.one_lt_log_of_three_le hR
  have hdelta : (100 * Real.log R)⁻¹ ≤ 1 / 100 := by
    have hden : (100 : ℝ) ≤ 100 * Real.log R := by nlinarith
    have hpos : 0 < (100 : ℝ) := by norm_num
    have hi := inv_anti₀ hpos hden
    simpa [one_div] using hi
  have hlower : -(100 * Real.log R)⁻¹ ≤ sigma - 1 / 2 :=
    (abs_le.mp hstrip).1
  dsimp [R] at hdelta hlower
  nlinarith

/-- Once the identity and the two reflected-piece budgets are supplied, the
certified direct-series theorem fills the fourth field of the literal contour
budget structure. -/
theorem ramachandraPrimitiveShiftedFourthK2_of_nonDirectConstructions
    (hconstruct : ∀ (q d : ℕ) [NeZero q] [NeZero d]
      (T sigma : ℝ), d ∣ q → 3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      { identity : PrimitiveShiftedContourIdentityData d T sigma //
        PrimitiveShiftedNonDirectBudgets d T sigma 200000000000 identity }) :
    RamachandraPrimitiveShiftedFourthK2 := by
  apply ramachandraPrimitiveShiftedFourthK2_of_contourConstructions
    (C := 200000000000) (by norm_num)
  intro q d _instq _instd T sigma hdq hT hstrip
  obtain ⟨identity, other⟩ := hconstruct q d T sigma hdq hT hstrip
  refine ⟨identity, ?_⟩
  let delta := (100 * Real.log ((q : ℝ) * T))⁻¹
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta]
    exact sourceDelta_nonneg q hT
  have hsigma0 : 0 ≤ sigma := sigma_nonneg_of_sourceStrip q hT hstrip
  have hdirect :=
    primitiveFamilyDirectSecondMoment_le_log200_of_sourceStrip
      q d hdq hT hdelta0 (le_rfl : delta ≤ delta) hstrip hsigma0
  exact
    { direct := by simpa [delta] using hdirect
      long := other.long
      short := other.short
      remainder_budget := other.remainder_budget }

/-- The same reduced construction, wired all the way through conductor
partition and the certified Euler envelope to the literal all-character
Ramachandra Theorem 6 source interface. -/
theorem ramachandraTheorem6K2Source_of_nonDirectConstructions
    (hconstruct : ∀ (q d : ℕ) [NeZero q] [NeZero d]
      (T sigma : ℝ), d ∣ q → 3 ≤ T →
      |sigma - (1 / 2 : ℝ)| ≤
          (100 * Real.log ((q : ℝ) * T))⁻¹ →
      { identity : PrimitiveShiftedContourIdentityData d T sigma //
        PrimitiveShiftedNonDirectBudgets d T sigma 200000000000 identity }) :
    RamachandraTheorem6K2Source :=
  RamachandraEulerExpEnvelope.ramachandraTheorem6K2Source_of_primitive
    (ramachandraPrimitiveShiftedFourthK2_of_nonDirectConstructions hconstruct)


end
end RamachandraPrimitiveShiftedSClosed

#print axioms RamachandraPrimitiveShiftedSClosed.ramachandraPrimitiveShiftedFourthK2_of_nonDirectConstructions
#print axioms RamachandraPrimitiveShiftedSClosed.ramachandraTheorem6K2Source_of_nonDirectConstructions
