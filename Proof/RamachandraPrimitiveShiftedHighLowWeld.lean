import RamachandraPrimitiveShiftedSClosed
import RamachandraPrincipalLowRange

/-!
# High/low weld for the shifted primitive fourth moment

The principal contour identity is only needed in the source's high range.
For `3 ≤ T < 9`, conductor one is bounded directly on the compact strip.
Nonprincipal conductors continue to use the contour construction at every
`T ≥ 3`.  This file makes that split explicit, rather than silently asking the
high principal rectangle for a range where its hypotheses are unavailable.
-/

namespace RamachandraPrimitiveShiftedHighLowWeld

open Complex MeasureTheory
open RamachandraTheorem6ShiftedStripSource
open RamachandraTheorem6SourceProofChain
open RamachandraPrimitiveShiftedContourReduction
open RamachandraPrimitiveShiftedSClosed

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)

/-- A uniform source construction is required only outside the compact
principal exception: either the conductor is nonprincipal, or `T ≥ 9`. -/
def PrimitiveShiftedHighNonprincipalConstruction (C : ℝ) : Type :=
  ∀ (q d : ℕ) [NeZero q] [NeZero d] (T sigma : ℝ),
    d ∣ q → 3 ≤ T →
    |sigma - (1 / 2 : ℝ)| ≤
        (100 * Real.log ((q : ℝ) * T))⁻¹ →
    (d ≠ 1 ∨ 9 ≤ T) →
    { identity : PrimitiveShiftedContourIdentityData d T sigma //
      PrimitiveShiftedContourBudgets d T sigma C identity.remainder }

/-- Every parameter point where the contour construction is requested has
`X=dT≥6`, exactly the lower bound used by the certified short-Gamma mass. -/
theorem primitiveShiftedScale_ge_six_of_highNonprincipalRange
    {d : ℕ} [NeZero d] {T : ℝ} (hT : 3 ≤ T)
    (hrange : d ≠ 1 ∨ 9 ≤ T) :
    6 ≤ primitiveShiftedScale d T := by
  unfold primitiveShiftedScale
  rcases hrange with hd | hT9
  · have hdpos : 0 < d := NeZero.pos d
    have hd2 : 2 ≤ d := by omega
    have hd2R : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    nlinarith [mul_le_mul hd2R hT (by norm_num : (0 : ℝ) ≤ 3)
      (by exact_mod_cast hdpos.le : (0 : ℝ) ≤ d)]
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
    nlinarith [mul_le_mul hd1 hT9 (by norm_num : (0 : ℝ) ≤ 9)
      (by exact_mod_cast (NeZero.pos d).le : (0 : ℝ) ≤ d)]

/-- The compact conductor-one range has an absolute source-shaped budget.
The intentionally large explicit constant avoids any hidden asymptotic
notation and uses only the certified fixed-strip zeta bound. -/
theorem principalCompactFourthIntegral_le_sourceBudget
    {q : ℕ} [NeZero q] {T sigma : ℝ}
    (hT : 3 ≤ T) (hT9 : T < 9)
    (hstrip : |sigma - (1 / 2 : ℝ)| ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹) :
    primitiveFamilyShiftedFourthIntegral 1 T sigma ≤
      (2 * (6400 * 13 ^ 6) ^ 4 : ℝ) * T * Real.log T ^ 200 := by
  obtain ⟨hsigma0, hsigma1⟩ :=
    RamachandraPrincipalLowRange.sigma_mem_zero_threequarters_of_ramachandraStrip
      hT hstrip
  have hraw := RamachandraPrincipalLowRange.principalLowRangeFourthIntegral_le
    hsigma0 hsigma1 (by linarith : 0 ≤ T)
  have hprim : (default : DirichletCharacter ℂ 1).IsPrimitive :=
    DirichletCharacter.isPrimitive_one_level_one
  have hlogone : 1 ≤ Real.log T := by
    have hlogthree : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
    have hmono : Real.log 3 ≤ Real.log T :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hTpos hT
    exact hlogthree.le.trans hmono
  have hbase : 4 + T ≤ 13 := by linarith
  have hpow : (6400 * (4 + T) ^ 6 : ℝ) ^ 4 ≤
      (6400 * 13 ^ 6 : ℝ) ^ 4 := by
    gcongr
  unfold primitiveFamilyShiftedFourthIntegral
  have hdefault : (default : DirichletCharacter ℂ 1) = 1 := Subsingleton.elim _ _
  have hprimOne : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
    simpa only [hdefault] using hprim
  simpa [hprim, hdefault, hprimOne] using!
    (calc
      (∫ t in (-T)..T, shiftedStripLFourth chiOne sigma t) ≤
          2 * T * (6400 * (4 + T) ^ 6) ^ 4 := hraw
      _ ≤ 2 * T * (6400 * 13 ^ 6) ^ 4 := by
        gcongr
      _ ≤ (2 * (6400 * 13 ^ 6) ^ 4 : ℝ) * T *
          Real.log T ^ 200 := by
        have hlogpow : 1 ≤ Real.log T ^ 200 :=
          one_le_pow₀ hlogone
        have hnonneg : 0 ≤ (2 * (6400 * 13 ^ 6) ^ 4 : ℝ) * T := by
          positivity
        calc
          2 * T * (6400 * 13 ^ 6 : ℝ) ^ 4 =
              (2 * (6400 * 13 ^ 6) ^ 4 : ℝ) * T := by ring
          _ ≤ (2 * (6400 * 13 ^ 6) ^ 4 : ℝ) * T *
              Real.log T ^ 200 := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hlogpow hnonneg))

/-- Exact range weld: a contour construction outside the compact principal
exception, plus the direct compact estimate, proves the full primitive source
leaf. -/
theorem ramachandraPrimitiveShiftedFourthK2_of_highNonprincipalConstruction
    {C : ℝ} (hC : 0 < C)
    (hCcompact : (2 * (6400 * 13 ^ 6) ^ 4 : ℝ) ≤ 16 * C)
    (hconstruct : PrimitiveShiftedHighNonprincipalConstruction C) :
    RamachandraPrimitiveShiftedFourthK2 := by
  refine ⟨16 * C, by positivity, ?_⟩
  intro q d _instq _instd T sigma hdq hT hstrip
  by_cases hprincipalLow : d = 1 ∧ T < 9
  · rcases hprincipalLow with ⟨rfl, hT9⟩
    have hlow := principalCompactFourthIntegral_le_sourceBudget
      (q := q) hT hT9 hstrip
    exact hlow.trans (by
      have hlog0 : 0 ≤ Real.log T ^ 200 := by positivity
      have hT0 : 0 ≤ T := by linarith
      have hm := mul_le_mul_of_nonneg_right hCcompact
        (mul_nonneg hT0 hlog0)
      simpa [mul_assoc] using hm)
  · have hrange : d ≠ 1 ∨ 9 ≤ T := by
      by_cases hd : d = 1
      · right
        by_contra hnot
        exact hprincipalLow ⟨hd, lt_of_not_ge hnot⟩
      · exact Or.inl hd
    obtain ⟨identity, budgets⟩ :=
      hconstruct q d T sigma hdq hT hstrip hrange
    have hsigma : sigma < 1 :=
      sigma_lt_one_of_ramachandraStrip hT hstrip
    exact primitiveFamilyShiftedFourthIntegral_le_of_contourLemmas
      (by linarith : 0 ≤ T) hsigma identity budgets

/-- The same honest high/low construction, welded through the already
certified conductor partition, finite Euler factors, and divisor/log
absorption to the literal all-character source theorem. -/
theorem ramachandraTheorem6K2Source_of_highNonprincipalConstruction
    {C : ℝ} (hC : 0 < C)
    (hCcompact : (2 * (6400 * 13 ^ 6) ^ 4 : ℝ) ≤ 16 * C)
    (hconstruct : PrimitiveShiftedHighNonprincipalConstruction C) :
    RamachandraTheorem6K2Source :=
  RamachandraEulerExpEnvelope.ramachandraTheorem6K2Source_of_primitive
    (ramachandraPrimitiveShiftedFourthK2_of_highNonprincipalConstruction
      hC hCcompact hconstruct)

/-- Packaged constant form used by analytic constructors whose explicit
constant is assembled from several fixed full-line masses. -/
structure PrimitiveShiftedHighNonprincipalConstructionPackage where
  C : ℝ
  C_pos : 0 < C
  compact_le : (2 * (6400 * 13 ^ 6) ^ 4 : ℝ) ≤ 16 * C
  data : PrimitiveShiftedHighNonprincipalConstruction C

theorem ramachandraTheorem6K2Source_of_exists_highNonprincipalConstruction
    (hconstruct : PrimitiveShiftedHighNonprincipalConstructionPackage) :
    RamachandraTheorem6K2Source := by
  exact ramachandraTheorem6K2Source_of_highNonprincipalConstruction
    hconstruct.C_pos hconstruct.compact_le hconstruct.data

end
end RamachandraPrimitiveShiftedHighLowWeld

#print axioms RamachandraPrimitiveShiftedHighLowWeld.principalCompactFourthIntegral_le_sourceBudget
#print axioms RamachandraPrimitiveShiftedHighLowWeld.ramachandraPrimitiveShiftedFourthK2_of_highNonprincipalConstruction
#print axioms RamachandraPrimitiveShiftedHighLowWeld.ramachandraTheorem6K2Source_of_highNonprincipalConstruction
#print axioms RamachandraPrimitiveShiftedHighLowWeld.ramachandraTheorem6K2Source_of_exists_highNonprincipalConstruction
